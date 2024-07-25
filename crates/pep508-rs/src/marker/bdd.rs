use std::fmt;
use std::sync::Mutex;
use std::{collections::hash_map::Entry, sync::MutexGuard};

use once_cell::sync::Lazy;
use pep440_rs::{Operator, Version, VersionPattern, VersionSpecifier};
use rustc_hash::FxHashMap;

use crate::{
    ExtraOperator, MarkerExpressionKind, MarkerOperator, MarkerValueString, MarkerValueVersion,
};

#[derive(Default)]
pub(crate) struct Interner {
    shared: InternerShared,
    state: Mutex<InternerState>,
}

impl InternerShared {
    /// Returns the node, accounting for the negation.
    fn node(&self, id: NodeId) -> Node {
        let node = self.nodes[id.index()];

        if id.is_complement() {
            node.flip()
        } else {
            node
        }
    }

    fn func(&self, id: FunctionId) -> &Function {
        &self.functions[id.index()]
    }
}

impl Interner {
    fn lock(&self) -> InternerGuard<'_> {
        InternerGuard {
            state: self.state.lock().unwrap(),
            shared: &self.shared,
        }
    }

    pub(crate) fn terminal(&self, expr: MarkerExpressionKind) -> NodeId {
        self.lock().smt(expr)
    }

    pub(crate) fn or(&self, x: NodeId, y: NodeId) -> NodeId {
        self.lock().or(x, y)
    }

    pub(crate) fn and(&self, x: NodeId, y: NodeId) -> NodeId {
        self.lock().and(x, y)
    }

    pub(crate) fn traverse<F>(&self, node: NodeId, f: &mut F)
    where
        F: FnMut(&MarkerExpressionKind),
    {
        if node == NodeId::TRUE || node == NodeId::FALSE {
            return;
        }

        let node = self.shared.node(node);
        let func = self.shared.func(node.func);
        f(&func.expr);
        self.traverse(node.low, f);
        self.traverse(node.high, f);
    }

    pub(crate) fn evaluate<F>(&self, mut node: NodeId, f: &mut F) -> bool
    where
        F: FnMut(&MarkerExpressionKind) -> bool,
    {
        loop {
            if node == NodeId::TRUE {
                return true;
            } else if node == NodeId::FALSE {
                return false;
            }

            let n = self.shared.node(node);
            let func = self.shared.func(n.func);

            if f(&func.expr) {
                node = n.high;
            } else {
                node = n.low;
            }
        }
    }
}

#[derive(Default)]
struct InternerShared {
    nodes: boxcar::Vec<Node>,
    functions: boxcar::Vec<Function>,
}

#[derive(Default)]
struct InternerState {
    node_ids: FxHashMap<Node, NodeId>,
    function_ids: FxHashMap<Variable, FxHashMap<MarkerExpressionKind, FunctionId>>,
    cache: FxHashMap<(NodeId, NodeId), NodeId>,
}

pub(crate) static BDD: Lazy<Interner> = Lazy::new(Interner::default);

#[derive(Debug)]
pub(crate) struct Function {
    expr: MarkerExpressionKind,
}

struct InternerGuard<'a> {
    state: MutexGuard<'a, InternerState>,
    shared: &'a InternerShared,
}

impl InternerGuard<'_> {
    fn create_node(&mut self, func: FunctionId, low: NodeId, high: NodeId) -> NodeId {
        let mut node = Node { func, low, high };

        // Canonical Form: First child is never complemented.
        let mut flipped = false;
        if node.low.is_complement() {
            node = node.flip();
            flipped = true;
        }

        if node.low == node.high {
            if flipped {
                return node.low.not();
            } else {
                return node.low;
            }
        }

        match self.state.node_ids.entry(node.clone()) {
            Entry::Occupied(id) => *id.get(),
            Entry::Vacant(entry) => {
                let id = NodeId::new(self.shared.nodes.push(node), false);
                entry.insert(id);

                if flipped {
                    return id.not();
                } else {
                    return id;
                }
            }
        }
    }

    /// Returns a boolean variable representing a marker expression.
    pub(crate) fn node_for(&mut self, expr: MarkerExpressionKind) -> NodeId {
        let var = match &expr {
            MarkerExpressionKind::Version { key, .. } => key.clone().into(),
            MarkerExpressionKind::String { key, .. } => key.clone().into(),
            MarkerExpressionKind::Extra { .. } => Variable::Extra,
            MarkerExpressionKind::Arbitrary { .. } => panic!(),
        };

        let variables = self.state.function_ids.entry(var).or_default();
        let func = match variables.entry(expr.clone()) {
            Entry::Occupied(id) => *id.get(),
            Entry::Vacant(entry) => {
                let id = FunctionId::new(self.shared.functions.push(Function { expr }));
                entry.insert(id);
                id
            }
        };

        let node = self.create_node(func, NodeId::FALSE, NodeId::TRUE);
        self.unit_propagation(var, node);
        node
    }

    pub(crate) fn or(&mut self, x: NodeId, y: NodeId) -> NodeId {
        self.and(x.not(), y.not()).not()
    }

    pub(crate) fn and(&mut self, xi: NodeId, yi: NodeId) -> NodeId {
        if xi == NodeId::TRUE {
            return yi;
        }

        if yi == NodeId::TRUE {
            return xi;
        }

        if xi == yi {
            return xi;
        }

        if xi == NodeId::FALSE || yi == NodeId::FALSE {
            return NodeId::FALSE;
        }

        // One is complemented but not the other.
        if xi.index() == yi.index() {
            return NodeId::FALSE;
        }

        if let Some(result) = self.state.cache.get(&(xi, yi)) {
            return *result;
        }

        // Perform Shannon Expansion for the higher order variable.
        let (x, y) = (self.shared.node(xi), self.shared.node(yi));
        let (func, low, high) = if x.func < y.func {
            let low = self.and(x.low, yi);
            let high = self.and(x.high, yi);
            (x.func, low, high)
        } else if y.func < x.func {
            let low = self.and(y.low, xi);
            let high = self.and(y.high, xi);
            (y.func, low, high)
        } else {
            let low = self.and(x.low, y.low);
            let high = self.and(x.high, y.high);
            (x.func, low, high)
        };

        let node = self.create_node(func, low, high);
        self.state.cache.insert((xi, yi), node);

        node
    }
}

impl InternerGuard<'_> {
    fn unit_propagation(&mut self, var: Variable, id: NodeId) -> NodeId {
        let node = self.shared.node(id);
        let func = self.shared.func(node.func);

        let Some(variables) = self.state.function_ids.get(&var) else {
            return id;
        };

        for (other, other_id) in variables {
        }

        id
    }

    /// Rewrites an arbitrary marker expression into a normalized SAT expression.
    fn smt(&mut self, expr: MarkerExpressionKind) -> NodeId {
        match expr {
            MarkerExpressionKind::Version {
                ref key,
                ref specifier,
            } => {
                let (operator, version) = specifier.clone().into_parts();

                // Construct variables representing `key == V` and `key > V`.
                //
                // These are the minimal terms that we will use to rewrite all other expressions.
                let equal_to = self.node_for(MarkerExpressionKind::Version {
                    key: key.clone(),
                    specifier: VersionSpecifier::equals_version(version.clone()),
                });

                let greater_than = self
                    .node_for(MarkerExpressionKind::Version {
                        key: key.clone(),
                        specifier: VersionSpecifier::greater_than_version(
                            version.clone().without_local(),
                        ),
                    })
                    .not();

                match operator {
                    // Rewrite `v == V` as `(v == V) and not(v > V.N)`.
                    Operator::ExactEqual | Operator::Equal => {
                        self.and(equal_to, greater_than.not())
                    }

                    // Rewrite `v != V` as `not(v == V) or (v > V.N)`.
                    Operator::NotEqual => self.or(equal_to.not(), greater_than),

                    // Rewrite `v > V.N` as `(v > V.N) and (v != V)`.
                    Operator::GreaterThan => self.and(greater_than, equal_to.not()),

                    // Rewrite `v >= V.N` as `(v > V.N) or (v == V)`.
                    Operator::GreaterThanEqual => self.or(greater_than, equal_to),

                    // Rewrite `v <= V.N` as `not(v > V.N) or (v == V)`.
                    Operator::LessThanEqual => self.or(greater_than.not(), equal_to),

                    // Rewrite `v < V.N` as `not(v > V.N) and not(v == V)`.
                    Operator::LessThan => self.and(greater_than.not(), equal_to.not()),

                    // We do not currently rewrite `v == V.*` in terms of the strict `==` and `>`
                    // operators, so any use of `EqualStar` will introduce a new boolean variable.
                    //
                    // This is rarely used so should not be a problem.
                    Operator::EqualStar => self.node_for(expr),

                    // The most we can do is normalize `NotEqualStar` as `not(v == V.*)`.
                    Operator::NotEqualStar => self
                        .node_for(MarkerExpressionKind::Version {
                            key: key.clone(),
                            specifier: VersionSpecifier::from_version(Operator::EqualStar, version)
                                .unwrap(),
                        })
                        .not(),

                    // Rewrite `v ~= V.N` as `(v > V.N) or (v == V.*)`.
                    Operator::TildeEqual => {
                        let pattern = VersionPattern::wildcard(Version::new(
                            &version.release()[..version.release().len() - 1],
                        ));

                        // This is OK because it only fails if the above would fail
                        // (which we know it doesn't) or if the operator is not compatible
                        // with wildcards, but == is.
                        let equal = self.node_for(MarkerExpressionKind::Version {
                            key: key.clone(),
                            specifier: VersionSpecifier::from_pattern(
                                pep440_rs::Operator::Equal,
                                pattern,
                            )
                            .unwrap(),
                        });

                        self.and(greater_than, equal)
                    }
                }
            }

            MarkerExpressionKind::String {
                ref key,
                operator,
                ref value,
            } => {
                // Construct variables representing `key == value`, `key > value`,
                // `key in value`, and `value in key`.
                //
                // These are the minimal terms that we will use to rewrite all other expressions.
                let equal_to = self.node_for(MarkerExpressionKind::String {
                    key: key.clone(),
                    operator: MarkerOperator::Equal,
                    value: value.clone(),
                });

                let greater_than = self.node_for(MarkerExpressionKind::String {
                    key: key.clone(),
                    operator: MarkerOperator::GreaterThan,
                    value: value.clone(),
                });

                match operator {
                    // Rewrite `key == value` as `(key == value) and not(key > value)`.
                    MarkerOperator::Equal => self.and(equal_to, greater_than.not()),

                    // Rewrite `key != value` as `not(key == value) or (key > value)`.
                    MarkerOperator::NotEqual => self.or(equal_to.not(), greater_than),

                    // Rewrite `key > value` as `(key > value) and (key != value)`.
                    MarkerOperator::GreaterThan => self.and(greater_than, equal_to.not()),

                    // Rewrite `key >= value` as `(key > value) or (key == value)`.
                    MarkerOperator::GreaterEqual => self.or(greater_than, equal_to),

                    // Rewrite `key <= value` as `not(key > value) or (key == value)`.
                    MarkerOperator::LessEqual => self.or(greater_than.not(), equal_to),

                    // Rewrite `key < value` as `not(key > value) and not(key == value)`.
                    MarkerOperator::LessThan => self.and(greater_than.not(), equal_to.not()),

                    // Rewrite `key in value` as `(key in value) or (key == value)`
                    MarkerOperator::In => {
                        let substring = self.node_for(expr);
                        self.or(substring, equal_to)
                    }

                    // Rewrite `key not in value` as `not(key in value) and not(key == value)`
                    MarkerOperator::NotIn => {
                        let substring = self.node_for(expr);
                        self.and(substring.not(), equal_to.not())
                    }

                    // Rewrite `value in key` as `(value in key) or (key == value)`
                    MarkerOperator::Contains => {
                        let contains = self.node_for(expr);
                        self.or(contains, equal_to)
                    }

                    // Rewrite `value not in key` as `not(value in key) and not(key == value)`
                    MarkerOperator::NotContains => {
                        let contains = self.node_for(expr);
                        self.and(contains.not(), equal_to.not())
                    }

                    // `~=` is an invalid comparison operator for strings.
                    //
                    // The marker environment will emit a warning and evaluate to `false`.
                    MarkerOperator::TildeEqual => NodeId::FALSE,
                }
            }

            MarkerExpressionKind::Extra { name, operator } => {
                // Extra expressions are easy to normalize as there is only
                // one possible expression for a given key, and it's negation.
                let expr = MarkerExpressionKind::Extra {
                    name,
                    operator: ExtraOperator::Equal,
                };

                match operator {
                    ExtraOperator::Equal => self.node_for(expr),
                    ExtraOperator::NotEqual => self.node_for(expr).not(),
                }
            }

            // Invalid expressions always evaluate to `false`.
            MarkerExpressionKind::Arbitrary { .. } => NodeId::FALSE,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct NodeId(usize);

impl NodeId {
    pub(crate) const FALSE: NodeId = NodeId(0);
    pub(crate) const TRUE: NodeId = NodeId(1);

    const fn new(index: usize, negated: bool) -> NodeId {
        NodeId(((index + 1) << 1) | (negated as usize))
    }

    pub(crate) fn is_satisfiable(self) -> bool {
        self != NodeId::FALSE
    }

    pub(crate) fn is_true(self) -> bool {
        self == NodeId::TRUE
    }

    pub(crate) fn not(self) -> NodeId {
        NodeId(self.0 ^ 1)
    }

    fn index(self) -> usize {
        (self.0 >> 1) - 1
    }

    fn is_complement(self) -> bool {
        (self.0 & 1) == 1
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct FunctionId(usize);

impl fmt::Debug for FunctionId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == FunctionId::ELSE {
            write!(f, "else")
        } else {
            write!(f, "{:?}", BDD.shared.func(*self))
        }
    }
}

impl FunctionId {
    const ELSE: FunctionId = FunctionId(0);

    fn new(index: usize) -> FunctionId {
        FunctionId(index + 1)
    }

    fn index(self) -> usize {
        self.0 - 1
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub(crate) struct Node {
    func: FunctionId,
    low: NodeId,
    high: NodeId,
}

impl Node {
    fn flip(&self) -> Node {
        Node {
            func: self.func,
            low: self.low.not(),
            high: self.high.not(),
        }
    }
}

impl fmt::Debug for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == NodeId::FALSE {
            return write!(f, "false");
        }

        if *self == NodeId::TRUE {
            return write!(f, "true");
        }

        let node = BDD.shared.node(*self);
        let func = BDD.shared.func(node.func);

        write!(f, "if ({}) {{\n{:?}\n}}\n", func.expr, node.low)?;
        write!(f, "else {{\n{:?}\n}}", node.high)?;

        Ok(())
    }
}

#[repr(u8)]
#[derive(PartialOrd, Ord, PartialEq, Eq, Hash, Clone, Copy, Debug)]
enum Variable {
    // `MarkerValueVersion`
    ImplementationVersion,
    PythonFullVersion,
    PythonVersion,
    // `MarkerValueString`
    ImplementationName,
    OsName,
    OsNameDeprecated,
    PlatformMachine,
    PlatformMachineDeprecated,
    PlatformPythonImplementation,
    PlatformPythonImplementationDeprecated,
    PythonImplementationDeprecated,
    PlatformRelease,
    PlatformSystem,
    PlatformVersion,
    PlatformVersionDeprecated,
    SysPlatform,
    SysPlatformDeprecated,
    // `extra`
    Extra,
}

impl From<MarkerValueVersion> for Variable {
    fn from(value: MarkerValueVersion) -> Self {
        match value {
            MarkerValueVersion::ImplementationVersion => Variable::ImplementationVersion,
            MarkerValueVersion::PythonFullVersion => Variable::PythonFullVersion,
            MarkerValueVersion::PythonVersion => Variable::PythonVersion,
        }
    }
}

impl From<MarkerValueString> for Variable {
    fn from(value: MarkerValueString) -> Self {
        match value {
            MarkerValueString::ImplementationName => Variable::ImplementationName,
            MarkerValueString::OsName => Variable::OsName,
            MarkerValueString::OsNameDeprecated => Variable::OsNameDeprecated,
            MarkerValueString::PlatformMachine => Variable::PlatformMachine,
            MarkerValueString::PlatformMachineDeprecated => Variable::PlatformMachineDeprecated,
            MarkerValueString::PlatformPythonImplementation => {
                Variable::PlatformPythonImplementation
            }
            MarkerValueString::PlatformPythonImplementationDeprecated => {
                Variable::PlatformPythonImplementationDeprecated
            }
            MarkerValueString::PythonImplementationDeprecated => {
                Variable::PythonImplementationDeprecated
            }
            MarkerValueString::PlatformRelease => Variable::PlatformRelease,
            MarkerValueString::PlatformSystem => Variable::PlatformSystem,
            MarkerValueString::PlatformVersion => Variable::PlatformVersion,
            MarkerValueString::PlatformVersionDeprecated => Variable::PlatformVersionDeprecated,
            MarkerValueString::SysPlatform => Variable::SysPlatform,
            MarkerValueString::SysPlatformDeprecated => Variable::SysPlatformDeprecated,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{NodeId, BDD};

    #[test]
    fn basic() {
        let m = &*BDD;

        let a = m.terminal("extra == 'foo'".parse().unwrap());
        assert!(a.is_satisfiable());

        let b = m.terminal("os_name == 'foo'".parse().unwrap());
        let c = m.or(a, b);
        assert!(c.is_satisfiable());
        assert!(m.and(a, b).is_satisfiable());

        let d = m.and(a, a.not());
        assert!(!d.is_satisfiable());

        let e = m.or(d, b);
        assert!(e.is_satisfiable());

        let f = m.or(c, c.not());
        assert!(f.is_satisfiable());
        assert!(f == NodeId::TRUE);

        let a = m.terminal("extra == 'foo'".parse().unwrap());
        assert!(a.is_satisfiable());

        let b = m.terminal("extra != 'foo'".parse().unwrap());
        assert!(m.and(a, b) == NodeId::FALSE);
        assert!(m.or(a, b) == NodeId::TRUE);

        let a = m.terminal("os_name >= 'bar'".parse().unwrap());
        assert!(a.is_satisfiable());

        let b = m.terminal("os_name < 'bar'".parse().unwrap());
        assert!(m.and(a, b) == NodeId::FALSE);
        assert!(m.or(a, b) == NodeId::TRUE);

        let c = m.terminal("os_name <= 'bar'".parse().unwrap());
        assert!(m.and(a, c).is_satisfiable());
        assert!(m.or(a, c) == NodeId::TRUE);
    }

    #[test]
    fn version() {
        let m = &*BDD;

        let a = m.terminal("python_version == '3'".parse().unwrap());
        let b = m.terminal("python_version != '3'".parse().unwrap());
        let c = m.terminal("python_version >= '3'".parse().unwrap());
        let d = m.terminal("python_version <= '3'".parse().unwrap());

        assert!(!m.and(a, b).is_satisfiable());
        assert!(m.or(a, b).is_true());

        assert_eq!(m.and(a, c), a);
        assert_eq!(m.and(a, d), a);

        assert!(m.and(c, d).is_satisfiable());
        assert!(m.or(c, d).is_true());
    }
}

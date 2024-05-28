use anyhow::Result;

use distribution_types::IndexLocations;
use install_wheel_rs::linker::LinkMode;
use uv_cache::Cache;
use uv_client::RegistryClientBuilder;
use uv_configuration::{
    Concurrency, ConfigSettings, NoBinary, NoBuild, PreviewMode, Reinstall, SetupPyStrategy,
};
use uv_dispatch::BuildDispatch;
use uv_installer::SitePackages;
use uv_requirements::ProjectWorkspace;
use uv_resolver::{FlatIndex, InMemoryIndex, Lock};
use uv_types::{BuildIsolation, HashStrategy, InFlight};
use uv_warnings::warn_user;

use crate::commands::pip::operations::Modifications;
use crate::commands::{pip, project, ExitStatus};
use crate::editables::ResolvedEditables;
use crate::printer::Printer;

/// Sync the project environment.
#[allow(clippy::too_many_arguments)]
pub(crate) async fn sync(
    preview: PreviewMode,
    cache: &Cache,
    printer: Printer,
) -> Result<ExitStatus> {
    if preview.is_disabled() {
        warn_user!("`uv sync` is experimental and may change without warning.");
    }

    // Find the project requirements.
    let project = ProjectWorkspace::discover(std::env::current_dir()?).await?;

    // Discover or create the virtual environment.
    let venv = project::init_environment(&project, preview, cache, printer)?;
    let markers = venv.interpreter().markers();
    let tags = venv.interpreter().tags()?;

    // Read the lockfile.
    let resolution = {
        let encoded =
            fs_err::tokio::read_to_string(project.workspace().root().join("uv.lock")).await?;
        let lock: Lock = toml::from_str(&encoded)?;
        lock.to_resolution(markers, tags, project.project_name())
    };

    // Initialize the registry client.
    // TODO(zanieb): Support client options e.g. offline, tls, etc.
    let client = RegistryClientBuilder::new(cache.clone())
        .markers(markers)
        .platform(venv.interpreter().platform())
        .build();

    // TODO(charlie): Respect project configuration.
    let build_isolation = BuildIsolation::default();
    let compile = false;
    let concurrency = Concurrency::default();
    let config_settings = ConfigSettings::default();
    let dry_run = false;
    let flat_index = FlatIndex::default();
    let hasher = HashStrategy::default();
    let in_flight = InFlight::default();
    let index = InMemoryIndex::default();
    let index_locations = IndexLocations::default();
    let link_mode = LinkMode::default();
    let no_binary = NoBinary::default();
    let no_build = NoBuild::default();
    let reinstall = Reinstall::default();
    let setup_py = SetupPyStrategy::default();

    // Create a build dispatch.
    let build_dispatch = BuildDispatch::new(
        &client,
        cache,
        venv.interpreter(),
        &index_locations,
        &flat_index,
        &index,
        &in_flight,
        setup_py,
        &config_settings,
        build_isolation,
        link_mode,
        &no_build,
        &no_binary,
        concurrency,
    );

    let site_packages = SitePackages::from_executable(&venv)?;

    // Build any editables.
    let editables = ResolvedEditables::resolve(
        resolution.editables(),
        &site_packages,
        &reinstall,
        &hasher,
        venv.interpreter(),
        tags,
        cache,
        &client,
        &build_dispatch,
        concurrency,
        printer,
    )
    .await?;

    let site_packages = SitePackages::from_executable(&venv)?;

    // Sync the environment.
    pip::operations::install(
        &resolution,
        &editables,
        site_packages,
        Modifications::Sufficient,
        &reinstall,
        &no_binary,
        link_mode,
        compile,
        &index_locations,
        &hasher,
        tags,
        &client,
        &in_flight,
        concurrency,
        &build_dispatch,
        cache,
        &venv,
        dry_run,
        printer,
    )
    .await?;

    // Notify the user of any resolution diagnostics.
    pip::operations::diagnose_resolution(resolution.diagnostics(), printer)?;

    Ok(ExitStatus::Success)
}

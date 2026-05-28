use tokio::sync::{RwLock, RwLockReadGuard};
use tokio_util::sync::CancellationToken;

use crate::project::{Project, ProjectConfig, ProjectError};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

/// Manages a Project with associated cancellation token for builds
pub struct ProjectManager {
    project: RwLock<Project>,
    cancel: RwLock<CancellationToken>,
    epoch: AtomicU64,
}

/// A read-only view of the project with its associated cancellation token
pub struct ProjectView<'a> {
    pub guard: RwLockReadGuard<'a, Project>,
    pub cancel: CancellationToken,
    pub epoch: u64,
}

impl ProjectManager {
    /// Creates a new ProjectManager with the given project configuration.
    /// Returns an error if the project format version is incompatible.
    pub fn new(
        src_dir: PathBuf,
        build_dir: PathBuf,
        config: ProjectConfig,
        add_src_targets: bool,
    ) -> Result<Self, ProjectError> {
        let mut project = Project::new(src_dir, build_dir, config.clone())?;
        // Target all source modules when the workspace is the library being edited, but
        // defer loading them until the background build. In packaged fallback mode, files
        // opened by the user become targets and imports are loaded on demand.
        if add_src_targets {
            project.add_unloaded_src_targets();
        }
        Ok(ProjectManager {
            project: RwLock::new(project),
            cancel: RwLock::new(CancellationToken::new()),
            epoch: AtomicU64::new(0),
        })
    }

    /// Gets a read-only view of the project
    pub async fn read(&self) -> ProjectView<'_> {
        let guard = self.project.read().await;
        let cancel = self.cancel.read().await.clone();
        let epoch = self.epoch.load(Ordering::SeqCst);
        ProjectView {
            guard,
            cancel,
            epoch,
        }
    }

    /// Mutates the project with exclusive access
    /// Automatically cancels the old token and creates a new one after mutation
    pub async fn mutate<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut Project) -> R,
    {
        self.mutate_with_epoch(f).await.0
    }

    /// Mutates the project and returns the epoch produced by the mutation.
    pub async fn mutate_with_epoch<F, R>(&self, f: F) -> (R, u64)
    where
        F: FnOnce(&mut Project) -> R,
    {
        // First cancel any ongoing builds
        {
            let cancel = self.cancel.read().await;
            cancel.cancel();
        }

        // Get write access to the project
        let mut project = self.project.write().await;

        // Call the mutation function
        let result = f(&mut project);

        // Increment the epoch to invalidate all existing views
        let epoch = self.epoch.fetch_add(1, Ordering::SeqCst) + 1;

        // Create a new cancellation token for future builds
        {
            let mut cancel = self.cancel.write().await;
            *cancel = CancellationToken::new();
        }

        (result, epoch)
    }

    /// Mutates the project only if the epoch matches
    /// Returns Ok(result) if the mutation succeeded, Err(()) if the epoch didn't match
    pub async fn mutate_if_epoch<F, R>(&self, epoch: u64, f: F) -> Result<R, ()>
    where
        F: FnOnce(&mut Project) -> R,
    {
        self.mutate_if_epoch_with_epoch(epoch, f)
            .await
            .map(|(result, _)| result)
    }

    /// Mutates the project only if the epoch matches, returning the new epoch.
    pub async fn mutate_if_epoch_with_epoch<F, R>(&self, epoch: u64, f: F) -> Result<(R, u64), ()>
    where
        F: FnOnce(&mut Project) -> R,
    {
        // Check the epoch before cancelling anything
        if self.epoch.load(Ordering::SeqCst) != epoch {
            return Err(());
        }

        // Cancel any ongoing builds
        {
            let cancel = self.cancel.read().await;
            cancel.cancel();
        }

        // Get write access to the project
        let mut project = self.project.write().await;

        // Double-check the epoch while holding the write lock
        if self.epoch.load(Ordering::SeqCst) != epoch {
            return Err(());
        }

        // Call the mutation function
        let result = f(&mut project);

        // Increment the epoch to invalidate all existing views
        let epoch = self.epoch.fetch_add(1, Ordering::SeqCst) + 1;

        // Create a new cancellation token for future builds
        {
            let mut cancel = self.cancel.write().await;
            *cancel = CancellationToken::new();
        }

        Ok((result, epoch))
    }
}

// Implement Deref for ProjectView to make it easier to use
impl<'a> std::ops::Deref for ProjectView<'a> {
    type Target = Project;

    fn deref(&self) -> &Self::Target {
        &self.guard
    }
}

//! Subprocess budgets (runner follows in a later change).
use std::time::Duration;

/// Bounds applied to every `fossil` child.
#[derive(Debug, Clone, Copy)]
pub struct Limits {
    /// Wall-clock deadline for write + wait.
    pub deadline: Duration,
    /// Maximum stdout bytes retained before the child is killed.
    pub stdout_max: usize,
    /// Maximum stderr bytes retained before the child is killed.
    pub stderr_max: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self { deadline: Duration::from_secs(10), stdout_max: 2 << 20, stderr_max: 64 << 10 }
    }
}

//! Errors produced while elaborating a proof.
use crate::{CheckerError, resolution::ResolutionError};
use std::path::Path;
use thiserror::Error;

use super::ElaborationPass;

/// An elaboration error, with information about the step and rule in which it occurred.
///
/// Note that this still does not contain information about the file and elaboration pass, which is
/// added when this is converted into a [`crate::Error`].
pub(super) struct ElaborationErrorAtStep {
    /// The underlying elaboration error.
    inner: ElaborationError,

    /// The rule that was being elaborated when the error occurred.
    rule: Box<str>,

    /// The ID of the step in which the error occurred.
    step: Box<str>,
}

impl ElaborationErrorAtStep {
    /// Converts the [`ElaborationErrorAtStep`] into an [`Error`] by locating it to a specific file
    /// and elaboration pass.
    pub fn at(self, filename: &Path, pass: ElaborationPass) -> crate::Error {
        crate::Error::Elaborator {
            inner: Box::new(self.inner),
            rule: self.rule,
            step: self.step,
            pass,
            file: filename.into(),
        }
    }
}

/// An error that occurred while elaborating a proof.
#[derive(Debug, Error)]
pub enum ElaborationError {
    /// The elaboration failed because the step is invalid. This wraps an underlying
    /// [`CheckerError`].
    #[error("trying to elaborate invalid step: {0}")]
    Checker(#[from] CheckerError),

    /// An error when using an external tool.
    #[error(transparent)]
    External(#[from] crate::external::ExternalError),

    /// The pivots of a `resolution` step could not be inferred from its conclusion.
    #[error("could not infer pivots for resolution step: {0}")]
    CouldNotInferPivots(ResolutionError),

    /// A `resolution` step could not be uncrowded because its pivots were not provided as
    /// arguments.
    #[error("cannot uncrowd resolution without pivots being provided")]
    UncrowdMissingPivots,
}

impl ElaborationError {
    /// Converts the [`ElaborationError`] into an [`ElaborationErrorAtStep`] by locating it to a
    /// specific step node.
    pub(super) fn at(self, step: &crate::ast::StepNode) -> ElaborationErrorAtStep {
        ElaborationErrorAtStep {
            inner: self,
            rule: step.rule.as_str().into(),
            step: step.id.as_str().into(),
        }
    }
}

impl From<ResolutionError> for ElaborationError {
    fn from(value: ResolutionError) -> Self {
        Self::Checker(value.into())
    }
}

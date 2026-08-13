//! Errors produced while elaborating a proof.
use crate::{resolution::ResolutionError, CheckerError};
use thiserror::Error;

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
    /// Converts the [`ElaborationError`] into an [`Error`] by locating it to a specific step node.
    pub fn at(self, step: &crate::ast::StepNode) -> crate::Error {
        crate::Error::Elaborator {
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

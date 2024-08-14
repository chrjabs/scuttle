//! # Functionality Related to Early Solver Termination
//!
//! The experimental `Try` trait is implemented for types here for ergonomics reasons. This is why
//! Scuttle requires nightly Rust.

use std::fmt;

/// Early termination reasons for [`Solve::solve`]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Termination {
    /// Terminated because of maximum number of Pareto points reached
    PPLimit,
    /// Terminated because of maximum number of solutions reached
    SolsLimit,
    /// Terminated because of maximum number of candidates reached
    CandidatesLimit,
    /// Terminated because of maximum number of oracle calls reached
    OracleCallsLimit,
    /// Termination because of external interrupt
    Interrupted,
}

impl fmt::Display for Termination {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Termination::PPLimit => {
                write!(f, "Solver terminated early because of Pareto point limit")
            }
            Termination::SolsLimit => {
                write!(f, "Solver terminated early because of solution limit")
            }
            Termination::CandidatesLimit => {
                write!(f, "Solver terminated early because of candidate limit")
            }
            Termination::OracleCallsLimit => {
                write!(f, "Solver terminated early because of oracle call limit")
            }
            Termination::Interrupted => {
                write!(f, "Solver terminated early because of interrupt signal")
            }
        }
    }
}

/// Return type for functions that either return a value or were terminated early for some reason
#[derive(Debug, PartialEq)]
pub enum MaybeTerminated<T = ()> {
    /// The operation finished with a return value
    Done(T),
    /// The operation was terminated early
    Terminated(Termination),
}

impl<T> MaybeTerminated<T> {
    pub fn unwrap(self) -> T {
        match self {
            MaybeTerminated::Done(val) => val,
            MaybeTerminated::Terminated(term) => {
                panic!("called `MaybeTerminated::unwrap()` on a `Terminated` value: {term}")
            }
        }
    }
}

impl<T> std::ops::Try for MaybeTerminated<T> {
    type Output = T;

    type Residual = MaybeTerminated<std::convert::Infallible>;

    fn from_output(output: Self::Output) -> Self {
        MaybeTerminated::Done(output)
    }

    fn branch(self) -> std::ops::ControlFlow<Self::Residual, Self::Output> {
        match self {
            MaybeTerminated::Done(val) => std::ops::ControlFlow::Continue(val),
            MaybeTerminated::Terminated(term) => {
                std::ops::ControlFlow::Break(MaybeTerminated::Terminated(term))
            }
        }
    }
}

impl<T> std::ops::FromResidual<MaybeTerminated<std::convert::Infallible>> for MaybeTerminated<T> {
    fn from_residual(residual: <Self as std::ops::Try>::Residual) -> Self {
        let MaybeTerminated::Terminated(term) = residual;
        MaybeTerminated::Terminated(term)
    }
}

/// Return type for functions that either return a value, terminate early or error
#[derive(Debug)]
pub enum MaybeTerminatedError<T = ()> {
    /// The operation finished with a return value
    Done(T),
    /// The operation was terminated early
    Terminated(Termination),
    /// The operation failed
    Error(anyhow::Error),
}

impl<T> MaybeTerminatedError<T> {
    pub fn unwrap(self) -> T {
        match self {
            MaybeTerminatedError::Done(val) => val,
            MaybeTerminatedError::Terminated(term) => {
                panic!("called `MaybeTerminatedError::unwrap()` on a `Terminated` value: {term}")
            }
            MaybeTerminatedError::Error(err) => {
                panic!("called `MaybeTerminatedError::unwrap()` on an `Error` value: {err}")
            }
        }
    }
}

impl<T> From<MaybeTerminated<T>> for MaybeTerminatedError<T> {
    fn from(value: MaybeTerminated<T>) -> Self {
        match value {
            MaybeTerminated::Done(val) => MaybeTerminatedError::Done(val),
            MaybeTerminated::Terminated(term) => MaybeTerminatedError::Terminated(term),
        }
    }
}

impl<T> From<anyhow::Result<T>> for MaybeTerminatedError<T> {
    fn from(value: anyhow::Result<T>) -> Self {
        match value {
            Ok(val) => MaybeTerminatedError::Done(val),
            Err(err) => MaybeTerminatedError::Error(err),
        }
    }
}

impl<T> std::ops::Try for MaybeTerminatedError<T> {
    type Output = T;

    type Residual = MaybeTerminatedError<std::convert::Infallible>;

    fn from_output(output: Self::Output) -> Self {
        MaybeTerminatedError::Done(output)
    }

    fn branch(self) -> std::ops::ControlFlow<Self::Residual, Self::Output> {
        match self {
            MaybeTerminatedError::Done(val) => std::ops::ControlFlow::Continue(val),
            MaybeTerminatedError::Terminated(term) => {
                std::ops::ControlFlow::Break(MaybeTerminatedError::Terminated(term))
            }
            MaybeTerminatedError::Error(err) => {
                std::ops::ControlFlow::Break(MaybeTerminatedError::Error(err))
            }
        }
    }
}

impl<T> std::ops::FromResidual<MaybeTerminatedError<std::convert::Infallible>>
    for MaybeTerminatedError<T>
{
    fn from_residual(residual: <Self as std::ops::Try>::Residual) -> Self {
        match residual {
            MaybeTerminatedError::Terminated(term) => MaybeTerminatedError::Terminated(term),
            MaybeTerminatedError::Error(err) => MaybeTerminatedError::Error(err),
        }
    }
}

impl<T> std::ops::FromResidual<MaybeTerminated<std::convert::Infallible>>
    for MaybeTerminatedError<T>
{
    fn from_residual(residual: MaybeTerminated<std::convert::Infallible>) -> Self {
        let MaybeTerminated::Terminated(term) = residual;
        MaybeTerminatedError::Terminated(term)
    }
}

impl<T, E> std::ops::FromResidual<Result<std::convert::Infallible, E>> for MaybeTerminatedError<T>
where
    E: Into<anyhow::Error>,
{
    fn from_residual(residual: Result<std::convert::Infallible, E>) -> Self {
        let Err(err) = residual;
        MaybeTerminatedError::Error(err.into())
    }
}

/// Equivalent of [`anyhow::ensure`] for [`MaybeTerminatedError`]
macro_rules! ensure {
    ($cond:expr, $msg:literal) => {
        if !$cond {
            return crate::MaybeTerminatedError::Error(anyhow::anyhow!($msg));
        }
    };
    ($cond:expr, $err:expr) => {
        if !$cond {
            return crate::MaybeTerminatedError::Error(anyhow::anyhow!($err));
        }
    };
    ($cond:expr, $fmt:expr, $($arg:tt)*) => {
        if !$cond {
            return crate::MaybeTerminatedError::Error(anyhow::anyhow!($fmt, $($arg)*));
        }
    };
}
pub(crate) use ensure;

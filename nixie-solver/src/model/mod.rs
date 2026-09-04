//! Model Building for SMT Solvers.

#[allow(unused_imports)]
use crate::prelude::*;

pub mod builder;
pub mod completion;
pub mod minimizer;

pub use builder::{Model, ModelBuilder, ModelBuilderConfig, ModelBuilderStats, Value, VarId};
pub use completion::{CompletionConfig, CompletionStats, CompletionStrategy, ModelCompleter};
pub use minimizer::{
    Assignment, MinimizationStrategy, MinimizerConfig, MinimizerStats, ModelMinimizer,
};

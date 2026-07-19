//! Model Building for SMT Solvers.

#[allow(unused_imports)]
use crate::prelude::*;

// `advanced_builder` is an under-development scaffold whose theory model
// builders are still placeholders (hardcoded bounds, no-op BV/array/datatype/UF
// construction, `determine_theory` always `Core`, `is_assignment_necessary`
// always true).  It is NOT wired into the real solve path.  Until it produces
// models that actually reflect the constraints, it is kept `#[doc(hidden)]` so
// it is not advertised as usable public API — building a model with it would
// silently ignore the input.  See its module docs.
#[doc(hidden)]
pub mod advanced_builder;
pub mod builder;
pub mod completion;
pub mod minimizer;

/// Re-exported for source compatibility only; the underlying builder is a
/// non-functional placeholder (see [`advanced_builder`]).  Hidden from the
/// public documentation so it is not presented as a supported model builder.
#[doc(hidden)]
pub use advanced_builder::{
    AdvancedModelBuilder, ArrayValue, Model as AdvancedModel,
    ModelBuilderConfig as AdvancedModelBuilderConfig,
    ModelBuilderStats as AdvancedModelBuilderStats, ModelValue, Theory, Value as ModelValue2,
};
pub use builder::{Model, ModelBuilder, ModelBuilderConfig, ModelBuilderStats, Value, VarId};
pub use completion::{CompletionConfig, CompletionStats, CompletionStrategy, ModelCompleter};
pub use minimizer::{
    Assignment, MinimizationStrategy, MinimizerConfig, MinimizerStats, ModelMinimizer,
};

//! Regression test for the removed fake "GPU acceleration" feature stubs.
//!
//! `oxiz-sat` used to publish `cuda`/`opencl`/`vulkan` Cargo features whose
//! constructors (`CudaAccelerator::new`, `OpenCLAccelerator::new`,
//! `VulkanAccelerator::new`) always returned `GpuError::BackendNotSupported`
//! and whose `check_*_available()` helpers always returned `false`: enabling
//! the features compiled code, but no backend could ever activate. That is
//! FFI-shaped surface area advertising GPU acceleration this crate never
//! actually implements, conflicting with the COOLJAPAN Pure Rust policy, so
//! the feature flags (and the dead `gpu` module scaffolding around them)
//! were removed outright rather than kept as inert placeholders. This test
//! guards against silently reintroducing them.

const MANIFEST: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml"));

#[test]
fn cargo_toml_does_not_publish_fake_gpu_backend_features() {
    for banned in ["cuda", "opencl", "vulkan"] {
        let declares_feature = MANIFEST
            .lines()
            .map(str::trim_start)
            .any(|line| line.starts_with(&format!("{banned} =")));
        assert!(
            !declares_feature,
            "oxiz-sat/Cargo.toml must not declare a `{banned}` Cargo feature: \
             this crate ships no real CUDA/OpenCL/Vulkan backend, so publishing \
             that feature would advertise GPU acceleration that does not exist"
        );
    }
}

#[test]
fn no_gpu_backend_types_are_publicly_exported() {
    // The crate's public prelude previously re-exported GPU-flavored types
    // (`GpuBackend`, `CpuReferenceAccelerator`, `GpuSolverAccelerator`, ...)
    // from a `gpu` module that was never wired into the CDCL solve loop and
    // had no callers anywhere else in the workspace. Grepping the published
    // API surface (this crate's own source, since it is the sole owner of
    // that module) confirms the module and its exports are gone rather than
    // just hidden behind a feature flag.
    let lib_rs = include_str!("../src/lib.rs");
    assert!(
        !lib_rs.contains("mod gpu"),
        "oxiz-sat/src/lib.rs must not reference a `gpu` module"
    );
    assert!(
        !lib_rs.to_lowercase().contains("gpubackend"),
        "oxiz-sat/src/lib.rs must not re-export GPU accelerator types"
    );
}

# nixie-smtcomp TODO

## Future Enhancements

### Performance
- [ ] GPU acceleration for parallel solving – **(decision: won't-implement – out-of-scope for the Pure-Rust policy; the inert `cuda`/`opencl`/`vulkan` stub feature flags in `nixie-sat` were confirmed fully dead (zero references anywhere in the workspace) and deleted entirely in the 0.3.0 hardening pass, rather than kept as always-`BackendNotSupported` stubs. Not planned going forward)**
- [ ] Distributed execution across multiple machines – **(status: future – this release upgraded `nixie-spacer`'s distributed PDR from a single-process sequential fallback to a genuine multi-thread parallel portfolio on one machine, but true multi-machine coordination (a wire protocol, e.g. over `websocket.rs`) has not been started.)**

### Integration
- [ ] SMT-LIB 3.0 support when available – **(status: externally blocked – the SMT-LIB 3.0 standard itself is unreleased; nothing to implement against yet.)**

## Module Summary

| Module | Description | Status |
|--------|-------------|--------|
| benchmark.rs | Core runner with timeout | Complete |
| loader.rs | Benchmark discovery | Complete |
| reporter.rs | Result reporting (JSON/CSV/Text) | Complete |
| statistics.rs | Statistical analysis | Complete |
| parallel.rs | Parallel execution (rayon) | Complete |
| memory.rs | Memory limit enforcement | Complete |
| model_verify.rs | Model verification | Complete |
| starexec.rs | StarExec compatibility | Complete |
| plotting.rs | SVG plot generation | Complete |
| html_report.rs | HTML reports | Complete |
| resumption.rs | Incremental saving | Complete |
| filtering.rs | Benchmark filtering | Complete |
| virtual_best.rs | VBS calculation | Complete |
| ci_integration.rs | CI/CD support | Complete |
| sampling.rs | Representative sampling | Complete |
| regression.rs | Regression detection | Complete |
| dashboard.rs | Web dashboard | Complete |

## Current Status (v0.3.1)

| Metric | Value |
|--------|-------|
| Version | 0.3.1 |
| Status | Production Ready (part of the Nixie workspace) |
| Tests | 264 passing (0 failures) |
| Rust LoC | 13,695 code lines (37 files, tokei) |
| `todo!`/`unimplemented!` | 0 |

*Last updated: 2026-07-31*

## Dependencies
- `rayon` for parallel execution
- `serde` for serialization
- `thiserror` for error handling
- `tracing` for logging

# nixie-wasm TODO

Last Updated: 2026-07-31 (v0.3.1)

## Progress: ~99% Complete

---

## BEYOND Z3: WASM-First Architecture

**Nixie is designed for the browser from day one!**

| Metric | Z3 WASM | Nixie WASM |
|--------|---------|-----------|
| Bundle Size | ~20MB | **Target <2MB** |
| Load Time | Slow | **Fast** |
| Memory | Heavy | Optimized |
| Async Support | Limited | **Full** |

**Benefits**:
- Client-side verification (no server roundtrip)
- Edge computing (CDN-deployed verification)
- Offline-capable web applications
- Embedded in web IDEs and playgrounds

**Framework Wrappers**: React, Vue, Svelte, Deno ready!

---

## Dependencies
- **nixie-core**: SMT-LIB2 parser
- **nixie-solver**: Main solver API

## Provides (enables other crates)
- JavaScript/TypeScript SMT solver API
- Browser-native verification
- WebWorker support for non-blocking solving

---

## Packaging

- [ ] Publish to npm (ready - use ./publish.sh when ready) – **(status: blocked – awaiting explicit authorization from the user (KitaSan) per the workspace publish policy; code, packaging (`package.json`, CDN docs, framework wrappers), and the `publish.sh`/`version-bump.sh` automation are all ready.)**

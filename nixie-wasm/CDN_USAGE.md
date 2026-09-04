# Nixie WASM CDN Usage Guide

This guide shows you how to use Nixie WASM directly from CDNs without installing npm packages.

## Quick Start

### Using unpkg

```html
<!DOCTYPE html>
<html>
<head>
    <title>Nixie WASM from CDN</title>
</head>
<body>
    <script type="module">
        // Load from unpkg
        import init, { WasmSolver } from 'https://unpkg.com/@cooljapan/nixie@latest/pkg/nixie_wasm.js';

        async function main() {
            await init();
            const solver = new WasmSolver();

            solver.execute(`
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (> x 5))
                (check-sat)
                (get-model)
            `);

            console.log('Solver ready!');
        }

        main();
    </script>
</body>
</html>
```

### Using jsDelivr

```html
<script type="module">
    // Load from jsDelivr
    import init, { WasmSolver } from 'https://cdn.jsdelivr.net/npm/@cooljapan/nixie@latest/pkg/nixie_wasm.js';

    async function main() {
        await init();
        const solver = new WasmSolver();
        // Use solver...
    }

    main();
</script>
```

## Version Pinning

### Specific Version

It's recommended to pin to a specific version in production:

```javascript
// unpkg
import init from 'https://unpkg.com/@cooljapan/nixie@0.2.0/pkg/nixie_wasm.js';

// jsDelivr
import init from 'https://cdn.jsdelivr.net/npm/@cooljapan/nixie@0.2.0/pkg/nixie_wasm.js';
```

### Version Ranges

```javascript
// Latest 0.2.x
import init from 'https://unpkg.com/@cooljapan/nixie@^0.2.0/pkg/nixie_wasm.js';

// Latest 0.x.x
import init from 'https://unpkg.com/@cooljapan/nixie@0/pkg/nixie_wasm.js';
```

## CDN Features

### unpkg

- **URL Format**: `https://unpkg.com/[package]@[version]/[file]`
- **Latest version**: Use `@latest` or omit version
- **Automatic redirects**: Resolves semver ranges
- **File browsing**: Visit package root to browse files
- **Example**: https://unpkg.com/@cooljapan/nixie@latest/

### jsDelivr

- **URL Format**: `https://cdn.jsdelivr.net/npm/[package]@[version]/[file]`
- **Minified files**: Add `.min` before extension
- **Combine files**: Supports combining multiple files
- **Stats**: Provides download statistics
- **Example**: https://cdn.jsdelivr.net/npm/@cooljapan/nixie@latest/

## Loading Strategies

### Direct ESM Import (Recommended)

```html
<script type="module">
    import init, { WasmSolver, version } from 'https://unpkg.com/@cooljapan/nixie/pkg/nixie_wasm.js';

    async function run() {
        await init();
        console.log('Nixie version:', version());
        const solver = new WasmSolver();
        // Use solver...
    }

    run();
</script>
```

### Dynamic Import

```html
<script>
    async function loadSolver() {
        const module = await import('https://unpkg.com/@cooljapan/nixie/pkg/nixie_wasm.js');
        await module.default(); // init()

        const solver = new module.WasmSolver();
        return solver;
    }

    loadSolver().then(solver => {
        console.log('Solver loaded!');
    });
</script>
```

### With Import Maps (Modern Browsers)

```html
<script type="importmap">
{
    "imports": {
        "@cooljapan/nixie": "https://unpkg.com/@cooljapan/nixie/pkg/nixie_wasm.js"
    }
}
</script>

<script type="module">
    import init, { WasmSolver } from '@cooljapan/nixie';

    await init();
    const solver = new WasmSolver();
</script>
```

## Complete Examples

### Basic SAT Solver

```html
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <title>Nixie CDN Example</title>
</head>
<body>
    <h1>Nixie WASM from CDN</h1>
    <pre id="output"></pre>

    <script type="module">
        import init, { WasmSolver } from 'https://unpkg.com/@cooljapan/nixie/pkg/nixie_wasm.js';

        const output = document.getElementById('output');

        try {
            await init();
            output.textContent = 'Loading solver...\n';

            const solver = new WasmSolver();

            const result = solver.execute(`
                (set-logic QF_LIA)
                (declare-const x Int)
                (declare-const y Int)
                (assert (> x 0))
                (assert (> y 0))
                (assert (< (+ x y) 10))
                (check-sat)
                (get-model)
            `);

            output.textContent += 'Result:\n' + result;
        } catch (error) {
            output.textContent = 'Error: ' + error.message;
        }
    </script>
</body>
</html>
```

### With Web Worker

```html
<!DOCTYPE html>
<html>
<head>
    <title>Nixie with Web Worker</title>
</head>
<body>
    <h1>Nixie in Web Worker</h1>
    <button id="solve">Solve</button>
    <pre id="output"></pre>

    <script>
        const worker = new Worker('worker.js', { type: 'module' });

        document.getElementById('solve').onclick = () => {
            worker.postMessage({
                type: 'solve',
                script: `
                    (set-logic QF_LIA)
                    (declare-const x Int)
                    (assert (> x 5))
                    (check-sat)
                    (get-model)
                `
            });
        };

        worker.onmessage = (e) => {
            document.getElementById('output').textContent = e.data.result;
        };
    </script>
</body>
</html>
```

**worker.js:**
```javascript
import init, { WasmSolver } from 'https://unpkg.com/@cooljapan/nixie/pkg/nixie_wasm.js';

let solver = null;

(async () => {
    await init();
    solver = new WasmSolver();
    console.log('Worker ready');
})();

self.onmessage = (e) => {
    if (e.data.type === 'solve') {
        try {
            const result = solver.execute(e.data.script);
            self.postMessage({ result });
        } catch (error) {
            self.postMessage({ error: error.message });
        }
    }
};
```

## TypeScript Support

CDN usage with TypeScript requires some configuration:

```typescript
// types.d.ts
declare module 'https://unpkg.com/@cooljapan/nixie/pkg/nixie_wasm.js' {
    export default function init(): Promise<void>;
    export class WasmSolver {
        constructor();
        execute(script: string): string;
        checkSat(): string;
        // ... other methods
    }
    export function version(): string;
}
```

```typescript
import init, { WasmSolver } from 'https://unpkg.com/@cooljapan/nixie/pkg/nixie_wasm.js';

async function main() {
    await init();
    const solver = new WasmSolver();
    const result = solver.execute('(check-sat)');
    console.log(result);
}
```

## Performance Considerations

### Caching

CDNs automatically cache files. Set appropriate headers for your use case:

- **unpkg**: Caches for 1 year for immutable versions
- **jsDelivr**: Caches for 7 days, purge manually if needed

### Preloading

Preload the WASM module for faster startup:

```html
<link rel="modulepreload" href="https://unpkg.com/@cooljapan/nixie/pkg/nixie_wasm.js">
<link rel="preload" href="https://unpkg.com/@cooljapan/nixie/pkg/nixie_wasm_bg.wasm" as="fetch" crossorigin>
```

### Bundle Size

The WASM bundle is optimized for size:
- Uncompressed: ~1.5-2MB
- Gzipped: ~500-800KB

Consider using a bundler for production deployments.

## CORS Considerations

CDNs set proper CORS headers for cross-origin requests. No special configuration needed.

## Fallback Strategy

```javascript
async function loadNixie() {
    const cdns = [
        'https://unpkg.com/@cooljapan/nixie/pkg/nixie_wasm.js',
        'https://cdn.jsdelivr.net/npm/@cooljapan/nixie/pkg/nixie_wasm.js'
    ];

    for (const cdn of cdns) {
        try {
            const module = await import(cdn);
            await module.default();
            return module;
        } catch (error) {
            console.warn(`Failed to load from ${cdn}:`, error);
        }
    }

    throw new Error('Failed to load Nixie from all CDNs');
}

const nixie = await loadNixie();
const solver = new nixie.WasmSolver();
```

## Security

### Subresource Integrity (SRI)

For production, use SRI hashes to ensure integrity:

```html
<script type="module"
    integrity="sha384-HASH_HERE"
    crossorigin="anonymous"
    src="https://unpkg.com/@cooljapan/nixie@0.2.0/pkg/nixie_wasm.js">
</script>
```

Generate SRI hash:
```bash
curl https://unpkg.com/@cooljapan/nixie@0.2.0/pkg/nixie_wasm.js | \
    openssl dgst -sha384 -binary | \
    openssl base64 -A
```

## Troubleshooting

### Module Not Found

Ensure you're using the correct path:
```javascript
// ✅ Correct
import init from 'https://unpkg.com/@cooljapan/nixie/pkg/nixie_wasm.js';

// ❌ Wrong (missing /pkg/)
import init from 'https://unpkg.com/@cooljapan/nixie/nixie_wasm.js';
```

### WASM Loading Failed

Check browser console for specific errors:
- Ensure browser supports WebAssembly
- Check Content-Security-Policy headers
- Verify network connectivity to CDN

### Version Not Found

Check if the version exists:
```bash
curl -I https://unpkg.com/@cooljapan/nixie@VERSION/
```

## Browser Compatibility

Nixie WASM requires:
- WebAssembly support (Chrome 57+, Firefox 52+, Safari 11+, Edge 16+)
- ES modules support (Chrome 61+, Firefox 60+, Safari 11+, Edge 16+)
- BigInt support (Chrome 67+, Firefox 68+, Safari 14+, Edge 79+)

## Additional Resources

- **NPM Package**: https://www.npmjs.com/package/@cooljapan/nixie
- **GitHub Repository**: https://github.com/cool-japan/nixie
- **Documentation**: https://docs.rs/nixie
- **Examples**: https://github.com/cool-japan/nixie/tree/main/nixie-wasm/examples

## Support

For issues or questions:
- GitHub Issues: https://github.com/cool-japan/nixie/issues
- Discussions: https://github.com/cool-japan/nixie/discussions

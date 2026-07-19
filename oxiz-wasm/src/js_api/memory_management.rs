//! Memory Management for WASM/JS Interop
#![allow(dead_code)] // Under development
//!
//! This module provides efficient memory management utilities for sharing
//! data between JavaScript and WebAssembly with minimal copying.
//!
//! # Strategies
//!
//! - **Zero-copy sharing**: Share memory views when possible
//! - **Smart pooling**: Reuse allocated buffers
//! - **Automatic cleanup**: RAII-based memory management
//! - **Memory tracking**: Monitor usage and detect leaks
//!
//! # Example
//!
//! ```javascript
//! const manager = new MemoryManager();
//!
//! // Allocate a buffer
//! const buffer = manager.allocate(1024);
//!
//! // Use the buffer
//! const view = new Uint8Array(buffer);
//! view[0] = 42;
//!
//! // Return to pool when done
//! manager.free(buffer);
//!
//! // Get statistics
//! const stats = manager.getStats();
//! console.log(`Memory usage: ${stats.used_bytes} bytes`);
//! ```

#![forbid(unsafe_code)]

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use wasm_bindgen::prelude::*;

/// Memory allocation strategy
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocationStrategy {
    /// Allocate exact size needed
    Exact,
    /// Allocate with power-of-2 sizes
    PowerOfTwo,
    /// Allocate with fixed size buckets
    Buckets,
}

/// Memory pool for buffer reuse
#[wasm_bindgen]
pub struct MemoryPool {
    /// Available buffers by size
    buffers: Rc<RefCell<HashMap<usize, Vec<Vec<u8>>>>>,
    /// Total allocated bytes
    total_allocated: Rc<RefCell<usize>>,
    /// Total freed bytes
    total_freed: Rc<RefCell<usize>>,
    /// Peak memory usage
    peak_usage: Rc<RefCell<usize>>,
    /// Allocation strategy
    strategy: AllocationStrategy,
}

#[wasm_bindgen]
impl MemoryPool {
    /// Create a new memory pool
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self {
            buffers: Rc::new(RefCell::new(HashMap::new())),
            total_allocated: Rc::new(RefCell::new(0)),
            total_freed: Rc::new(RefCell::new(0)),
            peak_usage: Rc::new(RefCell::new(0)),
            strategy: AllocationStrategy::PowerOfTwo,
        }
    }

    /// Allocate a buffer
    #[wasm_bindgen(js_name = allocate)]
    pub fn allocate(&self, size: usize) -> Vec<u8> {
        let actual_size = self.round_size(size);

        // Try to reuse from pool
        if let Some(buffer) = self.try_reuse(actual_size) {
            return buffer;
        }

        // Allocate new buffer
        let buffer = vec![0u8; actual_size];
        *self.total_allocated.borrow_mut() += actual_size;

        // Update peak
        let current = self.current_usage();
        let mut peak = self.peak_usage.borrow_mut();
        if current > *peak {
            *peak = current;
        }

        buffer
    }

    /// Return a buffer to the pool
    #[wasm_bindgen(js_name = free)]
    pub fn free(&self, buffer: Vec<u8>) {
        let size = buffer.len();
        *self.total_freed.borrow_mut() += size;

        self.buffers
            .borrow_mut()
            .entry(size)
            .or_default()
            .push(buffer);
    }

    /// Get current memory usage
    #[wasm_bindgen(js_name = currentUsage)]
    pub fn current_usage(&self) -> usize {
        self.total_allocated
            .borrow()
            .saturating_sub(*self.total_freed.borrow())
    }

    /// Get peak memory usage
    #[wasm_bindgen(js_name = peakUsage)]
    pub fn peak_usage(&self) -> usize {
        *self.peak_usage.borrow()
    }

    /// Get number of pooled buffers
    #[wasm_bindgen(js_name = pooledCount)]
    pub fn pooled_count(&self) -> usize {
        self.buffers.borrow().values().map(|v| v.len()).sum()
    }

    /// Clear all pooled buffers
    #[wasm_bindgen(js_name = clearPool)]
    pub fn clear_pool(&self) {
        self.buffers.borrow_mut().clear();
    }

    /// Get memory statistics
    #[wasm_bindgen(js_name = getStats)]
    pub fn get_stats(&self) -> JsValue {
        let stats = js_sys::Object::new();
        let _ = js_sys::Reflect::set(
            &stats,
            &"total_allocated".into(),
            &(*self.total_allocated.borrow()).into(),
        );
        let _ = js_sys::Reflect::set(
            &stats,
            &"total_freed".into(),
            &(*self.total_freed.borrow()).into(),
        );
        let _ = js_sys::Reflect::set(
            &stats,
            &"current_usage".into(),
            &self.current_usage().into(),
        );
        let _ = js_sys::Reflect::set(
            &stats,
            &"peak_usage".into(),
            &(*self.peak_usage.borrow()).into(),
        );
        let _ = js_sys::Reflect::set(
            &stats,
            &"pooled_buffers".into(),
            &self.pooled_count().into(),
        );
        stats.into()
    }

    // Helper methods

    fn round_size(&self, size: usize) -> usize {
        match self.strategy {
            AllocationStrategy::Exact => size,
            AllocationStrategy::PowerOfTwo => size.next_power_of_two(),
            AllocationStrategy::Buckets => {
                // Round to 1KB, 4KB, 16KB, 64KB, 256KB, 1MB, etc.
                const BUCKETS: &[usize] = &[
                    1024,
                    4 * 1024,
                    16 * 1024,
                    64 * 1024,
                    256 * 1024,
                    1024 * 1024,
                ];
                BUCKETS
                    .iter()
                    .find(|&&b| b >= size)
                    .copied()
                    .unwrap_or(size)
            }
        }
    }

    fn try_reuse(&self, size: usize) -> Option<Vec<u8>> {
        self.buffers.borrow_mut().get_mut(&size)?.pop()
    }
}

impl Default for MemoryPool {
    fn default() -> Self {
        Self::new()
    }
}

/// Shared memory view for zero-copy operations
#[wasm_bindgen]
pub struct SharedMemoryView {
    /// Pointer to data (for tracking)
    data_ptr: usize,
    /// Size of the view
    size: usize,
    /// Whether this view owns the data
    owns_data: bool,
}

#[wasm_bindgen]
impl SharedMemoryView {
    /// Create a new shared memory view
    #[wasm_bindgen(constructor)]
    pub fn new(size: usize) -> Self {
        Self {
            data_ptr: 0,
            size,
            owns_data: true,
        }
    }

    /// Get the size of the view
    #[wasm_bindgen(js_name = size)]
    pub fn size(&self) -> usize {
        self.size
    }

    /// Check if this view owns the data
    #[wasm_bindgen(js_name = ownsData)]
    pub fn owns_data(&self) -> bool {
        self.owns_data
    }
}

/// Memory manager with tracking and leak detection
///
/// Unlike [`MemoryPool`], which only tracks aggregate byte counts,
/// `MemoryManager` keeps the actual allocated buffers alive (keyed by an
/// opaque allocation id) so they can be retrieved with [`MemoryManager::get`]
/// and returned to the pool with [`MemoryManager::free`]. This makes
/// `allocate`/`free`/`get` a real (not merely bookkeeping) memory API.
#[wasm_bindgen]
pub struct MemoryManager {
    /// Memory pool used to satisfy new allocations and recycle freed ones
    pool: MemoryPool,
    /// Buffers that are currently allocated and not yet freed, keyed by id
    buffers: Rc<RefCell<HashMap<usize, Vec<u8>>>>,
    /// Active allocations (bookkeeping metadata, populated when leak
    /// detection is enabled)
    active: Rc<RefCell<HashMap<usize, AllocationInfo>>>,
    /// Next allocation ID
    next_id: Rc<RefCell<usize>>,
    /// Enable leak detection
    leak_detection: bool,
}

#[derive(Debug, Clone)]
struct AllocationInfo {
    id: usize,
    size: usize,
    timestamp: f64,
    #[allow(dead_code)]
    stack_trace: Option<String>,
}

#[wasm_bindgen]
impl MemoryManager {
    /// Create a new memory manager
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self {
            pool: MemoryPool::new(),
            buffers: Rc::new(RefCell::new(HashMap::new())),
            active: Rc::new(RefCell::new(HashMap::new())),
            next_id: Rc::new(RefCell::new(0)),
            leak_detection: false,
        }
    }

    /// Enable leak detection
    #[wasm_bindgen(js_name = enableLeakDetection)]
    pub fn enable_leak_detection(&mut self, enabled: bool) {
        self.leak_detection = enabled;
    }

    /// Allocate memory
    ///
    /// Returns an opaque allocation id. The backing buffer is kept alive
    /// internally and can be read with [`MemoryManager::get`], overwritten
    /// with [`MemoryManager::set`], and returned to the pool with
    /// [`MemoryManager::free`].
    #[wasm_bindgen(js_name = allocate)]
    pub fn allocate(&self, size: usize) -> usize {
        let buffer = self.pool.allocate(size);
        let id = self.get_next_id();

        if self.leak_detection {
            let timestamp = web_sys::window()
                .and_then(|w| w.performance())
                .map(|p| p.now())
                .unwrap_or(0.0);

            self.active.borrow_mut().insert(
                id,
                AllocationInfo {
                    id,
                    size: buffer.len(),
                    timestamp,
                    stack_trace: None,
                },
            );
        }

        // Keep the buffer alive and retrievable by id instead of dropping it.
        self.buffers.borrow_mut().insert(id, buffer);
        id
    }

    /// Read the current contents of an allocation.
    ///
    /// Returns `undefined` (via `None`) if `id` does not refer to a live
    /// allocation (never allocated, or already freed).
    #[wasm_bindgen(js_name = get)]
    pub fn get(&self, id: usize) -> Option<Vec<u8>> {
        self.buffers.borrow().get(&id).cloned()
    }

    /// Overwrite the contents of an allocation.
    ///
    /// The allocation is resized to `data.len()`. Returns `false` if `id`
    /// does not refer to a live allocation.
    #[wasm_bindgen(js_name = set)]
    pub fn set(&self, id: usize, data: &[u8]) -> bool {
        let mut buffers = self.buffers.borrow_mut();
        match buffers.get_mut(&id) {
            Some(buffer) => {
                *buffer = data.to_vec();
                true
            }
            None => false,
        }
    }

    /// Get the size in bytes of a live allocation, or `undefined` if `id`
    /// does not refer to one.
    #[wasm_bindgen(js_name = sizeOf)]
    pub fn size_of(&self, id: usize) -> Option<usize> {
        self.buffers.borrow().get(&id).map(Vec::len)
    }

    /// Free memory
    ///
    /// Returns `true` if `id` referred to a live allocation that was just
    /// freed and returned to the pool, or `false` if `id` was never
    /// allocated or was already freed (honest double-free reporting).
    #[wasm_bindgen(js_name = free)]
    pub fn free(&self, id: usize) -> bool {
        let buffer = self.buffers.borrow_mut().remove(&id);
        match buffer {
            Some(buffer) => {
                if self.leak_detection {
                    self.active.borrow_mut().remove(&id);
                }
                self.pool.free(buffer);
                true
            }
            None => false,
        }
    }

    /// Get the number of live (allocated, not yet freed) allocations.
    #[wasm_bindgen(js_name = activeCount)]
    pub fn active_count(&self) -> usize {
        self.buffers.borrow().len()
    }

    /// Detect memory leaks
    #[wasm_bindgen(js_name = detectLeaks)]
    pub fn detect_leaks(&self, max_age_ms: f64) -> JsValue {
        if !self.leak_detection {
            return JsValue::NULL;
        }

        let current_time = web_sys::window()
            .and_then(|w| w.performance())
            .map(|p| p.now())
            .unwrap_or(0.0);

        let leaks = js_sys::Array::new();

        for info in self.active.borrow().values() {
            let age = current_time - info.timestamp;
            if age > max_age_ms {
                let leak = js_sys::Object::new();
                let _ = js_sys::Reflect::set(&leak, &"id".into(), &info.id.into());
                let _ = js_sys::Reflect::set(&leak, &"size".into(), &info.size.into());
                let _ = js_sys::Reflect::set(&leak, &"age_ms".into(), &age.into());
                leaks.push(&leak);
            }
        }

        leaks.into()
    }

    /// Get memory statistics
    #[wasm_bindgen(js_name = getStats)]
    pub fn get_stats(&self) -> JsValue {
        let pool_stats = self.pool.get_stats();
        let _ = js_sys::Reflect::set(
            &pool_stats,
            &"active_allocations".into(),
            &self.active_count().into(),
        );
        pool_stats
    }

    /// Force garbage collection hint
    #[wasm_bindgen(js_name = gc)]
    pub fn gc(&self) {
        self.pool.clear_pool();
    }

    fn get_next_id(&self) -> usize {
        let mut next_id = self.next_id.borrow_mut();
        let id = *next_id;
        *next_id += 1;
        id
    }
}

impl Default for MemoryManager {
    fn default() -> Self {
        Self::new()
    }
}

/// Buffer copier for efficient data transfer
#[wasm_bindgen]
pub struct BufferCopier;

#[wasm_bindgen]
impl BufferCopier {
    /// Copy bytes from source to destination
    #[wasm_bindgen(js_name = copy)]
    pub fn copy(src: &[u8], dst: &mut [u8], count: usize) -> usize {
        let to_copy = count.min(src.len()).min(dst.len());
        dst[..to_copy].copy_from_slice(&src[..to_copy]);
        to_copy
    }

    /// Zero out a buffer
    #[wasm_bindgen(js_name = zero)]
    pub fn zero(dst: &mut [u8]) {
        dst.fill(0);
    }

    /// Fill a buffer with a value
    #[wasm_bindgen(js_name = fill)]
    pub fn fill(dst: &mut [u8], value: u8) {
        dst.fill(value);
    }

    /// Compare two buffers
    #[wasm_bindgen(js_name = compare)]
    pub fn compare(a: &[u8], b: &[u8]) -> i32 {
        use std::cmp::Ordering;
        match a.cmp(b) {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_pool_allocation() {
        let pool = MemoryPool::new();
        let buffer = pool.allocate(100);
        assert_eq!(buffer.len(), 128); // Next power of 2

        assert_eq!(pool.current_usage(), 128);
        assert_eq!(pool.peak_usage(), 128);
    }

    #[test]
    fn test_memory_pool_reuse() {
        let pool = MemoryPool::new();

        let buffer = pool.allocate(100);
        let size = buffer.len();
        pool.free(buffer);

        assert_eq!(pool.pooled_count(), 1);

        let buffer2 = pool.allocate(100);
        assert_eq!(buffer2.len(), size);
        assert_eq!(pool.pooled_count(), 0);
    }

    #[test]
    fn test_memory_manager() {
        let manager = MemoryManager::new();

        let id1 = manager.allocate(100);
        let id2 = manager.allocate(200);

        assert!(id1 != id2);
    }

    #[test]
    fn test_memory_manager_allocate_is_not_a_no_op() {
        let manager = MemoryManager::new();

        let id = manager.allocate(16);
        // The buffer must actually be retrievable, not dropped.
        let buf = manager.get(id).expect("allocated buffer should exist");
        assert_eq!(buf.len(), 16); // next_power_of_two(16) == 16
        assert_eq!(manager.active_count(), 1);
    }

    #[test]
    fn test_memory_manager_set_and_get_round_trip() {
        let manager = MemoryManager::new();
        let id = manager.allocate(8);

        assert!(manager.set(id, &[1, 2, 3, 4]));
        let data = manager.get(id).expect("buffer should exist");
        assert_eq!(data, vec![1, 2, 3, 4]);
        assert_eq!(manager.size_of(id), Some(4));
    }

    #[test]
    fn test_memory_manager_free_is_honest() {
        let manager = MemoryManager::new();
        let id = manager.allocate(32);

        // First free succeeds because the allocation is live.
        assert!(manager.free(id));
        // The buffer must no longer be retrievable after free.
        assert!(manager.get(id).is_none());
        // A second free (or freeing an id that never existed) must report
        // false rather than unconditionally claiming success.
        assert!(!manager.free(id));
        assert!(!manager.free(99_999));
    }

    #[test]
    fn test_memory_manager_get_unknown_id() {
        let manager = MemoryManager::new();
        assert!(manager.get(42).is_none());
        assert!(!manager.set(42, &[1, 2, 3]));
        assert_eq!(manager.size_of(42), None);
    }

    #[test]
    fn test_buffer_copier() {
        let src = vec![1, 2, 3, 4, 5];
        let mut dst = vec![0, 0, 0, 0, 0];

        let copied = BufferCopier::copy(&src, &mut dst, 5);
        assert_eq!(copied, 5);
        assert_eq!(dst, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_buffer_zero() {
        let mut buffer = vec![1, 2, 3, 4, 5];
        BufferCopier::zero(&mut buffer);
        assert_eq!(buffer, vec![0, 0, 0, 0, 0]);
    }

    #[test]
    fn test_buffer_compare() {
        let a = vec![1, 2, 3];
        let b = vec![1, 2, 3];
        let c = vec![1, 2, 4];

        assert_eq!(BufferCopier::compare(&a, &b), 0);
        assert_eq!(BufferCopier::compare(&a, &c), -1);
        assert_eq!(BufferCopier::compare(&c, &a), 1);
    }
}

//! Diagnostic-only matched controls. Removed before any production landing.
use nixie_core::ast::{TermId, TermKind, TermManager};
use num_bigint::BigInt;
use std::sync::{
    OnceLock,
    atomic::{AtomicU64, Ordering},
};
static SEED: AtomicU64 = AtomicU64::new(0);
static SLOTS: AtomicU64 = AtomicU64::new(0);
static ELIGIBLE: AtomicU64 = AtomicU64::new(0);
static CHANGED: AtomicU64 = AtomicU64::new(0);
pub(crate) fn seed(seed: u64) {
    SEED.store(seed, Ordering::Relaxed);
}
fn null() -> bool {
    static MODE: OnceLock<bool> = OnceLock::new();
    *MODE.get_or_init(|| std::env::var("NIXIE_POLICY_CONTROL").is_ok_and(|s| s == "null"))
}
fn mix(tag: u64) -> u64 {
    let mut z = SEED
        .load(Ordering::Relaxed)
        .wrapping_add(tag)
        .wrapping_add(0x9e3779b97f4a7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}
fn select(real: usize, alternative: usize) -> usize {
    SLOTS.fetch_add(1, Ordering::Relaxed);
    if real != alternative {
        ELIGIBLE.fetch_add(1, Ordering::Relaxed);
    }
    if null() {
        if real != alternative {
            CHANGED.fetch_add(1, Ordering::Relaxed);
        }
        alternative
    } else {
        real
    }
}
pub(crate) fn index(real: usize, len: usize, tag: u64) -> usize {
    let alternative = if len > 1 {
        (real + 1 + (mix(tag) % (len as u64 - 1)) as usize) % len
    } else {
        real
    };
    select(real, alternative)
}
pub(crate) fn rotate(values: &mut [String], tag: u64) {
    let len = values.len();
    if len < 2 {
        return;
    }
    let shift = 1 + (mix(tag) % (len as u64 - 1)) as usize;
    let original = values.to_vec();
    for (i, value) in values.iter_mut().enumerate() {
        let alternative = (i + shift) % len;
        let chosen = select(i, alternative);
        // Index movement is not an effective content intervention when values coincide.
        if original[i] == original[alternative] {
            ELIGIBLE.fetch_sub(1, Ordering::Relaxed);
            if null() {
                CHANGED.fetch_sub(1, Ordering::Relaxed);
            }
        }
        *value = original[chosen].clone();
    }
}
pub(crate) fn value(real: TermId, manager: &mut TermManager) -> TermId {
    let r = mix(17);
    let offset = 1 + (r % 65535) as i64;
    let alternative = match manager.get(real).map(|n| n.kind.clone()) {
        Some(TermKind::IntConst(value)) => {
            manager.mk_int(value + if r & 1 == 0 { offset } else { -offset })
        }
        Some(TermKind::BitVecConst { value, width }) if width > 0 => {
            let modulus = BigInt::from(1u8) << width;
            let offset = BigInt::from(offset | 1) % &modulus;
            manager.mk_bitvec((value + offset) % modulus, width)
        }
        Some(TermKind::True) => manager.mk_false(),
        Some(TermKind::False) => manager.mk_true(),
        _ => real,
    };
    let chosen = select(0, usize::from(real != alternative));
    if chosen == 0 { real } else { alternative }
}
pub(crate) struct Report;
impl Drop for Report {
    fn drop(&mut self) {
        eprintln!(
            "policy-control seed={} slots={} eligible={} changed={}",
            SEED.load(Ordering::Relaxed),
            SLOTS.load(Ordering::Relaxed),
            ELIGIBLE.load(Ordering::Relaxed),
            CHANGED.load(Ordering::Relaxed)
        );
    }
}

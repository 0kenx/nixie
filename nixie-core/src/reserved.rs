//! Names for solver-internal symbols that cannot be spelled in SMT-LIB input.

#[cfg(not(feature = "std"))]
use crate::prelude::{String, format};

/// Prefix shared by internal names. SMT-LIB forbids backslashes in both
/// simple and quoted symbols, so input cannot capture these symbols.
pub const RESERVED_PREFIX: &str = "\\nixie.";

/// Internal function symbol for a constant array, distinct from every user UF.
pub const CONST_ARRAY_FUNC: &str = "\\nixie.const-array";

/// Prefix for array-extensionality witness indices.
pub const ARRAY_EXT_WITNESS_PREFIX: &str = "\\nixie.ext!";

/// Prefix for array indices outside a store chain.
pub const ARRAY_OFF_CHAIN_PREFIX: &str = "\\nixie.off!";

/// Construct an internal name from a purpose tag and a distinguishing suffix.
#[must_use]
pub fn reserved_name(tag: &str, suffix: &str) -> String {
    format!("{RESERVED_PREFIX}{tag}!{suffix}")
}

/// Whether `name` belongs to the internal family identified by `tag`.
#[must_use]
pub fn is_reserved_tag(name: &str, tag: &str) -> bool {
    name.strip_prefix(RESERVED_PREFIX)
        .and_then(|rest| rest.strip_prefix(tag))
        .is_some_and(|rest| rest.starts_with('!'))
}

/// Whether a symbol is an encoder proxy whose model value can override its
/// temporary arithmetic tableau value. Skolems and other witnesses are not proxies.
#[must_use]
pub fn is_encoder_proxy(name: &str) -> bool {
    [
        "ite",
        "boolarg",
        "numarg",
        "order-pad",
        "ite-table",
        "uncnstr",
        "arith-proxy",
    ]
    .iter()
    .any(|tag| is_reserved_tag(name, tag))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn families_do_not_match_user_names_or_other_tags() {
        let name = reserved_name("sk", "17");
        assert!(is_reserved_tag(&name, "sk"));
        assert!(!is_reserved_tag(&name, "skf"));
        assert!(!is_reserved_tag("sk!17", "sk"));
        assert!(CONST_ARRAY_FUNC.starts_with(RESERVED_PREFIX));
        assert!(ARRAY_EXT_WITNESS_PREFIX.starts_with(RESERVED_PREFIX));
        assert!(ARRAY_OFF_CHAIN_PREFIX.starts_with(RESERVED_PREFIX));
        assert!(is_encoder_proxy(&reserved_name("ite", "17")));
        assert!(is_encoder_proxy(&reserved_name("arith-proxy", "3")));
        assert!(!is_encoder_proxy("__nixie_ite_17"));
        assert!(!is_encoder_proxy("$price"));
        assert!(!is_encoder_proxy(&reserved_name("sk", "17")));
    }
}

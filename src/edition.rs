//! Explicit constitutional edition, independently of the compiler release.
//!
//! Parsing this value is configuration validation, not semantic acceptance.

use std::fmt;
use std::str::FromStr;

/// A supported constitutional regime. Callers must select it explicitly.
/// There is no default, floating selection or conversion from a product version.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Edition {
    E2026,
}

impl Edition {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::E2026 => "2026",
        }
    }

    /// Exact numeric identity for the native protocol's edition field.
    pub const fn as_u32(self) -> u32 {
        match self {
            Self::E2026 => 2026,
        }
    }
}

impl fmt::Display for Edition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnsupportedEdition(String);

impl fmt::Display for UnsupportedEdition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "unsupported Qleisli edition {:?}; only \"2026\" is supported",
            self.0
        )
    }
}

impl std::error::Error for UnsupportedEdition {}

impl FromStr for Edition {
    type Err = UnsupportedEdition;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "2026" => Ok(Self::E2026),
            _ => Err(UnsupportedEdition(value.to_owned())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_an_explicit_supported_identity_parses() {
        assert_eq!("2026".parse(), Ok(Edition::E2026));
        assert_eq!(Edition::E2026.as_u32(), 2026);
        for value in [
            "",
            "latest",
            "current",
            "*",
            "2027",
            "02026",
            "2026 ",
            " 2026",
            "0.3.0-beta",
        ] {
            assert!(value.parse::<Edition>().is_err(), "{value:?}");
        }
    }
}

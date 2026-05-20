#![doc = include_str!("../README.md")]
#![warn(missing_docs)]

#[cfg(feature = "find")]
mod find;
mod loc;

// === Re-exports ===

#[cfg(feature = "find")]
pub use find::*;
pub use loc::*;

// === Result/Error used within this crate ===

type Result<T> = std::result::Result<T, Error>;
type Error = Box<dyn std::error::Error + Send + Sync>;

// === Hash map used within this crate ===

type Map<K, V> = std::collections::HashMap<K, V, fxhash::FxBuildHasher>;

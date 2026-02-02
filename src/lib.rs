#![doc = include_str!("../README.md")]

#[cfg(feature = "find")]
mod find;
mod loc;

// === Re-exports ===

pub use any_intern::Interned;
#[cfg(feature = "find")]
pub use find::*;
pub use loc::*;

// === Result/Error used within this crate ===

type Result<T> = std::result::Result<T, Error>;
type Error = Box<dyn std::error::Error + Send + Sync>;

// === Hash Map/Set used within this crate ===

type Map<K, V> = std::collections::HashMap<K, V, fxhash::FxBuildHasher>;

#![doc = include_str!("../README.md")]

mod loc;
#[cfg(feature = "find")]
mod find;

// === Re-exports ===

pub use loc::{Locate, LocateEntry, LocateGroup, Location, enable_thread_local, is_located, clear};
#[cfg(feature = "find")]
pub use find::{Find, FindPtr};

// === Result/Error used within this crate ===

type Result<T> = std::result::Result<T, Error>;
type Error = Box<dyn std::error::Error + Send + Sync>;

// === Hash Map/Set used within this crate ===

type Map<K, V> = std::collections::HashMap<K, V, fxhash::FxBuildHasher>;

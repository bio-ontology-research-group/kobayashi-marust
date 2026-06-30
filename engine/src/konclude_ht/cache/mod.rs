//! `konclude_ht::cache` — W6, the cache subtree (Konclude
//! `Source/Reasoner/Kernel/Cache/`). Nine families ported as struct-definition
//! files (the `// W6-CACHE method-batch` markers flag where method bodies land
//! in a later wave). See `PORT.md` §W6.

pub mod context;
pub mod base;
pub mod value;
pub mod unsat;
pub mod reuse;
pub mod satnode;
pub mod consequences;
pub mod sigexpand;
pub mod occstats;
pub mod events;
pub mod backend;
pub mod backend_data;
pub mod backend_facade1;
pub mod backend_facade_gap;
pub mod backend_facade2;
pub mod backend_facade3;
pub mod pending;

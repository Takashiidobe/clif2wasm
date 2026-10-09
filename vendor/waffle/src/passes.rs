//! Passes.

pub mod basic_opt;
pub mod dom_pass;
pub mod empty_blocks;
pub mod maxssa;
pub mod resolve_aliases;
// pub mod ssa;
// pub mod trace;
pub mod mem_fusing;
pub mod reorder_funs;
pub mod unmem;
// pub mod fixup_rets;
pub mod frint;
pub mod inline;
#[cfg(feature = "tcore")]
pub mod tcore;
pub mod ub_vaccum;
#[cfg(feature = "importify")]
pub mod importify;
#[cfg(feature = "copying")]
pub mod mapping;
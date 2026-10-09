//! Error types.
use alloc::string::String;
/// An error that occurs when translating Wasm to IR.
#[derive(Clone, Debug)]
pub enum FrontendError {
    /// The given WebAssembly feature is not supported.
    UnsupportedFeature(String),
    /// Some dimension of the WebAssembly module is too large to be
    /// supported by this library.
    TooLarge(String),
    /// An internal error occurred.
    Internal(String),
}

impl core::fmt::Display for FrontendError {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        core::fmt::Debug::fmt(self, f)
    }
}

impl core::error::Error for FrontendError {}

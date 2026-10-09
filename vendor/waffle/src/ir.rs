//! Intermediate representation for Wasm.

use alloc::collections::BTreeSet;

use crate::{declare_entity, entity::EntityRef};

pub trait Subtypes {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool;
}

impl Subtypes for Signature {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool {
        if vsigs.contains(&(*self, *other)) {
            return true;
        }
        let mut vsigs = vsigs.clone();
        vsigs.insert((*self, *other));
        module.signatures[*self].subtypes(&module.signatures[*other], module, &vsigs)
    }
}
impl Subtypes for SignatureData {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool {
        match (self, other) {
            (SignatureData::Array { ty, .. }, SignatureData::Array { ty: tyo, .. }) => {
                ty.subtypes(tyo, module, vsigs)
            }
            (
                SignatureData::Func {
                    params, returns, ..
                },
                SignatureData::Func {
                    params: po,
                    returns: ro,
                    ..
                },
            ) => {
                params.len() == po.len()
                    && returns.len() == ro.len()
                    && params
                        .iter()
                        .zip(po.iter())
                        .all(|(a, b)| b.subtypes(a, module, vsigs))
                    && returns
                        .iter()
                        .zip(ro.iter())
                        .all(|(a, b)| a.subtypes(b, module, vsigs))
            }
            (SignatureData::Struct { fields, .. }, SignatureData::Struct { fields: fo, .. }) => {
                fields.len() >= fo.len()
                    && fields
                        .iter()
                        .zip(fo.iter())
                        .all(|(a, b)| a.subtypes(b, module, vsigs))
            }
            _ => false,
        }
    }
}
impl<T: Subtypes> Subtypes for WithMutablility<T> {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool {
        return self.mutable == other.mutable && self.value.subtypes(&other.value, module, vsigs);
    }
}
impl<T: Subtypes> Subtypes for WithNullable<T> {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool {
        return (self.nullable == other.nullable || self.nullable)
            && self.value.subtypes(&other.value, module, vsigs);
    }
}
impl Subtypes for StorageType {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool {
        return self
            .clone()
            .unpack()
            .subtypes(&other.clone().unpack(), module, vsigs);
    }
}
impl Subtypes for Type {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool {
        match (self, other) {
            (Type::I32, Type::I32) => true,
            (Type::I64, Type::I64) => true,
            (Type::F32, Type::F32) => true,
            (Type::F64, Type::F64) => true,
            (Type::V128, Type::V128) => true,
            (Type::Heap(h), Type::Heap(i)) => h.subtypes(i, module, vsigs),
            _ => false,
        }
    }
}
impl Subtypes for HeapType {
    fn subtypes(
        &self,
        other: &Self,
        module: &Module,
        vsigs: &BTreeSet<(Signature, Signature)>,
    ) -> bool {
        match (self, other) {
            (HeapType::ExternRef, HeapType::ExternRef) => true,
            (HeapType::FuncRef, HeapType::FuncRef) => true,
            (HeapType::Sig { sig_index }, HeapType::Sig { sig_index: s2 }) => {
                sig_index.subtypes(s2, module, vsigs)
            }
            (HeapType::FuncRef, HeapType::Sig { sig_index }) => {
                matches!(&module.signatures[*sig_index], SignatureData::Func { .. })
            }
            (HeapType::Array, HeapType::Sig { sig_index }) => {
                matches!(&module.signatures[*sig_index], SignatureData::Array { .. })
            }
            _ => false,
        }
    }
}

#[non_exhaustive]
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
/// Types in waffle's IR.
///
/// These types correspond to (a subset of) the primitive Wasm value
/// types: integers, floats, SIMD vectors, and function references
/// (optionally typed).
///
/// Every SSA value in a function body has a `Type`, unless it is a
/// tuple (multi-value or zero-value result).

pub enum Type {
    /// A 32-bit integer. Signedness is unspecified: individual
    /// operators specify how they handle sign.
    I32,
    /// A 64-bit integer. Signedness is unspecified: individual
    /// operators specify how they handle sign.
    I64,
    /// A 32-bit IEEE 754 floating point value. Semantics around NaNs
    /// are defined by individual operators; from the point of view of
    /// IR scaffolding, floating-point values are bags of bits.
    F32,
    /// A 64-bit IEEE 754 floating point value. Semantics around NaNs
    /// are defined by individual operators; from the point of view of
    /// IR scaffolding, floating-point values are bags of bits.
    F64,
    /// A 128-bit SIMD vector value. Lanes and lane types are
    /// specified by individual operators; from the point of view of
    /// IR scaffolding, SIMD vector values are bags of bits.
    V128,
    /// A heap type.
    Heap(WithNullable<HeapType>),
}
#[non_exhaustive]
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
///a `Type` that can be stored on the heap
pub enum HeapType {
    FuncRef,
    ExternRef,
    Sig { sig_index: Signature },
    Array,
}
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
///Something, alsong with whether it can be `null`
pub struct WithNullable<T> {
    pub value: T,
    pub nullable: bool,
}
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
///Something, alsong with whether it can be mutated
pub struct WithMutablility<T> {
    pub value: T,
    pub mutable: bool,
}
#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    serde::Serialize,
    serde::Deserialize,
    Default,
)]
///An exception's handler
pub enum Handler<T> {
    ///Rethrow the exception
    #[default]
    Throw,
    ///Catch the exception
    Catch(T),
}
#[non_exhaustive]
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
///A storage type
pub enum StorageType {
    Val(Type),
    I8,
    I16,
}

impl StorageType {
    pub fn unpack(self) -> Type {
        match self {
            StorageType::Val(a) => a,
            StorageType::I8 => Type::I32,
            StorageType::I16 => Type::I64,
        }
    }
}

impl From<wasmparser::ValType> for Type {
    fn from(ty: wasmparser::ValType) -> Self {
        match ty {
            wasmparser::ValType::I32 => Type::I32,
            wasmparser::ValType::I64 => Type::I64,
            wasmparser::ValType::F32 => Type::F32,
            wasmparser::ValType::F64 => Type::F64,
            wasmparser::ValType::V128 => Type::V128,
            wasmparser::ValType::Ref(r) => Type::Heap(r.into()),
        }
    }
}
impl From<wasmparser::FieldType> for WithMutablility<StorageType> {
    fn from(value: wasmparser::FieldType) -> Self {
        WithMutablility {
            value: match value.element_type {
                wasmparser::StorageType::I8 => StorageType::I8,
                wasmparser::StorageType::I16 => StorageType::I16,
                wasmparser::StorageType::Val(val_type) => StorageType::Val(val_type.into()),
            },
            mutable: value.mutable,
        }
    }
}
impl From<wasmparser::RefType> for WithNullable<HeapType> {
    fn from(ty: wasmparser::RefType) -> Self {
        if ty.is_extern_ref() {
            return WithNullable {
                nullable: ty.is_nullable(),
                value: HeapType::ExternRef,
            };
        }
        if ty.is_array_ref() {
            return WithNullable {
                nullable: ty.is_nullable(),
                value: HeapType::Array,
            };
        }
        match ty.type_index() {
            Some(idx) => {
                let nullable = ty.is_nullable();
                WithNullable {
                    nullable,
                    value: HeapType::Sig {
                        sig_index: Signature::new(idx.as_module_index().unwrap() as usize),
                    },
                }
            }
            None => WithNullable {
                value: HeapType::FuncRef,
                nullable: ty.is_nullable(),
            },
        }
    }
}

impl core::fmt::Display for Type {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Type::I32 => write!(f, "i32"),
            Type::I64 => write!(f, "i64"),
            Type::F32 => write!(f, "f32"),
            Type::F64 => write!(f, "f64"),
            Type::V128 => write!(f, "v128"),
            Type::Heap(h) => write!(
                f,
                "ref({} {})",
                if h.nullable { "null" } else { "not_null" },
                &h.value
            ),
        }
    }
}

impl core::fmt::Display for HeapType {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            HeapType::FuncRef => write!(f, "funcref"),
            HeapType::ExternRef => write!(f, "externref"),
            HeapType::Sig { sig_index } => write!(f, "sigref({})", sig_index),
            HeapType::Array => write!(f, "arrayref"),
        }
    }
}

impl From<Type> for wasm_encoder::ValType {
    fn from(ty: Type) -> wasm_encoder::ValType {
        match ty {
            Type::I32 => wasm_encoder::ValType::I32,
            Type::I64 => wasm_encoder::ValType::I64,
            Type::F32 => wasm_encoder::ValType::F32,
            Type::F64 => wasm_encoder::ValType::F64,
            Type::V128 => wasm_encoder::ValType::V128,
            Type::Heap(h) => wasm_encoder::ValType::Ref(h.into()),
        }
    }
}

impl From<WithMutablility<StorageType>> for wasm_encoder::FieldType {
    fn from(value: WithMutablility<StorageType>) -> Self {
        wasm_encoder::FieldType {
            element_type: match value.value {
                StorageType::Val(t) => wasm_encoder::StorageType::Val(t.into()),
                StorageType::I8 => wasm_encoder::StorageType::I8,
                StorageType::I16 => wasm_encoder::StorageType::I16,
            },
            mutable: value.mutable,
        }
    }
}

impl From<WithNullable<HeapType>> for wasm_encoder::RefType {
    fn from(ty: WithNullable<HeapType>) -> wasm_encoder::RefType {
        match &ty.value {
            HeapType::ExternRef => wasm_encoder::RefType::EXTERNREF,
            HeapType::FuncRef => wasm_encoder::RefType::FUNCREF,
            HeapType::Sig { sig_index } => wasm_encoder::RefType {
                nullable: ty.nullable,
                heap_type: wasm_encoder::HeapType::Concrete(sig_index.0),
            },
            HeapType::Array => wasm_encoder::RefType::ARRAYREF,
            _ => panic!("Cannot convert {:?} into reftype", ty),
        }
    }
}

// Per-module index spaces:

// A signature (list of parameter types and list of return types) in
// the module.
declare_entity!(Signature, "sig");
// A function in the module.
declare_entity!(Func, "func");
// A global variable in the module.
declare_entity!(Global, "global");
// A table in the module.
declare_entity!(Table, "table");
// A memory in the module.
declare_entity!(Memory, "memory");
// A control tag in the module
declare_entity!(ControlTag, "control_tag");
// Per-function index spaces:

// A basic block in one function body.
declare_entity!(Block, "block");
// A local variable (storage slot) in one function body.
declare_entity!(Local, "local");
// An SSA value in one function body.
declare_entity!(Value, "v");

mod module;
pub use module::*;
mod func;
pub use func::*;
mod value;
pub use value::*;
mod display;
pub use display::*;
mod debug;
pub use debug::*;

//! Type-safe indices and indexed containers.

use core::default::Default;
use core::fmt::Debug;
use core::hash::Hash;
use core::marker::PhantomData;
use core::ops::{Index, IndexMut};

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;
use arena_traits::{Arena, IndexAlloc, IndexIter};

/// An index into an index-space of entities.
pub trait EntityRef: Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Hash {
    /// Create a new type-safe index value from a known index.
    fn new(value: usize) -> Self;
    /// Get the index value of this type-safe index. Must be a valid
    /// index (will panic otherwise).
    fn index(self) -> usize;
    /// A sentinel invalid value.
    fn invalid() -> Self;
    /// Is this index a valid index (not equal to `Self::invalid()`)?
    fn is_valid(self) -> bool {
        self != Self::invalid()
    }
    /// Is this index an invalid index (equal to `Self::invalid()`)?
    fn is_invalid(self) -> bool {
        self == Self::invalid()
    }
    /// Turn a valid index into `Some(index)`, and an invalid index
    /// into `None`.
    fn maybe_index(self) -> Option<usize> {
        if self.is_valid() {
            Some(self.index())
        } else {
            None
        }
    }
}

#[macro_export]
macro_rules! declare_entity {
    ($name:tt, $prefix:tt) => {
        #[derive(
            Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
        )]
        pub struct $name(u32);

        impl $crate::entity::EntityRef for $name {
            fn new(value: usize) -> Self {
                use core::convert::TryFrom;
                let value = u32::try_from(value).unwrap();
                debug_assert!(value != u32::MAX);
                Self(value)
            }
            fn index(self) -> usize {
                debug_assert!(self.is_valid());
                self.0 as usize
            }
            fn invalid() -> Self {
                Self(u32::MAX)
            }
        }

        impl core::convert::From<u32> for $name {
            fn from(val: u32) -> Self {
                <Self as $crate::entity::EntityRef>::new(val as usize)
            }
        }

        impl core::default::Default for $name {
            fn default() -> Self {
                <Self as $crate::entity::EntityRef>::invalid()
            }
        }

        impl core::fmt::Debug for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                write!(f, "{}{}", $prefix, self.0)
            }
        }
        impl core::fmt::Display for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                write!(f, "{}{}", $prefix, self.0)
            }
        }
    };
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct EntityVec<Idx: EntityRef, T: Clone + Debug>(Vec<T>, PhantomData<Idx>);

impl<Idx: EntityRef, T: Clone + Debug> core::default::Default for EntityVec<Idx, T> {
    fn default() -> Self {
        Self(vec![], PhantomData)
    }
}

impl<Idx: EntityRef, T: Clone + Debug> From<Vec<T>> for EntityVec<Idx, T> {
    fn from(vec: Vec<T>) -> Self {
        Self(vec, PhantomData)
    }
}

impl<Idx: EntityRef, T: Clone + Debug> EntityVec<Idx, T> {
    /// Add a new entity, returning its assigned index.
    pub fn push(&mut self, t: T) -> Idx {
        let idx = Idx::new(self.0.len());
        self.0.push(t);
        idx
    }

    /// Get the number of entities in this entity space.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Get an iterator over the index-space.
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = Idx> {
        (0..self.0.len()).map(|index| Idx::new(index))
    }

    /// Get an iterator over (borrows of) entity values.
    pub fn values(&self) -> impl DoubleEndedIterator<Item = &T> {
        self.0.iter()
    }

    /// Get an iterator over (mutable borrows of) entity values.
    pub fn values_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut T> {
        self.0.iter_mut()
    }

    /// Get an iterator over index, borrow-of-entity tuples.
    pub fn entries(&self) -> impl DoubleEndedIterator<Item = (Idx, &T)> {
        self.0
            .iter()
            .enumerate()
            .map(|(index, t)| (Idx::new(index), t))
    }

    /// Get an iterator over index, mutable-borrow-of-entity tuples.
    pub fn entries_mut(&mut self) -> impl Iterator<Item = (Idx, &mut T)> {
        self.0
            .iter_mut()
            .enumerate()
            .map(|(index, t)| (Idx::new(index), t))
    }

    /// Typesafe element access, returning `None` if `idx` is the
    /// invalid index.
    pub fn get(&self, idx: Idx) -> Option<&T> {
        self.0.get(idx.maybe_index()?)
    }

    /// Typesafe mutable element access, returning `None` if `idx` is
    /// the invalid index.
    pub fn get_mut(&mut self, idx: Idx) -> Option<&mut T> {
        self.0.get_mut(idx.maybe_index()?)
    }

    /// Convert this `EntityVec` into the underlying `Vec` and return
    /// it.
    pub fn into_vec(self) -> Vec<T> {
        self.0
    }
}

impl<Idx: EntityRef, T: Clone + Debug> Index<Idx> for EntityVec<Idx, T> {
    type Output = T;
    fn index(&self, idx: Idx) -> &T {
        &self.0[idx.index()]
    }
}

impl<Idx: EntityRef, T: Clone + Debug> IndexMut<Idx> for EntityVec<Idx, T> {
    fn index_mut(&mut self, idx: Idx) -> &mut T {
        &mut self.0[idx.index()]
    }
}

impl<Idx: EntityRef, T: Clone + Debug> IndexAlloc<Idx> for EntityVec<Idx, T> {
    fn alloc(&mut self, a: Self::Output) -> Idx {
        self.push(a)
    }
}
impl<Idx: EntityRef, T: Clone + Debug> IndexIter<Idx> for EntityVec<Idx, T> {
    fn iter(&self) -> Box<dyn Iterator<Item = Idx> + '_> {
        Box::new(self.iter())
    }
}

#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
/// Vector of state per entity in an index-space that does *not*
/// define the index-space. In other words, this container will not
/// pass out new indices, it will only allow associating state with
/// existing indices; and it requires a default value for data at an
/// index not yet assigned.

pub struct PerEntity<Idx: EntityRef, T: Clone + Debug + Default>(Vec<T>, PhantomData<Idx>, T);

impl<Idx: EntityRef, T: Clone + Debug + Default> Index<Idx> for PerEntity<Idx, T> {
    type Output = T;
    fn index(&self, idx: Idx) -> &T {
        debug_assert!(idx.is_valid());
        self.0.get(idx.index()).unwrap_or(&self.2)
    }
}

impl<Idx: EntityRef, T: Clone + Debug + Default> IndexMut<Idx> for PerEntity<Idx, T> {
    fn index_mut(&mut self, idx: Idx) -> &mut T {
        debug_assert!(idx.is_valid());
        if idx.index() >= self.0.len() {
            self.0.resize(idx.index() + 1, T::default());
        }
        &mut self.0[idx.index()]
    }
}

impl<Idx: EntityRef, T: Clone + Debug + Default + PartialEq> PartialEq for PerEntity<Idx, T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl<Idx: EntityRef, T: Clone + Debug + Default + PartialEq + Eq> Eq for PerEntity<Idx, T> {}

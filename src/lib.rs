#![cfg_attr(not(feature = "std"), no_std)]
#![feature(try_trait_v2)]

mod try_trait;

use self::TieredResult::*;
use core::{convert::Infallible, fmt::Debug, ops::Deref};
use nullable_result::NullableResult;

pub trait ErrorHandler<E, F, C = ()> {
    fn handle_error(&mut self, error: E) -> ClientResponse<F, C>;
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
#[must_use]
pub enum TieredResult<T, E, F> {
    Ok(T),
    Err(E),
    Null,
    Fatal(F),
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
#[must_use]
pub enum FatalResult<T, F> {
    Ok(T),
    Null,
    Fatal(F),
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
#[must_use]
pub enum FatalOrOk<T, F> {
    Ok(T),
    Fatal(F),
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
#[must_use]
pub enum ClientResponse<F, C = ()> {
    Throw(F),
    Continue(C),
}

impl<T, E, F> Default for TieredResult<T, E, F> {
    fn default() -> Self {
        Null
    }
}

impl<T, E: Debug, F> TieredResult<T, E, F> {
    /// Panics if it's not `Ok`, otherwise returns the contained value.
    #[inline]
    #[track_caller]
    pub fn unwrap(self) -> T {
        match self {
            Ok(item) => item,
            Err(err) => panic!(
                "tried to unwrap a tiered result containing Err: {:?}",
                err
            ),
            Null => {
                panic!("tried to unwrap a tiered result containing `Null`")
            }
            Fatal(_) => {
                panic!("tried to unwrap a tiered result containing `Fatal`")
            }
        }
    }
}

impl<T: Default, E, F> TieredResult<T, E, F> {
    /// Returns the contained value if it's `Ok`, otherwise returns the default value
    /// for that type.
    #[inline]
    pub fn unwrap_or_default(self) -> T {
        match self {
            Ok(item) => item,
            _ => T::default(),
        }
    }
}

impl<T: Copy, E, F> TieredResult<&'_ T, E, F> {
    /// Returns a [`TieredResult`] with the [`Ok`] part copied.
    #[inline]
    pub fn copied(self) -> TieredResult<T, E, F> {
        self.map(|&item| item)
    }
}

impl<T: Copy, E, F> TieredResult<&'_ mut T, E, F> {
    /// Returns a [`TieredResult`] with the [`Ok`] part copied.
    #[inline]
    pub fn copied(self) -> TieredResult<T, E, F> {
        self.map(|&mut item| item)
    }
}

impl<T: Clone, E, F> TieredResult<&'_ T, E, F> {
    /// Returns a [`TieredResult`] with the [`Ok`] part cloned.
    #[inline]
    pub fn cloned(self) -> TieredResult<T, E, F> {
        self.map(|item| item.clone())
    }
}

impl<T: Clone, E, F> TieredResult<&'_ mut T, E, F> {
    /// Returns a [`NullableResult`] with the [`Ok`] part cloned.
    #[inline]
    pub fn cloned(self) -> TieredResult<T, E, F> {
        self.map(|item| item.clone())
    }
}

impl<T: Deref, E, F: Clone> TieredResult<T, E, F> {
    /// Coerce the [`Ok`] variant of the original result with [`Deref`] and returns the
    /// new [`TieredResult`]
    #[inline]
    pub fn as_deref(&self) -> TieredResult<&T::Target, &E, F> {
        match self {
            Ok(item) => Ok(item.deref()),
            Err(err) => Err(err),
            Null => Null,
            Fatal(fatality) => Fatal(fatality.clone()),
        }
    }
}

impl<T, E, F: Clone> TieredResult<T, E, F> {
    /// Convert from a `TieredResult<T, E, F>` or `&TieredResult<T, E, F>` to a
    /// `TieredResult<&T, &E, F>`.
    #[inline]
    pub fn as_ref(&self) -> TieredResult<&T, &E, F> {
        match self {
            Ok(item) => Ok(item),
            Err(err) => Err(err),
            Null => Null,
            Fatal(fatality) => Fatal(fatality.clone()),
        }
    }

    /// Convert from a `mut TieredResult<T, E, F>` or `&mut NullableResult<T, E, F>` to a
    /// `TieredResult<&mut T, &mut E, F>`.
    #[inline]
    pub fn as_mut(&mut self) -> TieredResult<&mut T, &mut E, F> {
        match self {
            Ok(item) => Ok(item),
            Err(err) => Err(err),
            Null => Null,
            Fatal(fatality) => Fatal(fatality.clone()),
        }
    }
}

impl<T, E, F> TieredResult<T, E, F> {
    /// Returns `true` if this result is an [`Ok`] value
    #[inline]
    #[must_use]
    pub fn is_ok(&self) -> bool {
        matches!(self, Ok(_))
    }

    /// Returns `true` if this result is an [`Err`] value
    #[inline]
    #[must_use]
    pub fn is_err(&self) -> bool {
        matches!(self, Err(_))
    }

    /// Returns `true` if this result is a [`Null`] value
    #[inline]
    #[must_use]
    pub fn is_null(&self) -> bool {
        matches!(self, Null)
    }

    /// Returns `true` if this result is [`Fatal`] value
    #[inline]
    #[must_use]
    pub fn is_fatal(&self) -> bool {
        matches!(&self, Fatal(_))
    }

    /// Returns the contained [`Ok`] value, consuming `self`.
    ///
    /// # Panics
    /// Panics if the value is not [`Ok`] with the provided message.
    #[inline]
    #[track_caller]
    pub fn expect(self, msg: &str) -> T {
        match self {
            Ok(item) => item,
            _ => panic!("{}", msg),
        }
    }

    /// Returns the contained value if it's [`Ok`], returns `item` otherwise.
    #[inline]
    pub fn unwrap_or(self, item: T) -> T {
        match self {
            Ok(item) => item,
            _ => item,
        }
    }

    /// Returns the contained value if it's [`Ok`], otherwise, it calls `f` and forwards
    /// its return value.
    #[inline]
    pub fn unwrap_or_else<Func: FnOnce() -> T>(self, f: Func) -> T {
        match self {
            Ok(item) => item,
            _ => f(),
        }
    }

    #[inline]
    pub fn recover_as_null(self) -> NullableResult<T, E> {
        self.optional_nullable_result()
            .unwrap_or(NullableResult::Null)
    }

    #[inline]
    pub fn recover_as_err(self, err: E) -> NullableResult<T, E> {
        self.optional_nullable_result()
            .unwrap_or(NullableResult::Err(err))
    }

    #[inline]
    pub fn recover_as_err_with<Func: FnOnce() -> E>(
        self,
        f: Func,
    ) -> NullableResult<T, E> {
        self.optional_nullable_result()
            .unwrap_or_else(|| NullableResult::Err(f()))
    }

    #[inline]
    fn optional_nullable_result(self) -> Option<NullableResult<T, E>> {
        match self {
            Ok(item) => Some(NullableResult::Ok(item)),
            Err(err) => Some(NullableResult::Err(err)),
            Null => Some(NullableResult::Null),
            Fatal(_) => None,
        }
    }

    /// Maps to a [`TieredResult`] with a different ok type.
    #[inline]
    pub fn map<U, Func: FnOnce(T) -> U>(
        self,
        f: Func,
    ) -> TieredResult<U, E, F> {
        match self {
            Ok(item) => Ok(f(item)),
            Err(err) => Err(err),
            Null => Null,
            Fatal(fatality) => Fatal(fatality),
        }
    }

    /// Maps to a [`TieredResult`] with a different err type.
    #[inline]
    pub fn map_err<U, Func: FnOnce(E) -> U>(
        self,
        f: Func,
    ) -> TieredResult<T, U, F> {
        match self {
            Ok(item) => Ok(item),
            Err(err) => Err(f(err)),
            Null => Null,
            Fatal(fatality) => Fatal(fatality),
        }
    }

    /// Maps to a [`TieredResult`] with a different fatality type.
    #[inline]
    pub fn map_fatal<U, Func: FnOnce(F) -> U>(
        self,
        f: Func,
    ) -> TieredResult<T, E, U> {
        match self {
            Ok(item) => Ok(item),
            Err(err) => Err(err),
            Null => Null,
            Fatal(fatality) => Fatal(f(fatality)),
        }
    }

    /// If `self` is [`Ok`], returns `res`, keeps the value of `self` otherwise.
    #[inline]
    pub fn and<U>(self, res: TieredResult<U, E, F>) -> TieredResult<U, E, F> {
        match self {
            Ok(_) => res,
            Err(err) => Err(err),
            Null => Null,
            Fatal(fatality) => Fatal(fatality),
        }
    }

    /// Calls `op` if the result is [`Ok`], otherwise returns the value of `self`.
    #[inline]
    pub fn and_then<U, Func>(self, op: Func) -> TieredResult<U, E, F>
    where
        Func: FnOnce(T) -> TieredResult<U, E, F>,
    {
        match self {
            Ok(item) => op(item),
            Err(err) => Err(err),
            Null => Null,
            Fatal(fatality) => Fatal(fatality),
        }
    }
}

impl<T, E, F> TieredResult<TieredResult<T, E, F>, E, F> {
    /// Convert from `TieredResult<TieredResult<T, E>, E>` to
    /// `TieredResult<T, E>`.
    #[inline]
    pub fn flatten(self) -> TieredResult<T, E, F> {
        match self {
            Ok(Ok(item)) => Ok(item),
            Ok(Err(err)) | Err(err) => Err(err),
            Ok(Null) | Null => Null,
            Ok(Fatal(fatality)) | Fatal(fatality) => Fatal(fatality),
        }
    }
}

/// Analogue of [TryFrom] that returns a [`TieredResult`]
pub trait TryFromFatal<T>: Sized {
    /// The type that is returned if conversion fails
    type Error;

    /// The type that is returned if conversion fails fatally
    type Fatality;

    /// Convert a `T` to [`TieredResult<Self, Self::Error, Self::Fatality>`]
    fn try_from_fatal(
        item: T,
    ) -> TieredResult<Self, Self::Error, Self::Fatality>;
}

/// Analogue of [TryInto] that returns a [`TieredResult`]
pub trait TryIntoFatal<T>: Sized {
    /// The type that is returned if conversion fails
    type Error;

    /// The type that is returned if conversion fails fatally
    type Fatality;

    /// Convert a `Self` to [`TieredResult<T, Self::Error, Self::Fatality>`]
    fn try_into_fatal(self) -> TieredResult<T, Self::Error, Self::Fatality>;
}

impl<T, U: nullable_result::MaybeTryFrom<T>> TryFromFatal<T> for U {
    type Error = U::Error;
    type Fatality = Infallible;

    #[inline]
    fn try_from_fatal(
        item: T,
    ) -> TieredResult<Self, Self::Error, Self::Fatality> {
        Ok(U::maybe_try_from(item)?)
    }
}

impl<T, U: TryFromFatal<T>> TryIntoFatal<U> for T {
    type Error = U::Error;
    type Fatality = U::Fatality;

    #[inline]
    fn try_into_fatal(self) -> TieredResult<U, Self::Error, Self::Fatality> {
        U::try_from_fatal(self)
    }
}

impl<T, F> FatalOrOk<T, F> {
    #[inline]
    #[track_caller]
    pub fn unwrap(self) -> T {
        use FatalOrOk::*;

        match self {
            Ok(item) => item,
            Fatal(_) => {
                panic!("tried to unwrap a tiered result containing `Fatal`")
            }
        }
    }
}

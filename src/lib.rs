//! This crate is an alternate strategy for error handling for libraries.
//!
//! Public functions that might want to keep trying in case of error, or report
//! multiple errors can take an additional parameter `&mut dyn ErrorHandler`. When
//! they encounter an error that they can sort-of recover from, they can invoke the
//! error handler (which calls back into the library user's code) and the error
//! handler gets to decide if the function should keep going or stop early.
//!
//! When the error handler says to return early, this is considered a fatal error
//! and all further processing and recovery should stop, and the library should
//! return control to the caller as quickly as possibly.
//!
//! If the error handler says to continue but the error does not allow the
//! calculation to finish, it should return null. This leads to the four variants in
//! a [`TieredResult`]: [`Ok`], [`Err`], [`Null`], and [`Fatal`].
//!
//! Your library code might look something like this:
//! ```rust
//! use tiered_result::TieredResult;
//! use std::fmt::{Display, Formatter};
//! pub use tiered_result::{ErrorHandler, ClientResponse};
//! use nullable_result::NullableResult;
//!
//! pub fn public_fn(handler: &mut dyn ErrorHandler<Error, Fatality>) -> Option<i64> {
//!     match private_fn(handler) {
//!         TieredResult::Ok(n) => Some(i64::from(n)),
//!         TieredResult::Err(_) => Some(-1),
//!         TieredResult::Null => None,
//!         TieredResult::Fatal(_) => Some(-2)
//!     }
//! }
//!
//! fn private_fn(handler: &mut dyn ErrorHandler<Error, Fatality>) -> TieredResult<u32, Error, Fatality> {//!
//!     let n = another_private_fn(handler)?; // <-- this `?` bubbles up the fatal error
//!                                           //     leaving a nullable result behind
//!     let n = n?; // <-- this `?` bubbles up the null/err.
//!     // the previous two lines could be written as let n = another_private_fn(handler)??;
//!
//!     if n == 42 {
//!         handler.handle_error(Error("we don't like 42".to_owned()))?;
//!     }
//!     TieredResult::Ok(n + 5)
//! }
//!
//! fn another_private_fn(handler: &mut dyn ErrorHandler<Error, Fatality>) -> TieredResult<u32, Error, Fatality> {
//!     // --snip--
//!     # TieredResult::Ok(2)
//! }
//!
//! // a struct to represent fatal errors, can carry additional info if you need it to
//! struct Fatality;
//!
//! #[derive(Clone, Debug)]
//! struct Error(String); // any old error type
//!
//! impl std::error::Error for Error {}
//! impl Display for Error {
//!     fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
//!        write!(f, "There was an error: {}", self.0)
//!     }
//! }
//! ```
//!
//! The calling application might look like this:
//! ```rust
//! # mod the_lib_from_before {
//! #     pub use tiered_result::{ErrorHandler, ClientResponse};
//! #     pub struct Error;
//! #     pub struct Fatality;
//! #     pub fn public_fn(handler: &mut dyn ErrorHandler<Error, Fatality>) -> Option<i64> {
//! #         Some(5)
//! #     }
//! # }
//! use the_lib_from_before::*;
//!
//! #[derive(Default)]
//! struct Handler(u8);
//!
//! impl ErrorHandler<Error, Fatality> for Handler {
//!     fn handle_error(&mut self, error: Error) -> ClientResponse<Fatality, ()> {
//!         if self.0 > 2 { // allow two errors before giving up
//!             ClientResponse::Throw(Fatality)
//!         } else {
//!             ClientResponse::Continue(())
//!         }
//!     }
//! }
//!
//! let mut handler = Handler::default();
//! println!("{:?}", public_fn(&mut handler));
//! ```
#![cfg_attr(not(feature = "std"), no_std)]
#![feature(try_trait_v2)]
#![warn(missing_docs)]

mod try_trait;

use self::TieredResult::*;
use core::{convert::Infallible, fmt::Debug, ops::Deref};
use nullable_result::NullableResult;

/// This trait should be part of your public API so that your users can implement
/// it for their own types.
pub trait ErrorHandler<E, F, C = ()> {
    /// Take an error and decide if the library should continue without the result
    /// that was supposed to have been produced.
    fn handle_error(&mut self, error: E) -> ClientResponse<F, C>;
}

/// A result type to be used internally by your library.
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
#[must_use]
pub enum TieredResult<T, E, F> {
    /// Equivalent to [`Result::Ok`] or [`NullableResult::Ok`]
    Ok(T),

    /// Equivalent to [`Result::Err`] or [`NullableResult::Err`]
    Err(E),

    /// Equivalent to [`NullableResult::Null`]
    Null,

    /// This variant will be produced by the `?` operator a a [`ClientResponse`].
    /// It can be used to easily bubble up to your API boundary, then converted so
    /// something your users can handle.
    Fatal(F),
}

/// A result type to be used internally by your library.
///
/// This can be used when one of your functions doesn't produce any errors of its
/// own, but might need to bubble up a fatal error.
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
#[must_use]
pub enum FatalResult<T, F> {
    /// See [`TieredResult::Ok`]
    Ok(T),

    /// See [`TieredResult::Null`]
    Null,

    /// See [`TieredResult::Fatal`]
    Fatal(F),
}

/// A result type to be used internally by your library.
///
/// This can be used when one of your functions doesn't do any fallible operations
/// directly, but still needs to bubble a fatal error up from its callees.
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
#[must_use]
pub enum FatalOrOk<T, F> {
    /// See [`TieredResult::Ok`]
    Ok(T),

    /// See [`TieredResult::Fatal`]
    Fatal(F),
}

/// The return type of [`ErrorHandler::handle_error`]. This type (or a suitable alias)
/// should be part of your library's public interface. Additionally you may want to
/// provide methods or constants for your users' convenience.
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
#[must_use]
pub enum ClientResponse<F, C = ()> {
    /// Stop processing
    Throw(F),

    /// Try to continue
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

    /// Replace a fatal error with [`NullableResult::Null`]
    #[inline]
    pub fn recover_as_null(self) -> NullableResult<T, E> {
        self.optional_nullable_result()
            .unwrap_or(NullableResult::Null)
    }

    /// Replace a fatal error with the provided error
    #[inline]
    pub fn recover_as_err(self, err: E) -> NullableResult<T, E> {
        self.optional_nullable_result()
            .unwrap_or(NullableResult::Err(err))
    }

    /// Replace a fatal error with the error returned by the provided function.
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
    /// Return the contained item
    ///
    /// # Panics
    /// Panics if the value contains a fatal error.
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

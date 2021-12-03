use crate::{ClientResponse, FatalOrOk, FatalResult, TieredResult};
use core::{
    convert::Infallible,
    ops::{ControlFlow, FromResidual, Try},
};
use nullable_result::NullableResult;

pub struct Residual<F>(F);

impl<T, E, F> Try for TieredResult<T, E, F> {
    type Output = NullableResult<T, E>;
    type Residual = Residual<F>;

    fn from_output(output: Self::Output) -> Self {
        match output {
            NullableResult::Ok(item) => TieredResult::Ok(item),
            NullableResult::Err(err) => TieredResult::Err(err),
            NullableResult::Null => TieredResult::Null,
        }
    }

    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        use ControlFlow::*;
        use NullableResult::*;

        match self {
            TieredResult::Ok(item) => Continue(Ok(item)),
            TieredResult::Err(err) => Continue(Err(err)),
            TieredResult::Null => Continue(Null),
            TieredResult::Fatal(fatality) => Break(Residual(fatality)),
        }
    }
}

impl<T, E, F> FromResidual<Residual<F>> for TieredResult<T, E, F> {
    fn from_residual(residual: Residual<F>) -> Self {
        TieredResult::Fatal(residual.0)
    }
}

impl<T, E1, E2, F> FromResidual<NullableResult<Infallible, E1>>
    for TieredResult<T, E2, F>
where
    E1: Into<E2>,
{
    fn from_residual(residual: NullableResult<Infallible, E1>) -> Self {
        match residual {
            NullableResult::Ok(_) => unreachable!(),
            NullableResult::Err(err) => TieredResult::Err(err.into()),
            NullableResult::Null => TieredResult::Null,
        }
    }
}

impl<T, E1, E2, F> FromResidual<Result<Infallible, E1>>
    for TieredResult<T, E2, F>
where
    E1: Into<E2>,
{
    fn from_residual(residual: Result<Infallible, E1>) -> Self {
        match residual {
            Ok(_) => unreachable!(),
            Err(err) => TieredResult::Err(err.into()),
        }
    }
}

impl<T, E, F> FromResidual<Option<Infallible>> for TieredResult<T, E, F> {
    fn from_residual(_: Option<Infallible>) -> Self {
        TieredResult::Null
    }
}

impl<T, F> Try for FatalResult<T, F> {
    type Output = Option<T>;
    type Residual = Residual<F>;

    fn from_output(output: Self::Output) -> Self {
        match output {
            Some(value) => FatalResult::Ok(value),
            None => FatalResult::Null,
        }
    }

    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        use ControlFlow::*;

        match self {
            FatalResult::Ok(value) => Continue(Some(value)),
            FatalResult::Null => Continue(None),
            FatalResult::Fatal(fatality) => Break(Residual(fatality)),
        }
    }
}

impl<T, F> FromResidual<Residual<F>> for FatalResult<T, F> {
    fn from_residual(residual: Residual<F>) -> Self {
        FatalResult::Fatal(residual.0)
    }
}

impl<T, F> FromResidual<Option<Infallible>> for FatalResult<T, F> {
    fn from_residual(_: Option<Infallible>) -> Self {
        FatalResult::Null
    }
}

impl<T, F> Try for FatalOrOk<T, F> {
    type Output = T;
    type Residual = Residual<F>;

    fn from_output(output: Self::Output) -> Self {
        FatalOrOk::Ok(output)
    }

    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        use ControlFlow::*;

        match self {
            FatalOrOk::Ok(value) => Continue(value),
            FatalOrOk::Fatal(fatality) => Break(Residual(fatality)),
        }
    }
}

impl<T, F> FromResidual<Residual<F>> for FatalOrOk<T, F> {
    fn from_residual(residual: Residual<F>) -> Self {
        FatalOrOk::Fatal(residual.0)
    }
}

impl<F, C> Try for ClientResponse<F, C> {
    type Output = C;
    type Residual = Residual<F>;

    fn from_output(output: Self::Output) -> Self {
        ClientResponse::Continue(output)
    }

    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        use ControlFlow::*;

        match self {
            ClientResponse::Throw(err) => Break(Residual(err)),
            ClientResponse::Continue(continuation) => Continue(continuation),
        }
    }
}

impl<F, C> FromResidual<Residual<F>> for ClientResponse<F, C> {
    fn from_residual(residual: Residual<F>) -> Self {
        ClientResponse::Throw(residual.0)
    }
}

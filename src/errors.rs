pub type ArcturusResult<T> = core::result::Result<T, ArcturusError>;

#[derive(Debug, PartialEq)]
pub enum ArcturusError {
    BadArg,
    InvalidDimensions,
    InvalidScalar,
    MintsAndSpendsImbalance,
    MissingOutputSet,
    Overflow,
    SpendNotFoundInRing,
    SetAlreadyLoaded,
    TooManySpends,
    TooShort,
    VerificationFailed,
}

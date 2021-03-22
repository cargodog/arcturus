pub type ArcturusResult<T> = core::result::Result<T, ArcturusError>;

#[derive(Debug, PartialEq)]
pub enum ArcturusError {
    BadArg,
    DuplicateBins,
    InvalidDimensions,
    InvalidScalar,
    MintsAndSpendsImbalance,
    MissingOutputSet,
    Overflow,
    SpendNotFoundInRing,
    SetAlreadyLoaded,
    TooFewBins,
    TooManyBins,
    TooManySpends,
    TooShort,
    Unimplemented,
    VerificationFailed,
}

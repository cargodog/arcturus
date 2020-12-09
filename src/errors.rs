pub type ArcturusResult<T> = core::result::Result<T, ArcturusError>;

#[derive(Debug, PartialEq)]
pub enum ArcturusError {
    BadArg,
    MintsAndSpendsImbalance,
    Overflow,
    ProofDigitsTooSmall,
    ProofNumSignersTooSmall,
    ProofNumSignersTooLarge,
    ProofRadixTooSmall,
    RingSizeTooSmall,
    RingSizeTooLarge,
    Unimplemented,
    VerificationFailed,
}

use core::cmp::PartialOrd;
use core::ops::{Div, Mul, Sub};
use curve25519_dalek::scalar::Scalar;

#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ScalarExp {
    x: Scalar,
    next_x: Scalar,
}

impl Iterator for ScalarExp {
    type Item = Scalar;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let x = self.next_x;
        self.next_x *= self.x;
        Some(x)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

pub fn exp_iter(x: Scalar) -> ScalarExp {
    let next_x = Scalar::one();
    ScalarExp { x, next_x }
}

#[derive(Clone, Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct SizedFlatten<I, U> {
    outer: I,
    inner: Option<U>,
}

impl<I, U> SizedFlatten<I, U>
where
    I: Iterator,
{
    pub fn new(iter: I) -> SizedFlatten<I, U> {
        SizedFlatten {
            outer: iter,
            inner: None,
        }
    }
}

impl<I, U> Iterator for SizedFlatten<I, U>
where
    I: Clone + Iterator,
    U: Clone + Iterator,
    I::Item: IntoIterator<IntoIter = U, Item = U::Item>,
{
    type Item = U::Item;

    #[inline]
    fn next(&mut self) -> Option<U::Item> {
        loop {
            if let Some(ref mut i) = self.inner {
                match i.next() {
                    None => self.inner = None,
                    v @ Some(_) => return v,
                }
            }
            match self.outer.next() {
                None => return None,
                Some(i) => self.inner = Some(i.into_iter()),
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (mut lo, mut hi) = self.inner.as_ref().map_or((0, Some(0)), U::size_hint);
        for (l, h) in self.outer.clone().map(|i| i.into_iter().size_hint()) {
            lo += l;
            if let Some(sum) = hi {
                hi = match h {
                    Some(val) => Some(sum + val),
                    None => None,
                };
            }
        }
        (lo, hi)
    }
}

pub fn sized_flatten<I: Iterator, U>(iter: I) -> SizedFlatten<I, U> {
    SizedFlatten::new(iter)
}

pub struct RadixDecomposer<T> {
    radix: T,
    quotient: T,
}

impl<T> RadixDecomposer<T> {
    pub fn new(num: T, radix: T) -> RadixDecomposer<T> {
        RadixDecomposer {
            radix: radix,
            quotient: num,
        }
    }
}

impl<T> Iterator for RadixDecomposer<T>
where
    T: Copy + Div<Output = T> + Mul<Output = T> + PartialOrd + Sub<Output = T>,
{
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let q = self.quotient / self.radix;
        let r = self.quotient - (self.radix * q);
        self.quotient = q;
        Some(r)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[cfg(not(feature = "std"))]
    use alloc::vec::Vec;
    #[cfg(feature = "std")]
    use std::vec::Vec;

    #[test]
    fn scalar_exp() {
        let mut test_rng = rand::thread_rng();
        let seed = Scalar::random(&mut test_rng);
        let mut running_prod = Scalar::one();

        // Test iterator values
        for exp in exp_iter(seed).take(25) {
            assert_eq!(running_prod, exp);
            running_prod *= seed;
        }

        // Test size_hint()
        assert_eq!((usize::max_value(), None), exp_iter(seed).size_hint());
    }

    #[test]
    fn sized_flatten() {
        let nested = (0..5)
            .map(|i| (0..2).map(|j| 2 * i + j).collect())
            .collect::<Vec<Vec<_>>>();

        // Test iterator values
        for (k, val) in SizedFlatten::new(nested.iter()).enumerate() {
            assert_eq!(&k, val);
        }

        // Test size_hint()
        assert_eq!((10, Some(10)), SizedFlatten::new(nested.iter()).size_hint());
    }

    struct RadixDecomposeTest {
        num: usize,
        radix: usize,
        decomposed: [usize; 12],
    }
    const RADIX_DECOMPOSE_TESTS: [RadixDecomposeTest; 8] = [
        RadixDecomposeTest {
            num: 131,
            radix: 2,
            decomposed: [1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
        },
        RadixDecomposeTest {
            num: 131,
            radix: 8,
            decomposed: [3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        },
        RadixDecomposeTest {
            num: 131,
            radix: 10,
            decomposed: [1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        },
        RadixDecomposeTest {
            num: 131,
            radix: 16,
            decomposed: [3, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        },
        RadixDecomposeTest {
            num: 3819,
            radix: 2,
            decomposed: [1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1],
        },
        RadixDecomposeTest {
            num: 3819,
            radix: 8,
            decomposed: [3, 5, 3, 7, 0, 0, 0, 0, 0, 0, 0, 0],
        },
        RadixDecomposeTest {
            num: 3819,
            radix: 10,
            decomposed: [9, 1, 8, 3, 0, 0, 0, 0, 0, 0, 0, 0],
        },
        RadixDecomposeTest {
            num: 3819,
            radix: 16,
            decomposed: [11, 14, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        },
    ];

    #[test]
    fn radix_decomposer() {
        for test in &RADIX_DECOMPOSE_TESTS {
            assert_eq!(
                &test.decomposed,
                &RadixDecomposer::new(test.num, test.radix)
                    .take(12)
                    .collect::<Vec<usize>>()[..]
            );
        }
    }
}

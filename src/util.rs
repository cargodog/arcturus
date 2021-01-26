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

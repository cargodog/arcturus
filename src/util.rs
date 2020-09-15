use curve25519_dalek::scalar::Scalar;

#[derive(Clone)]
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

#[derive(Clone)]
pub struct TellSize<I> {
    size: usize,
    iter: I,
}

pub trait IntoTellSize {
    #[inline]
    fn tell_size(self, size: usize) -> TellSize<Self>
    where
        Self: Sized + Iterator,
    {
        TellSize { iter: self, size }
    }
}

impl<I: ?Sized> IntoTellSize for I where I: Iterator {}

impl<I> Iterator for TellSize<I>
where
    I: Iterator,
{
    type Item = I::Item;

    #[inline]
    fn next(&mut self) -> Option<I::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }
}

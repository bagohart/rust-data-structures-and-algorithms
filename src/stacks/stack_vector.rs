struct StackVector<T> {
    data: Vec<T>,
}

pub struct IntoIter<T>(StackVector<T>);

pub struct Iter<'a, T> {
    data: &'a Vec<T>,
    current: Option<usize>,
}

pub struct IterMut<'a, T> {
    slice: &'a mut [T],
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        // this doesn't work, it seems that this would lead to a double mutable reference in self.slice and head/tail.
        // not sure, why the ref here isn't consumed!
        // let (head, tail) = self.slice.split_first_mut()?;

        let sl = std::mem::replace(&mut self.slice, &mut []);
        let (head, tail) = sl.split_last_mut()?;

        self.slice = tail;
        Some(head)
    }
}

impl<T> StackVector<T> {
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            slice: &mut self.data[..],
        }
    }

    pub fn new() -> Self {
        StackVector { data: Vec::new() }
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn push(&mut self, elem: T) {
        self.data.push(elem);
    }

    pub fn pop(&mut self) -> Option<T> {
        let elem = self.data.pop();
        if self.data.capacity() > 2 * self.data.len() {
            // Only shrink the capacity if the stack has significantly more space than is currently necessary
            // This optimization is probably bogus though.
            self.data.shrink_to_fit();
        }
        elem
    }

    pub fn peek(&self) -> Option<&T> {
        self.data.last()
    }

    pub fn peek_mut(&mut self) -> Option<&mut T> {
        self.data.last_mut()
    }

    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter(self)
    }

    pub fn iter<'b>(&'b self) -> Iter<'b, T> {
        Iter {
            data: &self.data,
            current: Some(self.data.len() - 1),
        }
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.data.pop()
    }
}

// I could probably delegate to Vec's iterator + reverse, but this way it's more fun u_U
// The same approach CANNOT work for IterMut! Otherwise, there would be 2
// mutable references on the Vector!
// see "how to implement a safe mutable iterator for vec on the mailing list
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        match self.current {
            Some(index) => {
                let elem = &self.data[index];
                if index == 0 {
                    self.current = None;
                } else {
                    self.current = self.current.map(|i| i - 1);
                }
                Some(elem)
            }
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::StackVector;

    #[test]
    fn basics() {
        let mut s: StackVector<i32> = StackVector::new();
        s.push(1);
        s.push(2);
        s.push(3);
        assert_eq!(s.peek(), Some(&3));
        let top = s.peek_mut().unwrap();
        assert_eq!(top, &3);
        *top = 8;
        assert_eq!(s.peek(), Some(&8));

        assert_eq!(s.pop(), Some(8));
        assert_eq!(s.pop(), Some(2));
        assert_eq!(s.pop(), Some(1));
        assert_eq!(s.pop(), None);

        let mut s: StackVector<i32> = StackVector::new();
        s.push(1);
        s.push(2);
        s.push(3);
        let mut i = s.into_iter();
        assert_eq!(i.next(), Some(3));
        assert_eq!(i.next(), Some(2));
        assert_eq!(i.next(), Some(1));
        assert_eq!(i.next(), None);

        let mut s: StackVector<i32> = StackVector::new();
        s.push(1);
        s.push(2);
        s.push(3);
        let mut i = s.iter();
        assert_eq!(i.next(), Some(&3));
        assert_eq!(i.next(), Some(&2));
        assert_eq!(i.next(), Some(&1));
        assert_eq!(i.next(), None);

        let mut i = s.iter_mut();
        let x = i.next();
        *x.unwrap() = 9;
        let x = i.next();
        *x.unwrap() = 8;
        let x = i.next();
        *x.unwrap() = 7;
        let x = i.next();
        assert_eq!(x, None);

        let mut i = s.into_iter();
        assert_eq!(i.next(), Some(9));
        assert_eq!(i.next(), Some(8));
        assert_eq!(i.next(), Some(7));
        // assert_eq!(i.next(), Some(7));
        // assert_eq!(i.next(), Some(8));
        // assert_eq!(i.next(), Some(9));
        assert_eq!(i.next(), None);
    }
}


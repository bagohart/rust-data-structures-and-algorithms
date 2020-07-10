use std::collections::vec_deque;
use std::collections::VecDeque;
use std::iter::Rev;

struct QueueVector<T> {
    data: VecDeque<T>,
}

impl<T> QueueVector<T> {
    pub fn new() -> Self {
        QueueVector {
            data: VecDeque::new(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
    pub fn enqueue(&mut self, elem: T) {
        self.data.push_front(elem)
    }
    pub fn dequeue(&mut self) -> Option<T> {
        self.data.pop_back()
    }
    pub fn peek(&self)->Option<&T>{
        self.data.back()
    }

    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter { queue: self }
    }

    fn iter(&self) -> Iter<T> {
        Iter {
            it: self.data.iter().rev(),
        }
    }

    fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            it: self.data.iter_mut().rev(),
        }
    }
}

pub struct IntoIter<T> {
    queue: QueueVector<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.queue.dequeue()
    }
}

pub struct Iter<'a, T> {
    it: Rev<vec_deque::Iter<'a, T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.it.next()
    }
}

pub struct IterMut<'a, T> {
    it: Rev<vec_deque::IterMut<'a, T>>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;
    fn next(&mut self) -> Option<Self::Item> {
        self.it.next()
    }
}

#[cfg(test)]
mod tests {
    use super::QueueVector;

    #[test]
    fn basics() {
        let mut q = QueueVector::new();
        q.enqueue(1);
        q.enqueue(2);
        q.enqueue(3);
        assert_eq!(q.is_empty(), false);
        assert_eq!(q.peek(), Some(&1));
        assert_eq!(q.dequeue(), Some(1));
        assert_eq!(q.dequeue(), Some(2));
        assert_eq!(q.dequeue(), Some(3));
        assert_eq!(q.dequeue(), None);
        assert_eq!(q.is_empty(), true);

        let mut q = QueueVector::new();
        q.enqueue(1);
        q.enqueue(2);
        q.enqueue(3);
        let mut i = q.into_iter();
        assert_eq!(i.next(), Some(1));
        assert_eq!(i.next(), Some(2));
        assert_eq!(i.next(), Some(3));

        let mut q = QueueVector::new();
        q.enqueue(1);
        q.enqueue(2);
        q.enqueue(3);
        let mut i = q.iter();
        assert_eq!(i.next(), Some(&1));
        assert_eq!(i.next(), Some(&2));
        assert_eq!(i.next(), Some(&3));
        let mut i = q.iter_mut();
        let f = i.next();
        assert_eq!(f, Some(&mut 1));
        *f.unwrap() = 8;
        assert_eq!(i.next(), Some(&mut 2));
        assert_eq!(i.next(), Some(&mut 3));
        assert_eq!(q.dequeue(), Some(8));
    }
}

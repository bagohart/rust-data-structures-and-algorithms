use std::fmt;
use std::fmt::Debug;
use std::fmt::Display;
// a binary max heap, embedded in an array

#[derive(Debug)]
struct BinaryHeap<T>
where
    T: Ord,
{
    data: Vec<T>,
}

pub struct IntoIter<T>(std::vec::IntoIter<T>);
impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

pub struct Iter<'heap, T>(std::slice::Iter<'heap, T>);
impl<'heap, T> Iterator for Iter<'heap, T> {
    type Item = &'heap T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

pub struct IterMut<'heap, T>(std::slice::IterMut<'heap, T>);

impl<T: Ord + Display + Debug> BinaryHeap<T> {
    pub fn assert_ok(&self) {
        for (index, elem) in self.data.iter().enumerate() {
            let left_child_index = 2 * index + 1;
            let right_child_index = 2 * index + 2;
            if left_child_index < self.data.len() {
                assert!(
                    elem >= &self.data[left_child_index],
                    "heap broken: {} >= {} in heap {}",
                    elem,
                    self.data[left_child_index],
                    self.to_string()
                );
            }
            if right_child_index < self.data.len() {
                assert!(
                    elem >= &self.data[right_child_index],
                    "heap broken: {} >= {} in heap {}",
                    elem,
                    self.data[right_child_index],
                    self.to_string()
                );
            }
        }
    }
    pub fn new() -> Self {
        BinaryHeap { data: Vec::new() }
    }

    pub fn from_vec(mut vec: Vec<T>) -> Self {
        println!("unsorted vec is {:?}", vec);
        for i in (0..vec.len() / 2).rev() {
            BinaryHeap::heapify(&mut vec[..], i);
        }
        let res = BinaryHeap { data: vec };
        res.assert_ok();
        res
    }

    pub fn delete_root(&mut self) -> Option<T> {
        self.assert_ok();
        match self.data.len() {
            0 => None,
            1 => self.data.pop(),
            _ => {
                let last = self.data.pop().unwrap();
                let res = std::mem::replace(&mut self.data[0], last);
                BinaryHeap::heapify(&mut self.data[..], 0); // restore order
                self.assert_ok();
                Some(res)
            }
        }
    }

    // deletes and returns the first equal element
    pub fn delete_elem(&mut self, elem: &T) -> Option<T> {
        self.assert_ok();
        let index = self.data.iter().position(|x| x == elem);
        // I cannot compute the last index here, because overflow o_O
        let len = self.data.len();
        match index {
            None => None,
            Some(0) => self.delete_root(),
            Some(index) if index == len - 1 => self.data.pop(),
            Some(index) => {
                self.data.swap(index, len - 1);
                let res = self.data.pop();
                BinaryHeap::heapify(&mut self.data[..], index);
                self.assert_ok();
                res
            }
        }
    }

    // assume that the left and right subtrees of the root are already max heaps.
    // the first element then 'sinks' into the heap as deep as necessary by swapping
    // the element with its biggest child
    fn heapify(slice: &mut [T], mut pos: usize) {
        println!("start heapify on slice {:?} starting at {:?}", slice, pos);
        let mut next = 2 * pos + 1; // left child
        while
        // there is a left child
        next < slice.len() {
            // check right child (does not necessarily exist, even if left child does)
            if next + 1 < slice.len() && slice[next + 1] > slice[next] {
                next += 1;
            }
            if slice[pos] >= slice[next] {
                break;
            }
            println!("swap {} and {}", slice[pos], slice[next]);
            slice.swap(pos, next);
            pos = next;
            next = 2 * pos + 1;
        }
        println!("heapify complete: {:?}", slice);
    }
    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter(self.data.into_iter())
    }
    pub fn iter(&self) -> Iter<T> {
        Iter(self.data.iter())
    }
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut(self.data.iter_mut())
    }
    // allows duplicate keys, always succeeds
    pub fn insert(&mut self, elem: T) {
        // element bubbles up as long as necessary
        self.assert_ok();
        self.data.push(elem);
        let mut pos = self.data.len() - 1;
        while pos > 0 {
            let parent = (pos - 1) / 2;
            if self.data[parent] > self.data[pos] {
                break;
            }
            self.data.swap(parent, pos);
            pos = parent;
        }
        self.assert_ok();
    }
}

impl<T: Display + Ord + Debug> Display for BinaryHeap<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.data)
    }
}

#[cfg(test)]
mod tests {
    use super::BinaryHeap;

    #[test]
    fn build_from_vec() {
        let vec = vec![1, 4, 8, 2, 7, 4, 9, 20, 137, 50, 8643, 82, 13, 17, 5];
        let heap = BinaryHeap::from_vec(vec);
        heap.assert_ok();
    }

    #[test]
    fn delete_elem() {
        let mut heap = BinaryHeap::new();
        heap.insert(5);
        heap.insert(3);
        heap.insert(5);
        heap.insert(4);
        heap.insert(13);
        heap.insert(7);
        heap.insert(20);
        heap.insert(50);
        heap.insert(1);
        heap.insert(2);
        heap.insert(12);
        heap.insert(17);

        let x = heap.delete_elem(&5);
        assert!(x.is_some());
        let x = heap.delete_elem(&3);
        assert!(x.is_some());
        let x = heap.delete_elem(&5);
        assert!(x.is_some());
        let x = heap.delete_elem(&4);
        assert!(x.is_some());
        let x = heap.delete_elem(&13);
        assert!(x.is_some());
        let x = heap.delete_elem(&7);
        assert!(x.is_some());
        let x = heap.delete_elem(&20);
        assert!(x.is_some());
        let x = heap.delete_elem(&50);
        assert!(x.is_some());
        let x = heap.delete_elem(&1);
        assert!(x.is_some());
        let x = heap.delete_elem(&2);
        assert!(x.is_some());
        let x = heap.delete_elem(&12);
        assert!(x.is_some());
        let x = heap.delete_elem(&17);
        assert!(x.is_some());
        let x = heap.delete_elem(&17);
        assert!(x.is_none());
    }

    #[test]
    fn delete_root() {
        let mut heap = BinaryHeap::new();
        heap.insert(5);
        heap.insert(3);
        heap.insert(5);
        heap.insert(4);
        heap.insert(13);
        heap.insert(7);
        heap.insert(20);
        heap.insert(50);
        heap.insert(1);
        heap.insert(2);
        heap.insert(12);
        heap.insert(17);
        heap.assert_ok();
        heap.delete_root();
        heap.delete_root();
        heap.delete_root();
        heap.delete_root();
        heap.delete_root();
        heap.delete_root();
        heap.delete_root();
        heap.delete_root();
        heap.delete_root();
        heap.delete_root();
        heap.delete_root();
        heap.delete_root();
        heap.delete_root();
        heap.delete_root();
        heap.delete_root();
        heap.delete_root();
        heap.assert_ok();
    }

    #[test]
    fn insert() {
        let mut heap = BinaryHeap::new();
        heap.insert(5);
        heap.insert(3);
        heap.insert(5);
        heap.insert(4);
        heap.insert(13);
        heap.insert(7);
        heap.insert(20);
        heap.insert(50);
        heap.insert(1);
        heap.insert(2);
        heap.insert(12);
        heap.insert(17);
        heap.assert_ok();
        assert_eq!(
            heap.to_string(),
            "[50, 20, 17, 5, 12, 13, 7, 3, 1, 2, 4, 5]"
        );
    }
}

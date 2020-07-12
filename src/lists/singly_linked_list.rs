type Link<T> = Option<Box<Node<T>>>;

struct Node<T> {
    elem: T,
    next: Link<T>,
}

pub struct SinglyLinkedList<T> {
    head: Link<T>,
}

impl<T> SinglyLinkedList<T> {
    // mostly from LRWETMLL
    pub fn new() -> Self {
        SinglyLinkedList { head: None }
    }

    pub fn push_front(&mut self, elem: T) {
        let new_node = Box::new(Node {
            elem: elem,
            next: self.head.take(),
        });
        self.head = Some(new_node);
    }

    pub fn pop_front(&mut self) -> Option<T> {
        let front_node = self.pop_front_node();
        front_node.map(|node| node.elem)
    }

    fn pop_front_node(&mut self) -> Link<T> {
        let head: Link<T> = self.head.take();
        head.map(|mut node| {
            // alternatively, we can move it out (partial move) and then overwrite it.
            // Rust is that clever already :)
            self.head = node.next.take();
            node
        })
    }

    pub fn peek_front(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.elem)
    }

    pub fn peek_front_mut(&mut self) -> Option<&mut T> {
        self.head.as_mut().map(|node| &mut node.elem)
    }

    // the following functions are actually new
    pub fn peek_back(&self) -> Option<&T> {
        self.last_node().map(|node| &node.elem)
    }

    pub fn peek_back_mut(&mut self) -> Option<&mut T> {
        self.last_node_mut().map(|node| &mut node.elem)
    }

    fn last_node_mut<'a>(&'a mut self) -> Option<&'a mut Node<T>> {
        // I couldn't get the same construction to work as for last_node because of lifetime issues.
        // Not sure if this is somehow possible.
        if self.head.is_none() {
            return None;
        }

        let mut node: &mut Node<T> = self.head.as_mut().unwrap();
        while node.next.is_some() {
            node = node.next.as_mut().unwrap();
        }
        Some(node)
    }

    fn last_node(&self) -> Option<&Node<T>> {
        self.head.as_ref().take().map(|head| {
            // todo: can I do |ref head| or something to dereference the box in the closure argument list?
            let mut node: &Node<T> = &*head;

            while let Some(next_node_box) = node.next.as_ref() {
                // what magic is this? why is the box casted to a reference implicitly? woah.
                node = next_node_box;
            }
            node

            // This works too:
            // while node.next.is_some() {
            //     node = &**node.next.as_ref().unwrap();
            // }
            // node
        })
    }

    pub fn push_back(&mut self, elem: T) {
        let new_node = Box::new(Node {
            elem: elem,
            next: None,
        });
        let last_node = self.last_node_mut();
        match last_node {
            None => self.head = Some(new_node),
            Some(last_node) => last_node.next = Some(new_node),
        }
    }

    fn pop_back_link(&mut self) -> Link<T> {
        if self.head.is_none() {
            return None;
        }

        let mut node_box_ref_mut: &mut Link<T> = &mut self.head;
        // todo: here is repetition. can this be expressed better?
        // ^ probably not. tried with loop, ran into temporary variables/ownership problems u_U
        while node_box_ref_mut.as_mut().unwrap().next.is_some() {
            node_box_ref_mut = &mut node_box_ref_mut.as_mut().unwrap().next;
        }
        node_box_ref_mut.take()
    }

    pub fn pop_back(&mut self) -> Option<T> {
        let last_link: Link<T> = self.pop_back_link();
        last_link.map(|link| link.elem)
    }
}

impl<T> Drop for SinglyLinkedList<T> {
    // Not necessary for memory correctness, but absolutely needed to prevent stack overflow
    fn drop(&mut self) {
        while let Some(_) = self.pop_front_node() {}
    }
}

pub struct IntoIter<T>(SinglyLinkedList<T>);

impl<T> SinglyLinkedList<T> {
    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter(self)
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop_front()
    }
}

pub struct Iter<'a, T> {
    next: Option<&'a Node<T>>,
}

impl<T> SinglyLinkedList<T> {
    pub fn iter(&self) -> Iter<T> {
        Iter {
            next: self.head.as_ref().map(|node| &**node),
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        // don't need to use take because shared references are Copy
        self.next.map(|node| {
            self.next = node.next.as_ref().map(|node| &**node);
            &node.elem
        })
    }
}

pub struct IterMut<'a, T> {
    next: Option<&'a mut Node<T>>,
}

impl<T> SinglyLinkedList<T> {
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            next: self.head.as_mut().map(|node| &mut **node),
        }
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;
    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().map(|node| {
            self.next = node.next.as_mut().map(|node| &mut **node);
            &mut node.elem
        })
    }
}

#[cfg(test)]
mod tests {
    use super::SinglyLinkedList;

    #[test]
    fn pop_back() {
        let mut list = SinglyLinkedList::new();
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        let last_elem = list.pop_back();
        assert_eq!(last_elem, Some(1));
        let last_elem = list.pop_back();
        assert_eq!(last_elem, Some(2));
        assert_eq!(list.pop_front(), Some(3));
        assert_eq!(list.pop_front(), None);
    }

    #[test]
    fn push_back() {
        let mut list = SinglyLinkedList::new();
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        list.push_back(4);
        assert_eq!(list.pop_front(), Some(3));
        assert_eq!(list.pop_front(), Some(2));
        assert_eq!(list.pop_front(), Some(1));
        assert_eq!(list.pop_front(), Some(4));
        assert_eq!(list.pop_front(), None);
    }

    #[test]
    fn peek_back() {
        let mut list = SinglyLinkedList::new();
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        let last_elem = list.peek_back();
        assert_eq!(last_elem, Some(&1));

        let mut last_elem_mut = list.peek_back_mut();
        last_elem_mut.as_mut().map(|n| **n = 8);
        assert_eq!(last_elem_mut, Some(&mut 8));
    }

    #[test]
    fn last_node_mut() {
        let mut list = SinglyLinkedList::new();
        let last_node = list.last_node();
        assert!(last_node.is_none());
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        let last_node = list.last_node_mut();
        last_node.map(|n| n.elem = 5);
        let last_node = list.last_node();
        assert_eq!(last_node.unwrap().elem, 5);
    }

    #[test]
    fn last_node() {
        let mut list = SinglyLinkedList::new();
        let last_node = list.last_node();
        assert!(last_node.is_none());
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        let last_node = list.last_node();
        assert_eq!(last_node.unwrap().elem, 1);
    }

    #[test]
    fn iter_mut() {
        let mut list = SinglyLinkedList::new();
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        let mut iter = list.iter_mut();
        assert_eq!(iter.next(), Some(&mut 3));
        assert_eq!(iter.next(), Some(&mut 2));
        assert_eq!(iter.next(), Some(&mut 1));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter() {
        let mut list = SinglyLinkedList::new();
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        let mut iter = list.iter();
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn into_iter() {
        let mut list = SinglyLinkedList::new();
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        let mut iter = list.into_iter();
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn basics() {
        let mut list = SinglyLinkedList::new();
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.peek_front(), None);

        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        assert_eq!(list.peek_front(), Some(&3));
        let x = list.peek_front_mut();
        x.map(|v| *v = 8);
        assert_eq!(list.peek_front(), Some(&8));
        assert_eq!(list.pop_front(), Some(8));
        assert_eq!(list.pop_front(), Some(2));

        list.push_front(4);
        list.push_front(5);
        assert_eq!(list.pop_front(), Some(5));
        assert_eq!(list.pop_front(), Some(4));
        assert_eq!(list.pop_front(), Some(1));
        assert_eq!(list.pop_front(), None);
    }
}

use std::fmt::Display;

// todo:
// merge (zip) <- via iterator ?

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

    pub fn clear(&mut self) {
        while let Some(_) = self.pop_front_node() {}
    }

    pub fn push_front(&mut self, elem: T) {
        // this could be written a bit shorter (and it was)
        // but I like it this way.
        let new_node = Box::new(Node {
            elem: elem,
            next: None,
        });
        self.push_single_front_node(new_node);
    }

    fn push_single_front_node(&mut self, mut node: Box<Node<T>>) {
        assert!(node.next.is_none());
        node.next = self.head.take();
        self.head = Some(node);
    }

    fn push_single_back_node(&mut self, node: Box<Node<T>>) {
        assert!(node.next.is_none());
        if self.head.is_none() {
            self.head = Some(node);
        } else {
            let last_node = self.last_node_mut().unwrap();
            last_node.next = Some(node);
        }
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

    // Returns a mutable link to this position. Works also for the link to the first index
    // after the list (then the Link is None), but not beyond that.
    fn link_to_pos_mut(&mut self, pos: usize) -> Option<&mut Link<T>> {
        let mut link: &mut Link<T> = &mut self.head;
        for _ in 0..pos {
            if link.is_none() {
                return None;
            }

            link = &mut link.as_mut().unwrap().next;
        }
        Some(link)
    }

    pub fn insert(&mut self, elem: T, pos: usize) -> Result<(), T> {
        let mut link_to_pos: Option<&mut Link<T>> = self.link_to_pos_mut(pos);
        if link_to_pos.is_none() {
            return Err(elem);
        }

        let link_to_next: Link<T> = link_to_pos.as_mut().unwrap().take();
        let new_node = Box::new(Node {
            elem: elem,
            next: link_to_next,
        });
        *link_to_pos.unwrap() = Some(new_node);

        Ok(())
    }

    pub fn insert_list(&mut self, mut other: Self, pos: usize) -> Result<(), Self> {
        if pos > self.length() || other.length() == 0 {
            return Err(other);
        }
        let mut link_to_right_part: Option<&mut Link<T>> = self.link_to_pos_mut(pos);
        // remove right part from list
        let right_part = link_to_right_part.as_mut().unwrap().take();
        // append right part to other list
        other.append(SinglyLinkedList { head: right_part });
        // append other list to left part of self
        *link_to_right_part.unwrap() = other.head.take();
        Ok(())

        // Alternatively: (simpler, but less efficient)
        // let right_part = self.split_off(pos);
        // other.append(right_part);
        // self.append(other);
    }

    fn length(&self) -> usize {
        self.iter().count()
    }

    // in case of error, returns the length of the list
    pub fn remove(&mut self, pos: usize) -> Result<(), usize> {
        let mut link_to_pos: Option<&mut Link<T>> = self.link_to_pos_mut(pos);
        // if link_to_pos.is_none() || link_to_pos.as_mut().unwrap().next.is_none() {
        if link_to_pos.is_none() || link_to_pos.as_mut().unwrap().is_none() {
            // this is inefficient: it could already be calculated by link_to_pos_mut() u_U
            let len = self.length();
            return Err(len);
        }

        let mut node_to_remove: Box<Node<T>> = link_to_pos.as_mut().unwrap().take().unwrap();
        *link_to_pos.unwrap() = node_to_remove.next.take();

        Ok(())
    }

    pub fn append(&mut self, mut other: Self) {
        match self.last_node_mut() {
            None => self.head = other.head.take(),
            Some(last_node) => last_node.next = other.head.take(),
        }
    }

    pub fn split_off(&mut self, pos: usize) -> Self {
        if pos >= self.length() {
            return SinglyLinkedList::new();
        }

        SinglyLinkedList {
            // this can't fail because of length-test above
            head: self.link_to_pos_mut(pos).unwrap().take(),
        }
    }

    // splits existing list in two. the second list includes the element at position pos
    pub fn split(mut self, pos: usize) -> (Self, Self) {
        if self.head.is_none() {
            return (Self::new(), Self::new());
        }

        match self.link_to_pos_mut(pos) {
            None => (self, Self::new()),
            Some(link_to_pos_mut) => {
                let link_to_right_part = link_to_pos_mut.take();
                (
                    self,
                    SinglyLinkedList {
                        head: link_to_right_part,
                    },
                )
            }
        }
    }

    // wow. this... just works o_O
    pub fn reverse(&mut self) {
        if self.head.is_none() {
            return;
        }

        let mut reversed: Link<T> = None;
        let mut rest: Link<T> = self.head.take();
        while rest.is_some() {
            let rest_tail = rest.as_mut().unwrap().next.take();
            rest.as_mut().unwrap().next = reversed;
            reversed = rest;
            rest = rest_tail;
        }
        self.head = reversed;
    }

    // in case of error, returns the length of the list
    // wtf. it works on the first try. WHAT
    pub fn swap(&mut self, pos1: usize, pos2: usize) -> Result<(), usize> {
        // swapping a node with itself is a no-op
        if pos1 == pos2 {
            return Ok(());
        }
        // Both nodes must exist in the list.
        if pos1 >= self.length() || pos2 >= self.length() {
            let len = self.length();
            return Err(len);
        }
        // normalize to postpone temporary insanity
        let (left_pos, right_pos) = (std::cmp::min(pos1, pos2), std::cmp::max(pos1, pos2));
        // split lists to avoid two mutable references on the list at once (which Rust forbids)
        // I could even split this in 3 lists, which would make the remaining operations
        // a bit more obviously correct.
        let mut right_list: SinglyLinkedList<T> = self.split_off(right_pos);

        // after normalization, this node MUST be in the left list
        let mut link_to_left_node: Option<&mut Link<T>> = self.link_to_pos_mut(left_pos);
        // remove successor of left node from left list.
        let left_succ = link_to_left_node
            .as_mut()
            .unwrap()
            .as_mut()
            .unwrap()
            .next
            .take();
        // remove left node from left list, leaving two lists and one node
        let box_left_node: Option<Box<Node<T>>> = link_to_left_node.as_mut().unwrap().take();

        // remove right node from right list
        let box_right_node: Option<Box<Node<T>>> = right_list.pop_front_node();

        // This one is easy: put left node in position of right node
        right_list.push_single_front_node(box_left_node.unwrap());

        // put right node in position of left node.
        //
        // First, let left part of left list point to right node.
        // Link then has its final value,
        // so I can just unwrap() it without as_mut() this time.
        let link_to_left_node = link_to_left_node.unwrap();
        *link_to_left_node = box_right_node;
        // Second, let right node point to right part of left list
        link_to_left_node.as_mut().unwrap().next = left_succ;

        self.append(right_list);

        Ok(())
    }

    pub fn move_to_front(&mut self, pos: usize) -> Result<(), usize> {
        match self.link_to_pos_mut(pos) {
            None => Err(self.length()),
            Some(link_to_node) => {
                // remove node from list
                let mut node: Link<T> = link_to_node.take();
                if node.is_none() {
                    Err(self.length())
                } else {
                    // skip removed node
                    *link_to_node = node.as_mut().unwrap().next.take();
                    self.push_single_front_node(node.unwrap());
                    Ok(())
                }
            }
        }
    }

    pub fn move_to_back(&mut self, pos: usize) -> Result<(), usize> {
        match self.link_to_pos_mut(pos) {
            None => Err(self.length()),
            Some(link_to_node) => {
                // remove node from list
                let mut node: Link<T> = link_to_node.take();
                if node.is_none() {
                    Err(self.length())
                } else {
                    // skip removed node
                    *link_to_node = node.as_mut().unwrap().next.take();
                    self.push_single_back_node(node.unwrap());
                    Ok(())
                }
            }
        }
    }

    pub fn remove_range(&mut self, range: std::ops::Range<usize>) -> Result<Self, usize> {
        let range_len = range.end - range.start;
        if range_len == 0 {
            return Ok(Self::new());
        } else if range.end > self.length() {
            return Err(self.length());
        }

        let mut range_and_right_part = self.split_off(range.start);
        let right_part = range_and_right_part.split_off(range_len);
        self.append(right_part);
        Ok(range_and_right_part)
    }

    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    // I could use an iterator to do this or reuse some on the other methods,
    // but it's just so much fun...
    pub fn merge(&mut self, mut other: Self) {
        if other.is_empty() {
            return;
        }
        // not sure if it's possible to do this without storing self
        // as a local variable. The ownership gets tricky.
        let mut me: Self = self.remove_range(0..self.length()).unwrap();
        let mut new_list = Self::new();
        let mut new_list_end: &mut Link<T> = &mut new_list.head;
        while !me.is_empty() && !other.is_empty() {
            let my_node = me.pop_front_node().unwrap();
            let other_node = other.pop_front_node().unwrap();
            *new_list_end = Some(my_node);
            new_list_end = &mut new_list_end.as_mut().unwrap().next;
            *new_list_end = Some(other_node);
            new_list_end = &mut new_list_end.as_mut().unwrap().next;
        }
        if me.is_empty() {
            *new_list_end = other.head.take();
        } else if other.is_empty() {
            *new_list_end = me.head.take();
        } else {
            panic!("merge should never be here.");
        }
        self.append(new_list);
    }
}

impl<T> Drop for SinglyLinkedList<T> {
    // Not necessary for memory correctness, but absolutely needed to prevent stack overflow
    fn drop(&mut self) {
        while let Some(_) = self.pop_front_node() {}
    }
}

impl<T: Display> Display for SinglyLinkedList<T> {
    fn fmt(&self, w: &mut std::fmt::Formatter) -> std::result::Result<(), std::fmt::Error> {
        write!(w, "[")?;
        let strings = self.iter().map(T::to_string).collect::<Vec<_>>();
        write!(w, "{}", strings.join(" "))?;
        write!(w, "]")
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
    fn merge() {
        let mut list = SinglyLinkedList::new();
        list.push_back(0);
        list.push_back(1);
        list.push_back(2);

        let mut other = SinglyLinkedList::new();
        other.push_back(5);
        other.push_back(6);
        other.push_back(7);
        list.merge(other);

        assert_eq!(list.to_string(), "[0 5 1 6 2 7]");

        let mut list = SinglyLinkedList::new();
        list.push_back(0);
        list.push_back(1);
        list.push_back(2);

        let mut other = SinglyLinkedList::new();
        other.push_back(5);
        other.push_back(6);
        other.push_back(7);
        other.push_back(8);
        other.push_back(9);
        list.merge(other);

        assert_eq!(list.to_string(), "[0 5 1 6 2 7 8 9]");

        let mut list = SinglyLinkedList::new();
        list.push_back(0);
        list.push_back(1);
        list.push_back(2);
        list.push_back(3);
        list.push_back(4);

        let mut other = SinglyLinkedList::new();
        other.push_back(5);
        other.push_back(6);
        other.push_back(7);
        list.merge(other);

        assert_eq!(list.to_string(), "[0 5 1 6 2 7 3 4]");
    }

    #[test]
    fn insert_list() {
        let mut list = SinglyLinkedList::new();
        list.push_back(0);
        list.push_back(1);
        list.push_back(2);
        list.push_back(3);
        list.push_back(4);

        let mut list2 = SinglyLinkedList::new();
        list2.push_back(7);
        list2.push_back(8);
        list2.push_back(9);

        let _ = list.insert_list(list2, 2);
        assert_eq!(list.to_string(), "[0 1 7 8 9 2 3 4]");
    }

    #[test]
    fn remove_range() {
        let mut list = SinglyLinkedList::new();
        list.push_back(0);
        list.push_back(1);
        list.push_back(2);
        list.push_back(3);
        list.push_back(4);

        let removed_range = list.remove_range(0..2).unwrap();
        assert_eq!(list.to_string(), "[2 3 4]");
        assert_eq!(removed_range.to_string(), "[0 1]");
        let mut whole_list = list.remove_range(0..3).unwrap();
        assert!(list.is_empty());
        assert_eq!(whole_list.to_string(), "[2 3 4]");
        let last_part = whole_list.remove_range(1..3).unwrap();
        assert_eq!(whole_list.to_string(), "[2]");
        assert_eq!(last_part.to_string(), "[3 4]");
    }

    #[test]
    fn move_to_back() {
        let mut list = SinglyLinkedList::new();
        list.push_back(0);
        list.push_back(1);
        list.push_back(2);
        list.push_back(3);
        list.push_back(4);
        assert_eq!(list.to_string(), "[0 1 2 3 4]");
        let _ = list.move_to_back(3);
        assert_eq!(list.to_string(), "[0 1 2 4 3]");
        let _ = list.move_to_back(3);
        assert_eq!(list.to_string(), "[0 1 2 3 4]");
        let _ = list.move_to_back(1);
        assert_eq!(list.to_string(), "[0 2 3 4 1]");
        let _ = list.move_to_back(0);
        assert_eq!(list.to_string(), "[2 3 4 1 0]");
        let _ = list.move_to_back(2);
        assert_eq!(list.to_string(), "[2 3 1 0 4]");
        let r = list.move_to_back(5);
        assert!(r.is_err());
        let r = list.move_to_back(6);
        assert!(r.is_err());
    }

    #[test]
    fn move_to_front() {
        let mut list = SinglyLinkedList::new();
        list.push_back(0);
        list.push_back(1);
        list.push_back(2);
        list.push_back(3);
        list.push_back(4);
        assert_eq!(list.to_string(), "[0 1 2 3 4]");
        let _ = list.move_to_front(0);
        assert_eq!(list.to_string(), "[0 1 2 3 4]");
        let _ = list.move_to_front(1);
        assert_eq!(list.to_string(), "[1 0 2 3 4]");
        let _ = list.move_to_front(1);
        assert_eq!(list.to_string(), "[0 1 2 3 4]");
        let _ = list.move_to_front(2);
        assert_eq!(list.to_string(), "[2 0 1 3 4]");
        let _ = list.move_to_front(3);
        assert_eq!(list.to_string(), "[3 2 0 1 4]");
        let r = list.move_to_front(5);
        assert!(r.is_err());
        let r = list.move_to_front(6);
        assert!(r.is_err());
    }

    #[test]
    fn swap() {
        let mut list = SinglyLinkedList::new();
        list.push_back(0);
        list.push_back(1);
        list.push_back(2);
        list.push_back(3);
        list.push_back(4);
        assert_eq!(list.to_string(), "[0 1 2 3 4]");
        let _ = list.swap(1, 2);
        assert_eq!(list.to_string(), "[0 2 1 3 4]");
        let _ = list.swap(1, 2);
        assert_eq!(list.to_string(), "[0 1 2 3 4]");
        let _ = list.swap(0, 4);
        assert_eq!(list.to_string(), "[4 1 2 3 0]");
        let res = list.swap(0, 5);
        assert!(res.is_err());
        assert_eq!(list.to_string(), "[4 1 2 3 0]");
        let _ = list.swap(0, 4);
        let _ = list.swap(0, 3);
        assert_eq!(list.to_string(), "[3 1 2 0 4]");
        let _ = list.swap(1, 4);
        assert_eq!(list.to_string(), "[3 4 2 0 1]");
    }

    #[test]
    fn clear() {
        let mut list = SinglyLinkedList::new();
        list.push_back(0);
        list.push_back(1);
        list.push_back(2);
        list.clear();
        assert_eq!(list.pop_front(), None);
    }

    #[test]
    fn reverse() {
        let mut list = SinglyLinkedList::new();
        list.push_back(0);
        list.push_back(1);
        list.push_back(2);
        list.push_back(3);
        list.push_back(4);
        assert_eq!(list.to_string(), "[0 1 2 3 4]");
        list.reverse();
        assert_eq!(list.to_string(), "[4 3 2 1 0]");
        list.reverse();
        assert_eq!(list.to_string(), "[0 1 2 3 4]");

        let mut list = SinglyLinkedList::new();
        assert_eq!(list.to_string(), "[]");
        list.reverse();
        assert_eq!(list.to_string(), "[]");
        list.push_back(0);
        assert_eq!(list.to_string(), "[0]");
        list.reverse();
        assert_eq!(list.to_string(), "[0]");
    }

    #[test]
    fn display() {
        let mut list = SinglyLinkedList::new();
        list.push_back(0);
        list.push_back(1);
        list.push_back(2);
        list.push_back(3);
        list.push_back(4);
        assert_eq!(list.to_string(), String::from("[0 1 2 3 4]"));
    }

    #[test]
    fn split_off() {
        let mut list = SinglyLinkedList::new();
        list.push_back(0);
        list.push_back(1);
        list.push_back(2);
        list.push_back(3);
        list.push_back(4);
        let mut right_part = list.split_off(3);
        assert_eq!(list.to_string(), "[0 1 2]");
        assert_eq!(right_part.to_string(), "[3 4]");
        let empty = right_part.split_off(2);
        assert_eq!(empty.to_string(), "[]");
    }

    #[test]
    fn split() {
        let mut list = SinglyLinkedList::new();
        list.push_back(0);
        list.push_back(1);
        list.push_back(2);
        list.push_back(3);
        list.push_back(4);
        let (mut l1, mut l2) = list.split(2);
        assert_eq!(l1.pop_front(), Some(0));
        assert_eq!(l1.pop_front(), Some(1));
        assert_eq!(l1.pop_front(), None);
        assert_eq!(l2.pop_front(), Some(2));
        assert_eq!(l2.pop_front(), Some(3));
        assert_eq!(l2.pop_front(), Some(4));
        assert_eq!(l2.pop_front(), None);
    }

    #[test]
    fn append() {
        let mut list1 = SinglyLinkedList::new();
        list1.push_back(0);
        list1.push_back(1);
        list1.push_back(2);

        let mut list2 = SinglyLinkedList::new();
        list2.push_back(3);
        list2.push_back(4);
        list2.push_back(5);

        list1.append(list2);
        assert_eq!(list1.pop_front(), Some(0));
        assert_eq!(list1.pop_front(), Some(1));
        assert_eq!(list1.pop_front(), Some(2));
        assert_eq!(list1.pop_front(), Some(3));
        assert_eq!(list1.pop_front(), Some(4));
        assert_eq!(list1.pop_front(), Some(5));
        assert_eq!(list1.pop_front(), None);
    }

    #[test]
    fn remove() {
        let mut list = SinglyLinkedList::new();
        list.push_back(0);
        list.push_back(1);
        list.push_back(2);
        list.push_back(3);
        list.push_back(4);
        list.push_back(5);
        let res = list.remove(7);
        assert_eq!(res, Err(6));
        let res = list.remove(6);
        assert_eq!(res, Err(6));
        // 0 1 2 3 4 5
        let _ = list.remove(5);
        // 0 1 2 3 4
        let _ = list.remove(2);
        // 0 1 3 4
        let _ = list.remove(0);
        // 1 3 4
        assert_eq!(list.pop_front(), Some(1));
        assert_eq!(list.pop_front(), Some(3));
        assert_eq!(list.pop_front(), Some(4));
        assert_eq!(list.pop_front(), None);
    }

    #[test]
    fn insert() {
        // elem, pos
        let mut list = SinglyLinkedList::new();
        let res = list.insert(1337, 1);
        assert_eq!(res, Err(1337));
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        let _ = list.insert(5, 0);
        let _ = list.insert(6, 0);
        let _ = list.insert(10, 1);
        let _ = list.insert(15, 5);
        let _ = list.insert(37, 7);
        // 6 10 5 3 2 15 1 37
        assert_eq!(list.pop_front(), Some(6));
        assert_eq!(list.pop_front(), Some(10));
        assert_eq!(list.pop_front(), Some(5));
        assert_eq!(list.pop_front(), Some(3));
        assert_eq!(list.pop_front(), Some(2));
        assert_eq!(list.pop_front(), Some(15));
        assert_eq!(list.pop_front(), Some(1));
        assert_eq!(list.pop_front(), Some(37));
    }

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

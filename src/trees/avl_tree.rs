use std::cmp::max;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::fmt;
use std::fmt::Display;
use std::mem;

// todo neu:
// comprehensive integrity checks
// remove more useless stuff

// todo alt:
// insert + rebalance
// strategie: erstmal nur einfügen, danach von der wurzel neu suchen und rotieren.
// sollte in safe rust problemlos möglich sein
//
// remove + rebalance
// strategie:
// so wie bei einfügen, nur wiederholt. dabei geht etwas performance verloren, weil immer neu
// gesucht wird, anstatt dem parent pointer nach oben zu folgen.
// alternativ könnte der baum modifiziert werden, indem man temporär die ganzen knoten zerhackt.
// das hat dann noch zusätzliche kosten, könnte aber in der O(n) analyse insgesamt vorteilhaft
// sein. Ich denke, das sollte ich machen, sonst ist es zu einfach.
// unsafe rust mit *mut T wäre natürlich die leichtere lösung, aber wo bleibt da all der spaß.
//
// kleine funktionen:
// Node:
// is_balanced()
//
// AVLTree:
// top_unbalanced_node()
// bottom_unbalanced_node()
// split_top_to_bottom_unbalanced_node() <- zerhacke baum entlang diesem pfad, also speichere
// - den letzten nicht abgehackten node und L/R
// - ein array nodes und L/R
// - den letzten teilbaum. evtl. einfach der letzte eintrag im array
// Vec für stack abarbeitung scheint sehr angemessen.
//

// based on BinarySearchTree, but extended and restricted and removed
// some things irrelevant for AVL property
type Link<T> = Option<Box<Node<T>>>;

#[derive(Debug)]
pub struct Node<T> {
    pub elem: T,
    pub height: i32,
    pub left: Link<T>,
    pub right: Link<T>,
}

impl<T: Ord> Node<T> {
    pub fn assert_balanced(&self) {
        assert!((self.get_height_left_subtree() - self.get_height_right_subtree()).abs() <= 1);
        self.left.as_ref().map(|n| n.assert_balanced());
        self.right.as_ref().map(|n| n.assert_balanced());
    }
    pub fn assert_sorted(&self) {
        self.left.as_ref().map(|left| left.elem < self.elem);
        self.right.as_ref().map(|right| right.elem > self.elem);
        self.left.as_ref().map(|n| n.assert_sorted());
        self.right.as_ref().map(|n| n.assert_sorted());
    }
    pub fn assert_correct_heights(&self) {
        assert!(
            self.height == max(
                self.get_height_left_subtree(),
                self.get_height_right_subtree()
            ) + 1
        );
        self.left.as_ref().map(|n| n.assert_correct_heights());
        self.right.as_ref().map(|n| n.assert_correct_heights());
    }

    pub fn new(elem: T) -> Node<T> {
        Node {
            elem,
            height: 1,
            left: None,
            right: None,
        }
    }

    // helper method of rotations
    pub fn update_height_relying_on_subtrees(&mut self) {
        let left_height = AVLTree::get_height_from_link(&self.left);
        let right_height = AVLTree::get_height_from_link(&self.right);
        self.height = max(left_height, right_height) + 1;
    }

    pub fn get_height_left_subtree(&self) -> i32 {
        AVLTree::get_height_from_link(&self.left)
    }

    pub fn get_height_right_subtree(&self) -> i32 {
        AVLTree::get_height_from_link(&self.right)
    }

    // compares the height of both subtrees, does not recalculate them
    // ignores the height of the node itself
    pub fn is_balanced(&self) -> bool {
        let left_height = self.left.as_ref().map(|n| n.height).unwrap_or(0);
        let right_height = self.right.as_ref().map(|n| n.height).unwrap_or(0);
        (left_height - right_height).abs() > 1
    }

    pub fn has_no_children(&self) -> bool {
        self.left.is_none() && self.right.is_none()
    }

    pub fn has_exactly_one_child(&self) -> bool {
        self.left.is_some() ^ self.right.is_some()
    }

    pub fn take_only_child_link(&mut self) -> Link<T> {
        assert!(self.has_exactly_one_child());
        if self.left.is_some() {
            self.left.take()
        } else {
            self.right.take()
        }
    }

    fn push_left_branch<'node>(mut node: Option<&'node Node<T>>, stack: &mut Vec<&'node Node<T>>) {
        while let Some(ref leftmost) = node {
            stack.push(leftmost);
            node = leftmost.left.as_ref().map(|n| &**n);
        }
    }
}

impl<T: Display> Display for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let left = match self.left.as_ref() {
            None => String::from("Nil"),
            Some(node_box) => node_box.to_string(),
        };
        let right = match self.right.as_ref() {
            None => String::from("Nil"),
            Some(node_box) => node_box.to_string(),
        };
        if left == "Nil" && right == "Nil" {
            write!(f, "{}", self.elem)
        } else {
            write!(f, "{} ({}) ({})", self.elem, left, right)
        }
    }
}

pub struct IntoIterInOrder<T> {
    stack: Vec<Box<Node<T>>>,
}

pub struct IterInOrder<'tree, T> {
    stack: Vec<&'tree Node<T>>,
}

pub struct IterMutInOrder<'tree, T> {
    stack: Vec<(&'tree mut T, Option<&'tree mut Box<Node<T>>>)>,
}

impl<T: Ord> Drop for AVLTree<T> {
    fn drop(&mut self) {
        let mut queue = VecDeque::new();
        self.root.take().map(|r| queue.push_back(r));
        while let Some(mut node) = queue.pop_front() {
            node.left.take().map(|l| queue.push_back(l));
            node.right.take().map(|r| queue.push_back(r));
        }
    }
}

impl<T: Ord> AVLTree<T> {
    pub fn into_iter_in_order(mut self) -> IntoIterInOrder<T> {
        IntoIterInOrder {
            stack: self.root.take().into_iter().collect(),
        }
    }
    pub fn iter_in_order(&self) -> IterInOrder<T> {
        IterInOrder {
            stack: {
                let mut stack = Vec::new();
                Node::push_left_branch(self.root.as_ref().map(|n| &**n), &mut stack);
                stack
            },
        }
    }
    pub fn iter_mut_in_order(&mut self) -> IterMutInOrder<T> {
        let node = self.root.as_mut();
        let mut stack = Vec::new();
        push_left_branch_mut_1(node, &mut stack);
        IterMutInOrder { stack }
    }
}

impl<T> Iterator for IntoIterInOrder<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let mut last: &mut Node<T> = self.stack.last_mut()?;
        while last.left.is_some() {
            let left = last.left.take().unwrap();
            self.stack.push(left);
            last = self.stack.last_mut().unwrap();
        }
        let mut last: Box<Node<T>> = self.stack.pop().unwrap();
        let right: Option<Box<Node<T>>> = last.right.take();
        right.map(|right| self.stack.push(right));
        Some(last.elem)
    }
}

impl<'tree, T: Ord> Iterator for IterInOrder<'tree, T> {
    type Item = &'tree T;
    // cannot use same technique as in IntoIter, since the tree was not modified!
    // alternative solution(?): for every entry save visited flag (or enum)
    fn next(&mut self) -> Option<Self::Item> {
        let top: &Node<T> = self.stack.pop()?;
        let elem = &top.elem;
        Node::push_left_branch(top.right.as_ref().map(|n| &**n), &mut self.stack);
        Some(elem)
    }
}

fn push_left_branch_mut_1<'tree, T>(
    mut node: Option<&'tree mut Box<Node<T>>>,
    stack: &mut Vec<(&'tree mut T, Option<&'tree mut Box<Node<T>>>)>,
) {
    while let Some(n) = node {
        stack.push((&mut n.elem, n.right.as_mut()));
        node = n.left.as_mut();
    }
}

impl<'tree, T> Iterator for IterMutInOrder<'tree, T> {
    type Item = &'tree mut T;
    fn next(&mut self) -> Option<Self::Item> {
        let (elem, node) = self.stack.pop()?;
        push_left_branch_mut_1(node, &mut self.stack);
        Some(elem)
    }
}

#[derive(Debug)]
pub struct AVLTree<T: Ord> {
    pub root: Link<T>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Direction {
    Left,
    Right,
}

impl<T: Ord> AVLTree<T> {
    // todo: recursive things. only for sanity tests.
    fn assert_balanced(&self) {
        self.root.as_ref().map(|root| root.assert_balanced());
    }
    fn assert_sorted(&self) {
        self.root.as_ref().map(|root| root.assert_sorted());
    }
    fn assert_correct_heights(&self) {
        self.root.as_ref().map(|root| root.assert_correct_heights());
    }
    fn assert_ok(&self) {
        self.assert_balanced();
        self.assert_sorted();
        self.assert_correct_heights();
    }

    // succeeds if it exists and has a left child
    // "right" denotes the direction in which the node moves, and downward
    //          elem
    //         /    \
    //        l      C
    //       /  \
    //      A    B
    //      ->
    //      l
    //    /  \
    //   A   elem
    //      /   \
    //     B     C
    fn rotate_right_node(parent_link: &mut Link<T>) {
        if parent_link.is_none() {
            panic!("called rotate_right_node() on empty subtree!");
        }
        if parent_link.as_ref().unwrap().left.is_none() {
            panic!("called rotate_right_node() without left child!");
        }

        // remove left child...
        let mut left_child = parent_link.as_mut().unwrap().left.take();
        // ... and its right subtree from the tree
        let left_child_right_subtree = left_child.as_mut().unwrap().right.take();
        // also remove found node from tree
        let mut top = parent_link.take();
        // now rotate all the things around
        top.as_mut().unwrap().left = left_child_right_subtree;
        top.as_mut().unwrap().update_height_relying_on_subtrees();
        left_child.as_mut().unwrap().right = top;
        left_child
            .as_mut()
            .unwrap()
            .update_height_relying_on_subtrees();
        *parent_link = left_child;
    }

    // succeeds if it exists and has a right child
    // "left" denotes the direction in which the node moves, and downward
    //    elem
    //    /  \
    //   A    l
    //      /   \
    //     B     C
    //      ->
    //           l
    //         /   \
    //      elem    C
    //       /  \
    //      A    B
    fn rotate_left_node(parent_link: &mut Link<T>) {
        if parent_link.is_none() {
            panic!("called rotate_right_node() on empty subtree!");
        }
        if parent_link.as_ref().unwrap().right.is_none() {
            panic!("called rotate_right_node() without right child!");
        }

        // remove right child...
        let mut right_child = parent_link.as_mut().unwrap().right.take();
        // ... and its right subtree from the tree
        let right_child_left_subtree = right_child.as_mut().unwrap().left.take();
        // also remove found node from tree
        let mut top = parent_link.take();
        // now rotate all the things around
        top.as_mut().unwrap().right = right_child_left_subtree;
        top.as_mut().unwrap().update_height_relying_on_subtrees();
        right_child.as_mut().unwrap().left = top;
        right_child
            .as_mut()
            .unwrap()
            .update_height_relying_on_subtrees();
        *parent_link = right_child;
    }

    fn find_mut_node_link(&mut self, elem: &T) -> Option<&mut Link<T>> {
        let mut node_link = &mut self.root;
        while node_link.is_some() {
            // ¯\(u_u)/¯ more elegant while let construction didn't please the borrow checker
            match node_link.as_ref().unwrap().elem.cmp(&elem) {
                Ordering::Equal => return Some(node_link),
                Ordering::Less => node_link = &mut node_link.as_mut().unwrap().right,
                Ordering::Greater => node_link = &mut node_link.as_mut().unwrap().left,
            }
        }
        None
    }

    // todo: rebalance
    pub fn remove(&mut self, elem: &T) {
        // By using links instead of nodes, we don't have to treat the root as a special case
        let node_link = self.find_mut_node_link(elem);
        // this construction is inelegant, but if let is annoying here, too =/
        let node_link: &mut Link<T> = if node_link.is_some() {
            node_link.unwrap()
        } else {
            return;
        };
        let node: &mut Box<Node<T>> = node_link.as_mut().unwrap();
        if node.has_no_children() {
            // remove found node, easiest case
            *node_link = None;
        } else if node.has_exactly_one_child() {
            // "skip" found node, easy case
            *node_link = node.take_only_child_link();
        } else {
            // node has 2 successors, difficult case
            // it might be possible to extract some code from the find_succ() method
            // but here we need to use links to cut out the node, so it would not necessarily become
            // more obvious what is going on

            // find successor node
            let succ_link = {
                let mut succ_link: &mut Link<T> = &mut node.right;
                while succ_link.as_ref().unwrap().left.is_some() {
                    succ_link = &mut succ_link.as_mut().unwrap().left;
                }
                succ_link
            };

            // cut successor node out of tree
            let mut succ_node = succ_link.take();

            // remove children from soon-to-be-removed-node
            let link_left = node.left.take();
            let link_right = node.right.take();

            // append children to successor node
            succ_node.as_mut().unwrap().left = link_left;
            succ_node.as_mut().unwrap().right = link_right;

            // replace target node by successor node
            *node_link = succ_node;
            // old node is dropped implicitly.
            // Since we took out the children, there is no danger of stack overflow
        }
    }

    pub fn find_succ(&self, elem: &T) -> Option<&T> {
        if self.root.is_none() {
            return None;
        }
        let mut mother = None;
        let mut node = self.root.as_ref();
        while let Some(inner_node) = node {
            match inner_node.elem.cmp(&elem) {
                Ordering::Equal => {
                    node = Some(inner_node);
                    break;
                }
                Ordering::Less => node = inner_node.right.as_ref(),
                Ordering::Greater => {
                    node = inner_node.left.as_ref();
                    mother = Some(inner_node);
                }
            }
        }
        // if the node does not exist, it has no successor
        let node = node?;
        if node.right.is_some() {
            // find the smallest (i.e. leftmost) node in the right subtree
            // ...I could extract that with find_min()
            let mut succ = node.right.as_ref().unwrap();
            while succ.left.is_some() {
                succ = succ.left.as_ref().unwrap();
            }
            Some(&succ.elem)
        } else {
            mother.as_ref().map(|m| &m.elem)
        }
    }

    pub fn find_min(&self) -> Option<&T> {
        // assumes correctly sorted tree
        let mut node = self.root.as_ref()?;
        while node.left.is_some() {
            node = node.left.as_ref().unwrap();
        }
        Some(&node.elem)
    }

    pub fn find_min_mut(&mut self) -> Option<&T> {
        // assumes correctly sorted tree
        let mut node = self.root.as_mut()?;
        while node.left.is_some() {
            node = node.left.as_mut().unwrap();
        }
        Some(&mut node.elem)
    }

    pub fn find(&self, elem: &T) -> Option<&T> {
        let mut node = self.root.as_ref();
        while let Some(inner_node) = node {
            match inner_node.elem.cmp(&elem) {
                Ordering::Equal => return Some(&inner_node.elem),
                Ordering::Less => node = inner_node.right.as_ref(),
                Ordering::Greater => node = inner_node.left.as_ref(),
            }
        }
        None
    }

    // helper function for insert(). relies on the height in the immediate subnodes to be correct.
    // ignores value of height
    fn compute_height_from_subtrees(node: &Box<Node<T>>) -> i32 {
        let left_height = AVLTree::get_height_from_link(&node.left);
        let right_height = AVLTree::get_height_from_link(&node.right);
        max(left_height, right_height) + 1
    }

    // relies on the height value to be correct
    // 0 for None
    fn get_height_from_link(link: &Link<T>) -> i32 {
        link.as_ref().map(|node| node.height).unwrap_or(0)
    }

    // helper function for insert()
    fn rebuild_tree_without_changes_to_structure(
        &mut self,
        mut subtree_link: Link<T>,
        mut stack: Vec<(Box<Node<T>>, Direction)>,
    ) {
        while let Some((mut parent_node, direction)) = stack.pop() {
            match direction {
                Direction::Left => parent_node.left = subtree_link,
                Direction::Right => parent_node.right = subtree_link,
            }
            subtree_link = Some(parent_node);
        }
        self.root = subtree_link;
    }

    // panics if the subtree is already balanced
    fn balance(subtree_link: &mut Link<T>) {
        assert!(subtree_link.is_some());
        let subtree_root = subtree_link.as_ref().unwrap();
        let left_height = subtree_root.left.as_ref().map(|n| n.height).unwrap_or(0);
        let right_height = subtree_root.right.as_ref().map(|n| n.height).unwrap_or(0);
        assert!(
            max(left_height, right_height) + 1 == subtree_root.height
                && !subtree_root.is_balanced()
        );
        match left_height.cmp(&right_height) {
            // left subtree is deeper
            Ordering::Greater => {
                if AVLTree::get_height_from_link(&subtree_root.left.as_ref().unwrap().left)
                    >= AVLTree::get_height_from_link(&subtree_root.left.as_ref().unwrap().right)
                {
                    // LL
                    AVLTree::rotate_right_node(subtree_link);
                // what now?
                } else {
                    // LR
                    AVLTree::rotate_left_node(&mut subtree_link.as_mut().unwrap().left);
                    AVLTree::rotate_right_node(subtree_link);
                }
            }
            // right subtree is deeper
            Ordering::Less => {
                if AVLTree::get_height_from_link(&subtree_root.right.as_ref().unwrap().right)
                    >= AVLTree::get_height_from_link(&subtree_root.right.as_ref().unwrap().left)
                {
                    // RR
                    AVLTree::rotate_left_node(subtree_link);
                // what now?
                } else {
                    // RL
                    AVLTree::rotate_right_node(&mut subtree_link.as_mut().unwrap().right);
                    AVLTree::rotate_left_node(subtree_link);
                }
            }
            Ordering::Equal => panic!("This panic is unreachable or this is a very sad day"),
        }
    }

    // elements are unique, so if the element already exists, return the old one
    //
    // 100% safe rust with some ceremony:
    // 1. split path as node is found
    // 2. insert node at appropriate link.
    // 3. reconstruct tree and correct height, until unbalanced node is found if any
    // 4. rebalance and reconstruct remaining path
    // (if comparison panics, the whole tree is removed)
    pub fn insert(&mut self, elem: T) -> Option<T> {
        if self.root.is_none() {
            self.root = Some(Box::new(Node {
                elem: elem,
                height: 1,
                left: None,
                right: None,
            }));
            return None;
        }

        // Step 1: find place for new node and split path
        let mut stack: Vec<(Box<Node<T>>, Direction)> =
            Vec::with_capacity(self.root.as_ref().unwrap().height as usize);
        let mut subtree_link: Link<T> = self.root.take();
        while subtree_link.is_some() {
            match elem.cmp(&subtree_link.as_ref().unwrap().elem) {
                Ordering::Equal => {
                    let old_value = mem::replace(&mut subtree_link.as_mut().unwrap().elem, elem);
                    self.rebuild_tree_without_changes_to_structure(subtree_link, stack);
                    return Some(old_value);
                }
                Ordering::Less => {
                    let next_link = subtree_link.as_mut().unwrap().left.take();
                    stack.push((subtree_link.unwrap(), Direction::Left));
                    subtree_link = next_link;
                }
                Ordering::Greater => {
                    let next_link = subtree_link.as_mut().unwrap().right.take();
                    stack.push((subtree_link.unwrap(), Direction::Right));
                    subtree_link = next_link;
                }
            }
        }
        let mut new_subtree: Box<Node<T>> = Box::new(Node {
            elem: elem,
            height: 1,
            left: None,
            right: None,
        });
        // Step 2: insert node, reconstruct tree and correct height. stop on unbalanced node.
        let mut path_node;
        // todo: while let
        while !stack.is_empty() {
            let (temp_node, direction) = stack.pop().unwrap();
            path_node = temp_node;
            match direction {
                Direction::Left => path_node.left = Some(new_subtree),
                Direction::Right => path_node.right = Some(new_subtree),
            };
            new_subtree = path_node;
            let old_height = new_subtree.height;
            let new_height = AVLTree::compute_height_from_subtrees(&new_subtree);
            if new_height == old_height {
                self.rebuild_tree_without_changes_to_structure(Some(new_subtree), stack);
                return None;
            } else {
                assert!(new_height > old_height);
                new_subtree.height = new_height;
                if new_subtree.is_balanced() {
                    continue;
                } else {
                    let mut new_subtree_link = Some(new_subtree);
                    AVLTree::balance(&mut new_subtree_link);
                    // after balancing, the subtree has the same height as before
                    // therefore, no changes in ancestors
                    self.rebuild_tree_without_changes_to_structure(new_subtree_link, stack);
                    return None;
                }
            }
        }
        // None rebalancing was necessary, but the height changed everywhere. This is not unusual.
        // Can happen e.g. if a node is inserted into a tree where only the root exists
        self.root = Some(new_subtree);
        None
    }

    pub fn is_sorted(&self) -> bool {
        let vec: Vec<_> = self.iter_in_order().collect();
        // is_sorted() on slices is still unstable, so...
        for i in 0..vec.len() - 1 {
            if vec[i] > vec[i + 1] {
                return false;
            }
        }
        true
    }

    // empty tree has height 0, tree with only root has height 1
    // not actually needed for avl tree (?)
    pub fn height(&self) -> i32 {
        // this is a bit ugly. oh well. :)
        match self.root.as_ref() {
            None => 0,
            Some(root) => {
                let mut max_height = 0;
                let mut queue: VecDeque<(&Box<Node<T>>, i32)> = VecDeque::new();
                queue.push_back((&root, 1));
                while let Some(node) = queue.pop_front() {
                    max_height = std::cmp::max(max_height, node.1);
                    node.0
                        .left
                        .as_ref()
                        .map(|n| queue.push_back((&n, node.1 + 1)));
                    node.0
                        .right
                        .as_ref()
                        .map(|n| queue.push_back((&n, node.1 + 1)));
                }
                max_height
            }
        }
    }

    pub fn new_empty() -> Self {
        AVLTree { root: None }
    }
    pub fn new(root: Node<T>) -> Self {
        AVLTree {
            root: Some(Box::new(root)),
        }
    }
}

impl<T: Ord + Display> Display for AVLTree<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let root = match self.root.as_ref() {
            None => String::from("Nil"),
            Some(node_box) => node_box.to_string(),
        };
        write!(f, "[{}]", root)
    }
}

#[cfg(test)]
mod tests {
    use super::AVLTree;
    // remove
    // use super::Node;

    fn create_avl_tree_1() -> AVLTree<i32> {
        // todo: was mach ich damit?
        let mut tree = AVLTree::new_empty();
        tree.insert(1);
        tree.insert(2);
        tree.insert(3);
        tree
    }

    #[test]
    fn rotate_left_node() {
        // // todo:
        // let mut tree = create_sorted_tree_1();
        // let _ = tree.rotate_left(&17);
        // assert_eq!(
        //     tree.to_string(),
        //     "[15 (5 (3) (12 (10 (6) (Nil)) (14))) (16 (Nil) (20 (18 (17) (Nil)) (31)))]"
        // );
        // let _ = tree.rotate_left(&5);
        // assert_eq!(
        //     tree.to_string(),
        //     "[15 (12 (5 (3) (10 (6) (Nil))) (14)) (16 (Nil) (20 (18 (17) (Nil)) (31)))]"
        // );

        // let e = tree.rotate_left(&1337);
        // assert_eq!(e.unwrap_err(), RotateError::MissingKey);
        // let e = tree.rotate_right(&31);
        // assert_eq!(e.unwrap_err(), RotateError::MissingChild);
    }

    #[test]
    fn rotate_right_node() {
        // // todo:
        // let mut tree = create_sorted_tree_1();
        // let _ = tree.rotate_right(&5);
        // assert_eq!(
        //     tree.to_string(),
        //     "[15 (3 (Nil) (5 (Nil) (12 (10 (6) (Nil)) (14)))) (16 (Nil) (20 (17 (Nil) (18)) (31)))]"
        // );
        // let _ = tree.rotate_right(&20);
        // assert_eq!(
        //     tree.to_string(),
        //     "[15 (3 (Nil) (5 (Nil) (12 (10 (6) (Nil)) (14)))) (16 (Nil) (17 (Nil) (20 (18) (31))))]"
        // );

        // let e = tree.rotate_right(&3);
        // assert_eq!(e.unwrap_err(), RotateError::MissingChild);
        // let e = tree.rotate_right(&1337);
        // assert_eq!(e.unwrap_err(), RotateError::MissingKey);
    }

    fn remove() {
        // todo: 
    }

    #[test]
    fn insert() {
        let mut tree = AVLTree::new_empty();
        tree.insert(1);
        tree.insert(2);
        tree.insert(3);
        // todo: das sieht broken aus
        assert_eq!(tree.to_string(), "lol");
    }
}

use std::cmp::max;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::fmt;
use std::fmt::Debug;
use std::fmt::Display;
use std::mem;

// based on BinarySearchTree, but extended and restricted and removed
// some things irrelevant for AVL property
type Link<T> = Option<Box<Node<T>>>;
type Subtree<T> = Link<T>;

#[derive(Debug)]
pub struct Node<T> {
    pub elem: T,
    pub height: i32,
    pub left: Link<T>,
    pub right: Link<T>,
}

enum SplitInstruction {
    Left,
    Right,
    Stop,
}

pub enum NodeType {
    Leaf,
    HalfLeaf,
    Branching,
}

// returns the height as indicated by Node value 'height' or 0 if the subtree is empty
fn subtree_height<T>(root: &Link<T>) -> usize {
    root.as_ref()
        .map(|root| root.height as usize)
        .unwrap_or(0 as usize)
}

impl<T: Ord + Debug + Display> Node<T> {
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
            self.height
                == max(
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
        (left_height - right_height).abs() <= 1
    }

    pub fn is_unbalanced(&self) -> bool {
        !self.is_balanced()
    }

    pub fn node_type(&self) -> NodeType {
        let left = self.left.as_ref().map(|_| 1).unwrap_or(0);
        let right = self.right.as_ref().map(|_| 1).unwrap_or(0);
        match left + right {
            0 => NodeType::Leaf,
            1 => NodeType::HalfLeaf,
            2 => NodeType::Branching,
            _ => panic!("node with wrong number of children"),
        }
    }

    pub fn has_no_children(&self) -> bool {
        self.left.is_none() && self.right.is_none()
    }

    pub fn has_exactly_one_child(&self) -> bool {
        self.left.is_some() ^ self.right.is_some()
    }

    pub fn take_only_child_link(&mut self) -> Link<T> {
        Some(self.take_only_child())
    }

    pub fn take_only_child(&mut self) -> Box<Node<T>> {
        assert!(self.has_exactly_one_child());
        if self.left.is_some() {
            self.left.take().unwrap()
        } else {
            self.right.take().unwrap()
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

impl<T: Ord + Debug> Drop for AVLTree<T> {
    fn drop(&mut self) {
        let mut queue = VecDeque::new();
        self.root.take().map(|r| queue.push_back(r));
        while let Some(mut node) = queue.pop_front() {
            node.left.take().map(|l| queue.push_back(l));
            node.right.take().map(|r| queue.push_back(r));
        }
    }
}

impl<T: Ord + Debug + Display> AVLTree<T> {
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

impl<'tree, T: Ord + Debug + Display> Iterator for IterInOrder<'tree, T> {
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
pub struct AVLTree<T: Ord + Debug> {
    pub root: Link<T>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Direction {
    Left,
    Right,
}

type PathStack<T> = Vec<(Box<Node<T>>, Direction)>;

impl<T: Ord + Debug + Display> AVLTree<T> {
    // recursive things. only for sanity tests. not for production because recursion.
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
    // height is corrected
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
    // height is corrected
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

    fn find_leftmost_child_and_split_path(root: Link<T>) -> (PathStack<T>, Link<T>) {
        AVLTree::find_subtree_and_split_path(root, &|node: &Box<Node<T>>| match node.left {
            Some(_) => SplitInstruction::Left,
            None => SplitInstruction::Stop,
        })
    }

    fn find_value_and_split_path(value: &T, root: Link<T>) -> (PathStack<T>, Link<T>) {
        AVLTree::find_subtree_and_split_path(root, &|node: &Box<Node<T>>| match value
            .cmp(&node.elem)
        {
            Ordering::Equal => SplitInstruction::Stop,
            Ordering::Less => SplitInstruction::Left,
            Ordering::Greater => SplitInstruction::Right,
        })
    }

    fn find_subtree_and_split_path<F>(root: Link<T>, split_function: &F) -> (PathStack<T>, Link<T>)
    where
        F: Fn(&Box<Node<T>>) -> SplitInstruction,
    {
        let mut path_stack: PathStack<T> = Vec::with_capacity(subtree_height(&root));
        let mut subtree_link = root;
        while let Some(mut node) = subtree_link {
            match split_function(&node) {
                SplitInstruction::Left => {
                    let next_link = node.left.take();
                    path_stack.push((node, Direction::Left));
                    subtree_link = next_link;
                }
                SplitInstruction::Right => {
                    let next_link = node.right.take();
                    path_stack.push((node, Direction::Right));
                    subtree_link = next_link;
                }
                SplitInstruction::Stop => {
                    subtree_link = Some(node);
                    break;
                }
            }
        }
        (path_stack, subtree_link)
    }

    // panics if a node would be overwritte, i.e. dropped
    fn append_to_parent_a_node(
        parent: &mut Box<Node<T>>,
        node: Box<Node<T>>,
        direction: Direction,
    ) {
        match direction {
            Direction::Left => {
                assert!(parent.left.is_none());
                parent.left = Some(node)
            }
            Direction::Right => {
                assert!(parent.right.is_none());
                parent.right = Some(node)
            }
        };
    }

    fn append_to_parent_a_subtree(
        parent: &mut Box<Node<T>>,
        subtree: Subtree<T>,
        direction: Direction,
    ) {
        match direction {
            Direction::Left => {
                assert!(parent.left.is_none());
                parent.left = subtree
            }
            Direction::Right => {
                assert!(parent.right.is_none());
                parent.right = subtree
            }
        };
    }

    // minor optimization potential: this function checks for necessary rebalancing at each step,
    // even if the height did not change.
    // it might be possible to use a function that drops the checking
    // as soon as a node with unaltered height is reached
    fn rebuild_and_balance_at_each_step(
        subtree: Subtree<T>,
        path_stack: PathStack<T>,
    ) -> Subtree<T> {
        let (subtree, path_stack) = AVLTree::rebuild_tree(
            subtree,
            path_stack,
            &|subtree, mut parent: Box<Node<T>>, direction| {
                AVLTree::append_to_parent_a_subtree(&mut parent, subtree, direction);
                parent.update_height_relying_on_subtrees();
                let mut parent_subtree = Some(parent);
                AVLTree::balance_if_necessary(&mut parent_subtree);
                (parent_subtree, true)
            },
        );
        assert!(path_stack.is_empty());
        assert!(subtree.as_ref().map(|s| s.is_balanced()).unwrap_or(true));
        subtree
    }

    // this is the hardest thing:
    // 1: find node, split path. if not found, reassemble path and quit
    // 2: distinguish 3 cases:
    // 2a leaf: remove, propagate heights back up and rebalance at each step if necessary
    // 2b half-leaf: as 2a
    // 2c branching node:
    //      - find successor (exists!) in right subtree, split path, take out successor
    //      - propagate heights back up and rebalance right subtree at each step if necessary
    //      - put successor node back in and update height. rebalance if necessary.
    //      - propagate heights back up and rebalance at each step if necessary
    pub fn delete(&mut self, elem: &T) -> Option<T> {
        self.assert_ok();
        let (path_stack, subtree) = AVLTree::find_value_and_split_path(elem, self.root.take());
        match subtree {
            None => {
                self.root = AVLTree::rebuild_original_tree(None, path_stack);
                None
            }
            Some(node) => Some(self.delete_found_node(path_stack, node)),
        }
    }

    fn delete_found_node(&mut self, mut path_stack: PathStack<T>, mut node: Box<Node<T>>) -> T {
        match node.node_type() {
            NodeType::Leaf => {
                println!("delete leaf");
                let value = node.elem;
                self.root = AVLTree::rebuild_and_balance_at_each_step(None, path_stack);
                value
            }
            NodeType::HalfLeaf => {
                println!("delete half leaf");
                let only_child = node.take_only_child();
                let value = node.elem;
                let parent = path_stack.pop();
                match parent {
                    None => {
                        // if it's unbalanced now, it was unbalanced before x_X
                        assert!(only_child.is_balanced());
                        self.root = Some(only_child);
                    }
                    Some((mut parent, direction)) => {
                        AVLTree::append_to_parent_a_node(&mut parent, only_child, direction);
                        parent.update_height_relying_on_subtrees();
                        if parent.is_unbalanced() {
                            println!("remove halfleaf, rebalance before reconstruction");
                            let mut parent_link = Some(parent);
                            AVLTree::balance(&mut parent_link);
                            parent = parent_link.unwrap();
                        }
                        self.root =
                            AVLTree::rebuild_and_balance_at_each_step(Some(parent), path_stack);
                    }
                };
                value
            }
            NodeType::Branching => {
                println!("delete branching node");
                let (right_subtree_path_stack, leftmost_child) = AVLTree::find_leftmost_child_and_split_path(node.right.take());
                let right_subtree_without_successor = AVLTree::rebuild_and_balance_at_each_step(None, right_subtree_path_stack);
                let old_value = mem::replace(&mut node.elem, leftmost_child.unwrap().elem);
                node.right = right_subtree_without_successor;
                node.update_height_relying_on_subtrees();
                node = AVLTree::balance_node_if_necessary(node);
                self.root = AVLTree::rebuild_and_balance_at_each_step(Some(node), path_stack);
                old_value
            }
        }
    }

    pub fn remove_old(&mut self, elem: &T) {
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

    fn rebuild_tree<F>(
        mut subtree: Link<T>,
        mut path_stack: PathStack<T>,
        combine_func: &F,
    ) -> (Subtree<T>, PathStack<T>)
    where
        F: Fn(
            /* subtree: */ Link<T>,
            /* parent: */ Box<Node<T>>,
            Direction,
        ) -> (Link<T>, /* continue */ bool),
    {
        let mut continue_ = true;
        while continue_ && !path_stack.is_empty() {
            let (parent_node, direction) = path_stack.pop().unwrap();
            let temp = combine_func(subtree, parent_node, direction);
            subtree = temp.0;
            continue_ = temp.1;
        }
        (subtree, path_stack)
    }

    fn rebuild_original_tree(subtree: Link<T>, path_stack: PathStack<T>) -> Link<T> {
        AVLTree::rebuild_tree(subtree, path_stack, &|subtree, mut parent, direction| {
            match direction {
                Direction::Left => parent.left = subtree,
                Direction::Right => parent.right = subtree,
            }
            (Some(parent), true)
        })
        .0
    }

    fn balance_node_if_necessary(node: Box<Node<T>>)-> Box<Node<T>> {
        let mut node_link = Some(node);
        AVLTree::balance_if_necessary(&mut node_link);
        node_link.unwrap()
    }

    // like balance, but works also for empty and balanced subtrees (noop)
    fn balance_if_necessary(subtree_link: &mut Link<T>) {
        if subtree_link.is_some() && subtree_link.as_ref().unwrap().is_unbalanced() {
            AVLTree::balance(subtree_link);
        }
    }

    // panics if the subtree is already balanced or empty
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
                    println!("LL");
                    AVLTree::rotate_right_node(subtree_link);
                // what now?
                } else {
                    // LR
                    println!("LR");
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
                    println!("RR");
                    AVLTree::rotate_left_node(subtree_link);
                // what now?
                } else {
                    // RL
                    println!("RL");
                    AVLTree::rotate_right_node(&mut subtree_link.as_mut().unwrap().right);
                    AVLTree::rotate_left_node(subtree_link);
                }
            }
            Ordering::Equal => panic!("This panic is unreachable or this is a very sad day"),
        }
    }

    fn create_new_subtree(elem: T) -> Subtree<T> {
        Some(Box::new(Node {
            elem: elem,
            height: 1,
            left: None,
            right: None,
        }))
    }

    // elements are unique, so if the element already exists, return the old one
    //
    // 100% safe rust with some tricks:
    // 1. split path as node is found
    // 2. insert node at appropriate link.
    // 3. reconstruct tree and correct height, until unbalanced node is found if any
    // 4. rebalance and reconstruct remaining path
    // (if comparison panics, the whole tree is removed)
    pub fn insert(&mut self, elem: T) -> Option<T> {
        self.assert_ok();
        let (stack, subtree) = AVLTree::find_value_and_split_path(&elem, self.root.take());
        match subtree {
            Some(subtree) => {
                self.root = AVLTree::rebuild_original_tree(Some(subtree), stack);
                Some(elem)
            }
            None => {
                let new_node = AVLTree::create_new_subtree(elem);
                // Step 2: insert node, reconstruct tree and correct height. stop on unbalanced node.
                // rebuild until unbalanced node found or until height has not changed
                let (mut modified_subtree, path_stack) = AVLTree::rebuild_tree(
                    new_node,
                    stack,
                    &|subtree, mut parent: Box<Node<T>>, direction| {
                        let parent_old_height = parent.height;
                        AVLTree::append_to_parent_a_subtree(&mut parent, subtree, direction);
                        let parent_new_height = AVLTree::compute_height_from_subtrees(&parent);
                        if parent_new_height == parent_old_height {
                            // no changes in ancestors necessary,
                            // so stop and rebuild the rest without checks and height updates
                            (Some(parent), false)
                        } else {
                            parent.height = parent_new_height;
                            let continue_ = parent.is_balanced();
                            (Some(parent), continue_)
                        }
                    },
                );
                match modified_subtree.as_ref().unwrap().is_balanced() {
                    true => {
                        // stack is empty if the root's height changed without rebalancing.
                        // This happens i.e. always on the second insertion.
                        self.root = AVLTree::rebuild_original_tree(modified_subtree, path_stack);
                    }
                    false => {
                        println!(
                            "found unbalanced subtree: {}",
                            modified_subtree.as_ref().unwrap().to_string()
                        );
                        AVLTree::balance(&mut modified_subtree);
                        // after balancing, the subtree has the same height as before
                        // therefore, no changes in ancestors
                        self.root = AVLTree::rebuild_original_tree(modified_subtree, path_stack);
                    }
                }
                None
            }
        }
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

impl<T: Ord + Display + Debug> Display for AVLTree<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let root = match self.root.as_ref() {
            None => String::from("Nil"),
            Some(node_box) => node_box.to_string(),
        };
        write!(f, "[{}]", root)
    }
}

// impl<T: Ord + Display + Debug> Display for Node<T> {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         let left = self.left.to_string();
//         let right = self.right.to_string();
//         let value = self.elem.to_string();

//         write!(f, "({} {} {})", value, left, right)
//     }
// }

#[cfg(test)]
mod tests {
    use super::AVLTree;

    #[test]
    fn delete() {
        let mut tree = AVLTree::new_empty();
        tree.insert(10);
        tree.delete(&10);
        tree.insert(10);
        tree.delete(&10);
        tree.insert(10);
        tree.insert(20);
        tree.delete(&20);
        tree.insert(20);
        tree.delete(&10);
        tree.insert(30);
        tree.insert(10);
        tree.insert(40);
        tree.delete(&30);

        tree.assert_ok();

        // 10 20 5 30 d5 failed!
        let mut tree = AVLTree::new_empty();
        tree.insert(10);
        tree.insert(20);
        tree.insert(5);
        tree.insert(30);
        tree.delete(&5);

        tree.assert_ok();

        let mut tree = AVLTree::new_empty();
        tree.insert(10);
        tree.insert(20);
        tree.insert(5);
        tree.insert(7);
        tree.insert(30);
        tree.insert(15);
        tree.insert(40);
        tree.delete(&5);
        tree.assert_ok();

        let mut tree = AVLTree::new_empty();
        tree.insert(5);
        tree.insert(10);
        tree.insert(3);
        tree.insert(7);
        tree.insert(15);
        tree.delete(&5);
        tree.assert_ok();

        let mut tree = AVLTree::new_empty();
        tree.insert(5);
        tree.insert(10);
        tree.insert(3);
        tree.insert(7);
        tree.insert(15);
        tree.delete(&5);

        tree.assert_ok();

        let mut tree = AVLTree::new_empty();
        tree.insert(50);
        tree.insert(20);
        tree.insert(100);
        tree.insert(10);
        tree.insert(40);
        tree.insert(75);
        tree.insert(150);
        tree.insert(30);
        tree.insert(45);
        tree.insert(60);
        tree.insert(90);
        tree.insert(25);

        tree.delete(&100);
        tree.assert_ok();

        // println!("TEST SUCCEEDED!");
        // panic!("lol");
    }

    #[test]
    fn insert() {
        let mut tree = AVLTree::new_empty();
        tree.insert(10);
        tree.insert(5);
        tree.insert(20);
        tree.insert(17);
        tree.insert(3);
        tree.insert(14);
        tree.assert_ok();
        let tree_before = tree.to_string();
        let o = tree.insert(14);
        let tree_after = tree.to_string();
        tree.assert_ok();
        assert_eq!(o, Some(14));
        assert_eq!(tree_before, tree_after);

        // RR
        let mut tree = AVLTree::new_empty();
        tree.insert(1);
        tree.assert_ok();
        tree.insert(2);
        tree.assert_ok();
        tree.insert(3);
        tree.assert_ok();
        assert_eq!(tree.to_string(), "[2 (1) (3)]");
        tree.insert(4);
        tree.assert_ok();
        tree.insert(5);
        tree.assert_ok();
        assert_eq!(tree.to_string(), "[2 (1) (4 (3) (5))]");

        // RL
        let mut tree = AVLTree::new_empty();
        tree.insert(1);
        tree.assert_ok();
        tree.insert(20);
        tree.assert_ok();
        assert_eq!(tree.to_string(), "[1 (Nil) (20)]");
        tree.insert(10);
        tree.assert_ok();
        assert_eq!(tree.to_string(), "[10 (1) (20)]");
        tree.insert(30);
        tree.assert_ok();
        tree.insert(25);
        tree.assert_ok();
        assert_eq!(tree.to_string(), "[10 (1) (25 (20) (30))]");

        // LL
        let mut tree = AVLTree::new_empty();
        tree.insert(30);
        tree.assert_ok();
        tree.insert(20);
        tree.assert_ok();
        tree.insert(10);
        tree.assert_ok();
        assert_eq!(tree.to_string(), "[20 (10) (30)]");
        tree.insert(8);
        tree.assert_ok();
        tree.insert(5);
        tree.assert_ok();
        assert_eq!(tree.to_string(), "[20 (8 (5) (10)) (30)]");

        // LR
        let mut tree = AVLTree::new_empty();
        tree.insert(30);
        tree.assert_ok();
        tree.insert(20);
        tree.assert_ok();
        tree.insert(25);
        tree.assert_ok();
        assert_eq!(tree.to_string(), "[25 (20) (30)]");
        tree.insert(10);
        tree.assert_ok();
        tree.insert(15);
        tree.assert_ok();
        assert_eq!(tree.to_string(), "[25 (15 (10) (20)) (30)]");
    }
}

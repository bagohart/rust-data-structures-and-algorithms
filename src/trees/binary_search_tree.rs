use std::cmp::Ordering;
use std::collections::VecDeque;
use std::fmt;
use std::fmt::Display;

// based on BinaryTree, but extended
// todo:
// insert
// find
// replace
// delete
// is_sorted()
//
// rotations:

type Link<T> = Option<Box<Node<T>>>;

#[derive(Debug)]
pub struct Node<T> {
    pub elem: T,
    pub left: Link<T>,
    pub right: Link<T>,
}

impl<T> Node<T> {
    pub fn new(elem: T) -> Node<T> {
        Node {
            elem,
            left: None,
            right: None,
        }
    }

    // discard old left subtree if necessary
    pub fn set_left_child(&mut self, elem: T) {
        self.left = Some(Box::new(Self::new(elem)));
    }

    // discard old right subtree if necessary
    pub fn set_right_child(&mut self, elem: T) {
        self.right = Some(Box::new(Self::new(elem)));
    }

    pub fn inorder<F>(&self, func: &F)
    where
        F: Fn(&T),
    {
        self.left.as_ref().map(|left| left.inorder(func));
        func(&self.elem);
        self.right.as_ref().map(|right| right.inorder(func));
    }

    pub fn preorder<F>(&self, func: &F)
    where
        F: Fn(&T),
    {
        func(&self.elem);
        self.left.as_ref().map(|left| left.preorder(func));
        self.right.as_ref().map(|right| right.preorder(func));
    }

    pub fn postorder<F>(&self, func: &F)
    where
        F: Fn(&T),
    {
        self.left.as_ref().map(|left| left.postorder(func));
        self.right.as_ref().map(|right| right.postorder(func));
        func(&self.elem);
    }

    fn push_left_branch<'node>(mut node: Option<&'node Node<T>>, stack: &mut Vec<&'node Node<T>>) {
        while let Some(ref leftmost) = node {
            stack.push(leftmost);
            node = leftmost.left.as_ref().map(|n| &**n);
        }
    }

    // just for iter_post_order_2()
    fn push_left_branch_2<'node>(
        mut node: Option<&'node Node<T>>,
        stack: &mut Vec<(&'node Node<T>, bool)>,
    ) {
        while let Some(ref leftmost) = node {
            stack.push((leftmost, false));
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

pub struct IntoIterPreOrder<T> {
    stack: Vec<Box<Node<T>>>,
}

pub struct IntoIterPostOrder<T> {
    stack: Vec<Box<Node<T>>>,
}

pub struct IntoIterLevelOrder<T> {
    queue: VecDeque<Box<Node<T>>>,
}

pub struct IterInOrder<'tree, T> {
    stack: Vec<&'tree Node<T>>,
}

pub struct IterPreOrder<'tree, T> {
    stack: Vec<&'tree Node<T>>,
}

pub struct IterPostOrder<'tree, T> {
    last_visited: Option<&'tree Node<T>>,
    stack: Vec<&'tree Node<T>>,
}

pub struct IterLevelOrder<'tree, T> {
    queue: VecDeque<&'tree Node<T>>,
}

pub struct IterMutInOrder<'tree, T> {
    stack: Vec<(&'tree mut T, Option<&'tree mut Box<Node<T>>>)>,
}

pub struct IterMutPreOrder<'tree, T> {
    stack: Vec<&'tree mut Node<T>>,
}

pub struct IterMutPostOrder<'tree, T> {
    stack: Vec<(&'tree mut T, Option<&'tree mut Box<Node<T>>>)>,
}

pub struct IterMutLevelOrder<'tree, T> {
    queue: VecDeque<&'tree mut Node<T>>,
}

impl<T> Drop for BinarySearchTree<T> {
    fn drop(&mut self) {
        let mut queue = VecDeque::new();
        self.root.take().map(|r| queue.push_back(r));
        while let Some(mut node) = queue.pop_front() {
            node.left.take().map(|l| queue.push_back(l));
            node.right.take().map(|r| queue.push_back(r));
        }
    }
}

impl<T> BinarySearchTree<T> {
    // consuming iterators
    pub fn into_iter_in_order(mut self) -> IntoIterInOrder<T> {
        IntoIterInOrder {
            stack: self.root.take().into_iter().collect(),
        }
    }
    pub fn into_iter_pre_order(mut self) -> IntoIterPreOrder<T> {
        IntoIterPreOrder {
            stack: self.root.take().into_iter().collect(),
        }
    }
    pub fn into_iter_post_order(mut self) -> IntoIterPostOrder<T> {
        IntoIterPostOrder {
            stack: self.root.take().into_iter().collect(),
        }
    }
    pub fn into_iter_level_order(mut self) -> IntoIterLevelOrder<T> {
        IntoIterLevelOrder {
            queue: self.root.take().into_iter().collect(),
        }
    }
    // shared iterators
    pub fn iter_in_order(&self) -> IterInOrder<T> {
        IterInOrder {
            stack: {
                let mut stack = Vec::new();
                Node::push_left_branch(self.root.as_ref().map(|n| &**n), &mut stack);
                stack
            },
        }
    }
    pub fn iter_pre_order(&self) -> IterPreOrder<T> {
        IterPreOrder {
            stack: self.root.iter().map(|box_node| &**box_node).collect(),
        }
    }
    pub fn iter_post_order(&self) -> IterPostOrder<T> {
        IterPostOrder {
            last_visited: None,
            stack: {
                let mut stack = Vec::new();
                Node::push_left_branch(self.root.as_ref().map(|n| &**n), &mut stack);
                stack
            },
        }
    }
    pub fn iter_level_order(&self) -> IterLevelOrder<T> {
        IterLevelOrder {
            queue: self.root.iter().map(|box_node| &**box_node).collect(),
        }
    }

    pub fn iter_mut_in_order(&mut self) -> IterMutInOrder<T> {
        let node = self.root.as_mut();
        let mut stack = Vec::new();
        push_left_branch_mut_1(node, &mut stack);
        IterMutInOrder { stack }
    }

    pub fn iter_mut_post_order(&mut self) -> IterMutPostOrder<T> {
        let node = self.root.as_mut();
        let mut stack = Vec::new();
        push_left_branch_mut_1(node, &mut stack);
        IterMutPostOrder { stack }
    }

    pub fn iter_mut_pre_order(&mut self) -> IterMutPreOrder<T> {
        IterMutPreOrder {
            stack: self
                .root
                .iter_mut()
                .map(|box_node| &mut **box_node)
                .collect(),
        }
    }
    pub fn iter_mut_level_order(&mut self) -> IterMutLevelOrder<T> {
        IterMutLevelOrder {
            queue: self
                .root
                .iter_mut()
                .map(|box_node| &mut **box_node)
                .collect(),
        }
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

impl<T> Iterator for IntoIterPreOrder<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let mut last: Box<Node<T>> = self.stack.pop()?;
        let left = last.left.take();
        let right = last.right.take();
        right.map(|right| self.stack.push(right));
        left.map(|left| self.stack.push(left));
        Some(last.elem)
    }
}

impl<T> Iterator for IntoIterPostOrder<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let mut last: &mut Node<T> = self.stack.last_mut()?;
        while last.left.is_some() || last.right.is_some() {
            if last.left.is_some() {
                let left: Box<Node<T>> = last.left.take().unwrap();
                self.stack.push(left);
                last = self.stack.last_mut().unwrap();
            } else
            /* if last.right.is_some() */
            {
                let right: Box<Node<T>> = last.right.take().unwrap();
                self.stack.push(right);
                last = self.stack.last_mut().unwrap();
            }
        }
        let last: Box<Node<T>> = self.stack.pop().unwrap();
        Some(last.elem)
    }
}

impl<T> Iterator for IntoIterLevelOrder<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let mut first: Box<Node<T>> = self.queue.pop_front()?;
        let left = first.left.take();
        let right = first.right.take();
        left.map(|left| self.queue.push_back(left));
        right.map(|right| self.queue.push_back(right));
        Some(first.elem)
    }
}

impl<'tree, T> Iterator for IterInOrder<'tree, T> {
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

impl<'tree, T> Iterator for IterPreOrder<'tree, T> {
    type Item = &'tree T;
    fn next(&mut self) -> Option<Self::Item> {
        let top = self.stack.pop()?;
        top.right.as_ref().map(|right| self.stack.push(&*right));
        top.left.as_ref().map(|left| self.stack.push(&*left));
        Some(&top.elem)
    }
}

impl<'tree, T> Iterator for IterPostOrder<'tree, T> {
    type Item = &'tree T;

    // Implementation inspired by https://en.wikipedia.org/wiki/Tree_traversal#Post-order_(LRN)
    fn next(&mut self) -> Option<Self::Item> {
        let mut peek_node: &Node<T> = self.stack.last()?;
        // this needs exactly the right number of * and &, otherwise we end up comparing
        // e.g. second-order references which is not what we want here.
        while peek_node.right.is_some()
            && !std::ptr::eq(
                *self.last_visited.as_ref().unwrap(),
                &**peek_node.right.as_ref().unwrap(),
            )
        {
            Node::push_left_branch(peek_node.right.as_ref().map(|n| &**n), &mut self.stack);
            peek_node = self.stack.last().unwrap();
        }
        self.last_visited = self.stack.pop();
        Some(&peek_node.elem)
    }
}

impl<'tree, T> Iterator for IterLevelOrder<'tree, T> {
    type Item = &'tree T;
    fn next(&mut self) -> Option<Self::Item> {
        let top: &Node<T> = self.queue.pop_front()?;
        top.left.as_ref().map(|left| self.queue.push_back(left));
        top.right.as_ref().map(|right| self.queue.push_back(right));
        Some(&top.elem)
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

impl<'tree, T> Iterator for IterMutPostOrder<'tree, T> {
    type Item = &'tree mut T;
    fn next(&mut self) -> Option<Self::Item> {
        let (mut elem, mut right) = self.stack.pop()?;
        while right.is_some() {
            self.stack.push((elem, None));
            push_left_branch_mut_1(right, &mut self.stack);
            let temp = self.stack.pop().unwrap();
            elem = temp.0;
            right = temp.1;
        }
        Some(elem)
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

impl<'tree, T> Iterator for IterMutPreOrder<'tree, T> {
    type Item = &'tree mut T;
    fn next(&mut self) -> Option<Self::Item> {
        let top = self.stack.pop()?;
        top.right.as_mut().map(|right| self.stack.push(&mut *right));
        top.left.as_mut().map(|left| self.stack.push(&mut *left));
        Some(&mut top.elem)
    }
}

impl<'tree, T> Iterator for IterMutLevelOrder<'tree, T> {
    type Item = &'tree mut T;
    fn next(&mut self) -> Option<Self::Item> {
        let top: &mut Node<T> = self.queue.pop_front()?;
        top.left.as_mut().map(|left| self.queue.push_back(left));
        top.right.as_mut().map(|right| self.queue.push_back(right));
        Some(&mut top.elem)
    }
}

#[derive(Debug)]
pub struct BinarySearchTree<T> {
    pub root: Link<T>,
}

impl<T: Ord> BinarySearchTree<T> {
    pub fn find_mut(&mut self, elem: T) -> Option<&mut T> {
        let mut node = self.root.as_mut();
        while let Some(inner_node) = node {
            match inner_node.elem.cmp(&elem) {
                Ordering::Equal => return Some(&mut inner_node.elem),
                Ordering::Less => node = inner_node.right.as_mut(),
                Ordering::Greater => node = inner_node.left.as_mut(),
            }
        }
        None
    }

    pub fn find(&self, elem: T) -> Option<&T> {
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

    pub fn insert(&mut self, elem: T) {
        let mut link: &mut Link<T> = &mut self.root;
        while link.is_some() {
            if elem < link.as_ref().unwrap().elem {
                link = &mut link.as_mut().unwrap().left;
            } else {
                link = &mut link.as_mut().unwrap().right;
            }
        }
        *link = Some(Box::new(Node {
            elem: elem,
            left: None,
            right: None,
        }));
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
        BinarySearchTree { root: None }
    }
    pub fn new(root: Node<T>) -> Self {
        BinarySearchTree {
            root: Some(Box::new(root)),
        }
    }
    pub fn inorder<F>(&self, func: F)
    where
        F: Fn(&T),
    {
        self.root.as_ref().map(|r| r.inorder(&func));
    }

    pub fn preorder<F>(&self, func: F)
    where
        F: Fn(&T),
    {
        self.root.as_ref().map(|r| r.preorder(&func));
    }

    pub fn postorder<F>(&self, func: F)
    where
        F: Fn(&T),
    {
        self.root.as_ref().map(|r| r.postorder(&func));
    }
}

impl<T: Display> Display for BinarySearchTree<T> {
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
    use super::BinarySearchTree;
    use super::Node;

    fn create_tree() -> BinarySearchTree<i32> {
        let mut root = Node::new(1);
        root.set_left_child(2);
        root.set_right_child(3);
        root.right.as_mut().unwrap().set_right_child(6);
        root.left.as_mut().unwrap().set_left_child(4);
        root.left.as_mut().unwrap().set_right_child(5);
        root.left
            .as_mut()
            .unwrap()
            .left
            .as_mut()
            .unwrap()
            .set_left_child(7);
        root.left
            .as_mut()
            .unwrap()
            .right
            .as_mut()
            .unwrap()
            .set_left_child(8);
        root.left
            .as_mut()
            .unwrap()
            .right
            .as_mut()
            .unwrap()
            .set_right_child(9);
        BinarySearchTree::new(root)
        //         1
        //        /   \
        //       2     3
        //     /   \     \
        //    4     5     6
        //   /     / \
        //  7     8   9
    }

    // like create_tree(), but checks postorder better
    fn create_tree_post_order() -> BinarySearchTree<i32> {
        let mut root = Node::new(1);
        root.set_left_child(2);
        root.set_right_child(3);
        root.right.as_mut().unwrap().set_right_child(6);
        root.left.as_mut().unwrap().set_left_child(4);
        root.left.as_mut().unwrap().set_right_child(5);
        root.left
            .as_mut()
            .unwrap()
            .left
            .as_mut()
            .unwrap()
            .set_left_child(7);
        root.left
            .as_mut()
            .unwrap()
            .left
            .as_mut()
            .unwrap()
            .left
            .as_mut()
            .unwrap()
            .set_right_child(1000);
        root.left
            .as_mut()
            .unwrap()
            .left
            .as_mut()
            .unwrap()
            .left
            .as_mut()
            .unwrap()
            .right
            .as_mut()
            .unwrap()
            .set_right_child(1001);
        root.left
            .as_mut()
            .unwrap()
            .right
            .as_mut()
            .unwrap()
            .set_left_child(8);
        root.left
            .as_mut()
            .unwrap()
            .right
            .as_mut()
            .unwrap()
            .set_right_child(9);
        BinarySearchTree::new(root)
        //         1
        //        /   \
        //       2     3
        //     /   \     \
        //    4     5     6
        //   /     / \
        //  7     8   9
        //    \
        //    1000
        //       \
        //       1001
    }

    fn create_sorted_tree_1() -> BinarySearchTree<i32> {
        let mut tree = BinarySearchTree::new_empty();
        tree.insert(15);
        tree.insert(5);
        tree.insert(3);
        tree.insert(12);
        tree.insert(10);
        tree.insert(14);
        tree.insert(6);
        tree.insert(16);
        tree.insert(20);
        tree.insert(17);
        tree.insert(18);
        tree.insert(31);
        tree
    }

    #[test]
    fn find() {
        let tree = create_sorted_tree_1();
        let root = tree.find(15);
        let e10 = tree.find(10);
        let e31 = tree.find(31);
        let e1337 = tree.find(1337);
        assert_eq!(root.unwrap(), &15);
        assert_eq!(e10.unwrap(), &10);
        assert_eq!(e31.unwrap(), &31);
        assert!(e1337.is_none());
    }

    #[test]
    fn is_sorted() {
        let tree = create_sorted_tree_1();
        assert_eq!(tree.is_sorted(), true);
    }

    #[test]
    fn height() {
        let tree = create_sorted_tree_1();
        assert_eq!(tree.height(), 5);
    }

    #[test]
    fn insert() {
        let mut tree = BinarySearchTree::new_empty();
        tree.insert(15);
        tree.insert(5);
        tree.insert(3);
        tree.insert(12);
        tree.insert(10);
        tree.insert(14);
        tree.insert(6);
        tree.insert(16);
        tree.insert(20);
        tree.insert(17);
        tree.insert(18);
        tree.insert(31);
        assert_eq!(
            tree.to_string(),
            "[15 (5 (3) (12 (10 (6) (Nil)) (14))) (16 (Nil) (20 (17 (Nil) (18)) (31)))]"
        );
    }

    #[test]
    fn into_iter() {
        let tree = create_tree();
        let inorder: Vec<i32> = tree.into_iter_in_order().collect();
        assert_eq!(inorder, vec![7, 4, 2, 8, 5, 9, 1, 3, 6]);
        let tree = create_tree();
        let preorder: Vec<i32> = tree.into_iter_pre_order().collect();
        assert_eq!(preorder, vec![1, 2, 4, 7, 5, 8, 9, 3, 6]);
        let tree = create_tree();
        let postorder: Vec<i32> = tree.into_iter_post_order().collect();
        assert_eq!(postorder, vec![7, 4, 8, 9, 5, 2, 6, 3, 1]);
        let tree = create_tree_post_order();
        let postorder: Vec<i32> = tree.into_iter_post_order().collect();
        assert_eq!(postorder, vec![1001, 1000, 7, 4, 8, 9, 5, 2, 6, 3, 1]);
        let tree = create_tree();
        let levelorder: Vec<i32> = tree.into_iter_level_order().collect();
        assert_eq!(levelorder, vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn iter() {
        let tree = create_tree();
        let inorder: Vec<i32> = tree.iter_in_order().copied().collect();
        assert_eq!(inorder, vec![7, 4, 2, 8, 5, 9, 1, 3, 6]);
        let tree = create_tree();
        let preorder: Vec<i32> = tree.iter_pre_order().copied().collect();
        assert_eq!(preorder, vec![1, 2, 4, 7, 5, 8, 9, 3, 6]);
        let tree = create_tree();
        let postorder: Vec<i32> = tree.iter_post_order().copied().collect();
        assert_eq!(postorder, vec![7, 4, 8, 9, 5, 2, 6, 3, 1]);
        let tree = create_tree();
        let levelorder: Vec<i32> = tree.iter_level_order().copied().collect();
        assert_eq!(levelorder, vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn iter_mut() {
        let mut tree = create_tree();
        let preorder: Vec<i32> = tree.iter_mut_pre_order().map(|i| &*i).copied().collect();
        assert_eq!(preorder, vec![1, 2, 4, 7, 5, 8, 9, 3, 6]);

        let mut tree = create_tree();
        let levelorder: Vec<i32> = tree.iter_mut_level_order().map(|i| &*i).copied().collect();
        assert_eq!(levelorder, vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);

        let mut tree = create_tree();
        let inorder: Vec<i32> = tree.iter_mut_in_order().map(|i| &*i).copied().collect();
        assert_eq!(inorder, vec![7, 4, 2, 8, 5, 9, 1, 3, 6]);

        let mut tree = create_tree();
        let postorder: Vec<i32> = tree.iter_mut_post_order().map(|i| &*i).copied().collect();
        assert_eq!(postorder, vec![7, 4, 8, 9, 5, 2, 6, 3, 1]);

        let mut tree = create_tree_post_order();
        let postorder: Vec<i32> = tree.iter_mut_post_order().map(|i| &*i).copied().collect();
        assert_eq!(postorder, vec![1001, 1000, 7, 4, 8, 9, 5, 2, 6, 3, 1]);
    }

    #[test]
    fn basics() {
        let mut root = Node::new(0);
        root.set_left_child(1);
        root.set_right_child(2);
        root.left.as_mut().unwrap().set_left_child(3);
        let tree = BinarySearchTree::new(root);
        assert_eq!(tree.to_string(), "[0 (1 (3) (Nil)) (2)]");
    }

    #[test]
    fn orders() {
        // not actually an automatic test.
        // activate the panic! at the end to see the output
        let mut root = Node::new(0);
        root.set_left_child(1);
        root.set_right_child(2);
        root.left.as_mut().unwrap().set_left_child(3);
        let tree = BinarySearchTree::new(root);
        println!("tree={}", tree);
        print!("inorder = [");
        tree.inorder(|e| print!("{} ", e));
        print!("]");
        print!("preorder = [");
        tree.preorder(|e| print!("{} ", e));
        print!("]");
        print!("postorder = [");
        tree.postorder(|e| print!("{} ", e));
        print!("]");
    }
}

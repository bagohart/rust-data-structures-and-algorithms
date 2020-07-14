use std::collections::VecDeque;
use std::fmt;
use std::fmt::Display;

// todo:
// inorder, preorder, postorder, levelorder
// iter,iter_mut,into_iter

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

impl<T> BinaryTree<T> {
    pub fn into_iter_in_order(self) -> IntoIterInOrder<T> {
        IntoIterInOrder {
            stack: self.root.into_iter().collect(),
        }
    }
    pub fn into_iter_pre_order(self) -> IntoIterPreOrder<T> {
        IntoIterPreOrder {
            stack: self.root.into_iter().collect(),
        }
    }
    pub fn into_iter_post_order(self) -> IntoIterPostOrder<T> {
        IntoIterPostOrder {
            stack: self.root.into_iter().collect(),
        }
    }
    pub fn into_iter_level_order(self) -> IntoIterLevelOrder<T> {
        IntoIterLevelOrder {
            queue: self.root.into_iter().collect(),
        }
    }
}

impl<T> Iterator for IntoIterInOrder<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let mut last: &mut Node<T> = self.stack.last_mut()?; // box to mut implicit?
        while last.left.is_some() {
            let left = last.left.take().unwrap(); // cannot inline (borrowing rules!)
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

#[derive(Debug)]
pub struct BinaryTree<T> {
    pub root: Link<T>,
}

impl<T> BinaryTree<T> {
    pub fn new_empty() -> Self {
        BinaryTree { root: None }
    }
    pub fn new(root: Node<T>) -> Self {
        BinaryTree {
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

impl<T: Display> Display for BinaryTree<T> {
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
    use super::BinaryTree;
    use super::Node;

    fn create_tree() -> BinaryTree<i32> {
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
        BinaryTree::new(root)
        //         1
        //        /   \
        //       2     3
        //     /   \     \
        //    4     5     6
        //   /     / \
        //  7     8   9
    }

    #[test]
    fn iter() {
        let tree = create_tree();
        let inorder: Vec<i32> = tree.into_iter_in_order().collect();
        assert_eq!(inorder, vec![7, 4, 2, 8, 5, 9, 1, 3, 6]);
        let tree = create_tree();
        let preorder: Vec<i32> = tree.into_iter_pre_order().collect();
        assert_eq!(preorder, vec![1, 2, 4, 7, 5, 8, 9, 3, 6]);
        let tree = create_tree();
        let postorder: Vec<i32> = tree.into_iter_post_order().collect();
        assert_eq!(postorder, vec![7, 4, 8, 9, 5, 2, 6, 3, 1]);
        let tree = create_tree();
        let levelorder: Vec<i32> = tree.into_iter_level_order().collect();
        assert_eq!(levelorder, vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn basics() {
        let mut root = Node::new(0);
        root.set_left_child(1);
        root.set_right_child(2);
        root.left.as_mut().unwrap().set_left_child(3);
        let tree = BinaryTree::new(root);
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
        let tree = BinaryTree::new(root);
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
        // panic!("lol");
    }
}

use std::fmt;
use std::fmt::Display;

// todo:
// inorder, preorder, postorder

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

impl<T> BinaryTree<T> {
    pub fn into_iter(self) -> IntoIterInOrder<T> {
        IntoIterInOrder {
            stack: self.root.into_iter().collect(),
        }
    }
}

impl<T> Iterator for IntoIterInOrder<T> {
    type Item = T;
    // let last: Box<Node<T>> = self.stack.pop()?;
    // while last.left.is_some() {
    //     let left = last.left.take().unwrap();
    //     let
    // implementing this with mutable borrows on the stack doesn not work
    // because then there are two mutable borrows to the stack
    // or does it?
    fn next(&mut self) -> Option<Self::Item> {
        // this is actually a box, but there is some casting magic here ?_?
        let last: &mut Node<T> = self.stack.last_mut()?;
        while last.left.is_some() {
            let left = last.left.take().unwrap();
            self.stack.push(left);
            last = self.stack.last_mut().unwrap();
        }
        let last: Box<Node<T>> = self.stack.pop().unwrap();
        let right: Option<Box<Node<T>>> = last.right.take();
        right.map(|right| self.stack.push(right));
        Some(last.elem)
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

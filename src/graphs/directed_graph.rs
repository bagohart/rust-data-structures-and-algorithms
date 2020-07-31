use std::cell::Ref;
use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt;
use std::fmt::Display;
use std::rc::Rc;

// todo
// transpose
// is_symmetric()
// is_complete()
// drop <- check if I get leaks!
// weakly connected
// strongly connected
// components
// cycles
// paths
// more ...

#[derive(Debug)]
pub struct Node<T: Display> {
    datum: T,
    edges: Vec<Rc<RefCell<Node<T>>>>,
}

// useful in some algorithms. maybe.
struct Edge<'graph, T: Display> {
    from: Ref<'graph, Node<T>>,
    to: Ref<'graph, Node<T>>,
}

impl<T: Display> std::hash::Hash for Edge<'_, T> {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        // I could also probably just derive this from the values
        // because only ( equality => hash equality ) must hold
        // but this should work, too, since I overloaded equality as reference equality
        (&*(self.from) as *const Node<T>).hash(state);
        (&*(self.to) as *const Node<T>).hash(state);
    }
}

impl<T: Display> PartialEq for Edge<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        // compare references to nodes.
        // do NOT compare their datums
        std::ptr::eq(&*self.from, &*other.from) && std::ptr::eq(&*self.to, &*other.to)
    }
}

impl<T: Display> Eq for Edge<'_, T> {}

impl<T: Display> Drop for Node<T> {
    fn drop(&mut self) {
        println!("Dropping node with datum {}", self.datum);
    }
}

#[derive(Debug)]
pub struct Graph<T: Display> {
    nodes: Vec<Rc<RefCell<Node<T>>>>,
}

#[derive(Debug)]
pub struct Path<T: Display> {
    nodes: Vec<Node<T>>,
}

impl<T: Display> Display for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let neighbour_datum_to_string = self
            .edges
            .iter()
            .map(|n: &Rc<RefCell<Node<T>>>| n.borrow().datum.to_string())
            .collect::<Vec<_>>();

        write!(
            f,
            "{} -> [{}]",
            self.datum.to_string(),
            neighbour_datum_to_string.join(", ")
        )
    }
}

impl<T: Display> Display for Graph<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let num_nodes = self.nodes.len();
        let node_contents = self
            .nodes
            .iter()
            .map(|n: &Rc<RefCell<Node<T>>>| n.borrow().datum.to_string())
            .collect::<Vec<_>>();
        let nodes_to_string = self
            .nodes
            .iter()
            .map(|n: &Rc<RefCell<Node<T>>>| n.borrow().to_string())
            .collect::<Vec<_>>();

        write!(
            f,
            "{} Nodes: {}\n{}",
            num_nodes,
            node_contents.join(", "),
            nodes_to_string.join("\n")
        )
    }
}

impl<T: Display> Node<T> {
    pub fn new(datum: T) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Node {
            datum: datum,
            edges: Vec::new(),
        }))
    }
}

impl<T: Display> Graph<T> {
    pub fn new() -> Self {
        Graph { nodes: Vec::new() }
    }
    pub fn is_symmetric(&self) -> bool {
        // store all edges, then check if each edge is found in swapped form
        // relies on equality of edges depending on address, not datum

        // note that this MUST come before the next declaration, or the lifetime is messed up o_O
        // we have to keep this thing around for RefCell madness to compile. uh oh.
        let node_refs: Vec<Ref<Node<T>>> = self.nodes.iter().map(|node| node.borrow()).collect();
        let mut all_edges: HashSet<Edge<T>> = HashSet::new();
        for node in node_refs.iter() {
            for neighbour in node.edges.iter() {
                all_edges.insert(Edge {
                    from: Ref::clone(node),
                    to: neighbour.borrow(),
                });
            }
        }

        all_edges.iter().all(|Edge { from: f, to: t }| {
            let sym_edge = Edge {
                from: Ref::clone(t),
                to: Ref::clone(f),
            };
            all_edges.contains(&sym_edge)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::Graph;
    use super::Node;
    // use std::cell::RefCell;
    // use std::rc::Rc;

    fn graph_1() -> Graph<String> {
        let mut graph = Graph::new();
        let node1 = Node::new("A".to_owned());
        graph.nodes.push(node1.clone());
        let node2 = Node::new("B".to_owned());
        node2.borrow_mut().edges.push(node1.clone());
        graph.nodes.push(node2.clone());
        graph
    }

    fn graph_2() -> Graph<String> {
        let mut graph = Graph::new();
        let node1 = Node::new("A".to_owned());
        let node2 = Node::new("B".to_owned());
        node1.borrow_mut().edges.push(node2.clone());
        node2.borrow_mut().edges.push(node1.clone());
        graph.nodes.push(node1.clone());
        graph.nodes.push(node2.clone());
        graph
    }

    fn graph_3() -> Graph<String> {
        let mut graph = Graph::new();
        let node1 = Node::new("A".to_owned());
        let node2 = Node::new("B".to_owned());
        let node3 = Node::new("B".to_owned());
        node1.borrow_mut().edges.push(node2.clone());
        node3.borrow_mut().edges.push(node1.clone());
        graph.nodes.push(node1.clone());
        graph.nodes.push(node2.clone());
        graph.nodes.push(node3.clone());
        graph
    }

    #[test]
    fn is_symmetric() {
        let graph = graph_1();
        println!("{}", graph);
        assert!(!graph.is_symmetric());

        let graph = graph_2();
        println!("{}", graph);
        assert!(graph.is_symmetric());

        // make sure that really references are compared and not contained data
        let graph = graph_3();
        println!("{}", graph);
        assert!(!graph.is_symmetric());
    }

    #[test]
    fn basics() {
        let graph = graph_1();
        println!("{}", graph);
    }
}


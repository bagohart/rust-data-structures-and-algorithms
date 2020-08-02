use std::cell::Ref;
use std::cell::RefCell;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::fmt;
use std::fmt::Display;
use std::rc::Rc;

// todo
// [x] is_complete
// [x] is_symmetric
// [x] transpose
// [x] bfs
// dfs, 
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

pub struct RRNode<T: Display>(Rc<RefCell<Node<T>>>);

pub struct NodeVec<T: Display>(Vec<RRNode<T>>);

impl<T: Display> Display for NodeVec<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = self.0.iter().map(|n| n.0.borrow().datum.to_string()).collect::<Vec<_>>().join(", ");
        write!(f, "{}", s)
    }
}

impl<T: Display> RRNode<T> {
    pub fn clone_from_rc(other: &Rc<RefCell<Node<T>>>) -> Self {
        RRNode(Rc::clone(other))
    }
    pub fn clone(&self) -> Self {
        RRNode::clone_from_rc(&self.0)
    }
}

impl<T: Display> std::hash::Hash for RRNode<T> {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        (&*(self.0.borrow()) as *const Node<T>).hash(state);
    }
}

impl<T: Display> PartialEq for RRNode<T> {
    fn eq(&self, other: &Self) -> bool {
        // check if two Rc<RefCell<_>>s reference the same node
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl<T: Display> Eq for RRNode<T> {}

pub struct Edge<T: Display> {
    from: Rc<RefCell<Node<T>>>,
    to: Rc<RefCell<Node<T>>>,
}

// useful in some algorithms. maybe.
// actually, this is a pain :)
pub struct RefEdge<'graph, T: Display> {
    from: Ref<'graph, Node<T>>,
    to: Ref<'graph, Node<T>>,
}

impl<T: Display> std::hash::Hash for Edge<T> {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        (&*(self.from.borrow()) as *const Node<T>).hash(state);
        (&*(self.to.borrow()) as *const Node<T>).hash(state);
    }
}

impl<T: Display> PartialEq for Edge<T> {
    fn eq(&self, other: &Self) -> bool {
        // check if two edges reference the same nodes
        Rc::ptr_eq(&self.from, &other.from) && Rc::ptr_eq(&self.to, &other.to)
    }
}

impl<T: Display> Eq for Edge<T> {}

impl<T: Display> std::hash::Hash for RefEdge<'_, T> {
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

impl<T: Display> PartialEq for RefEdge<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        // compare references to nodes.
        // do NOT compare their datums
        std::ptr::eq(&*self.from, &*other.from) && std::ptr::eq(&*self.to, &*other.to)
    }
}

impl<T: Display> Eq for RefEdge<'_, T> {}

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
    // computes bfs starting from one node.
    // if the graph is not connected, this is not a complete bfs
    // implementing a complete bfs might require another approach,
    // such as creating a new Node data structure with colours.
    pub fn get_bfs_nodes(&self, start: RRNode<T>) -> NodeVec<T> {
        // ensure start is part of graph
        let mut bfs = Vec::new();
        let mut queue = VecDeque::new();
        let mut found = HashSet::new();
        let mut done = HashSet::new();
        queue.push_back(start.clone());
        found.insert(start.clone());

        while let Some(next) = queue.pop_front() {
            for neighbour in next
                .0
                .borrow()
                .edges
                .iter()
                .map(|n| RRNode::clone_from_rc(n))
            {
                if !done.contains(&neighbour) && !found.contains(&neighbour) {
                    queue.push_back(neighbour.clone());
                    found.insert(neighbour);
                }
            }
            done.insert(next.clone());
            bfs.push(next);
        }
        NodeVec(bfs)
    }
    pub fn get_all_edges(&self) -> Vec<Edge<T>> {
        // this should be faster than the 'nice' version below
        // because no intermittent Vecs are created
        let mut all_edges = Vec::new();
        for node in self.nodes.iter() {
            for neighbour in node.borrow().edges.iter() {
                let edge = Edge {
                    from: Rc::clone(node),
                    to: Rc::clone(neighbour),
                };
                all_edges.push(edge);
            }
        }
        all_edges

        // this works fine as a 'nice' alternative to the double for loop, but
        // it's still not really nice and creates lots of temporary Vecs.
        // node that the temporary Vecs are necessary: returning only an iterator is
        // not possible because then the lifetime of the reference to node is broken
        //
        // self.nodes
        //     .iter()
        //     .flat_map(|node: &Rc<RefCell<Node<T>>>| {
        //         let outgoing_edges: Vec<_> = node
        //             .borrow()
        //             .edges
        //             .iter()
        //             .map(|neighbour: &Rc<RefCell<Node<T>>>| Edge {
        //                 from: Rc::clone(node),
        //                 to: Rc::clone(neighbour),
        //             })
        //             .collect();
        //         outgoing_edges
        //     })
        //     .collect()
    }
    pub fn get_all_edges_set(&self) -> HashSet<Edge<T>> {
        self.get_all_edges().into_iter().collect()
    }
    pub fn is_complete(&self) -> bool {
        let all_edges = self.get_all_edges_set();
        all_edges.iter().all(|edge| {
            all_edges.contains(&Edge {
                from: Rc::clone(&edge.to),
                to: Rc::clone(&edge.from),
            })
        })

        // alternative to iterator: remove elements from set, until
        // it is empty. then, if (a,b) was checked, (b,a) needs not be checked anymore
        // but taking out random elements from HashSet is not possible (I think)
        // so I would need BTreeMap and introduce an arbitrary ordering on the Edges
        // so they can be sorted
        // and all of this seems a bit overkill =/
    }
    pub fn is_symmetric(&self) -> bool {
        // store all edges, then check if each edge is found in swapped form
        // relies on equality of edges depending on address, not datum

        // note that this MUST come before the next declaration, or the lifetime is messed up o_O
        // we have to keep this thing around for RefCell madness to compile. uh oh.
        // With Edge instead of RefEdge, it is easier
        let node_refs: Vec<Ref<Node<T>>> = self.nodes.iter().map(|node| node.borrow()).collect();
        let mut all_edges: HashSet<RefEdge<T>> = HashSet::new();
        for node in node_refs.iter() {
            for neighbour in node.edges.iter() {
                all_edges.insert(RefEdge {
                    from: Ref::clone(node),
                    to: neighbour.borrow(),
                });
            }
        }

        all_edges.iter().all(|RefEdge { from: f, to: t }| {
            let sym_edge = RefEdge {
                from: Ref::clone(t),
                to: Ref::clone(f),
            };
            all_edges.contains(&sym_edge)
        })
    }
    // reverse the direction of all edges
    pub fn transpose(&mut self) {
        let adjacency_lists: Vec<Vec<_>> = self
            .nodes
            .iter_mut()
            .map(|node| node.borrow_mut().edges.drain(..).collect())
            .collect();
        for (node_index, neighbours) in adjacency_lists.into_iter().enumerate() {
            for neighbour in neighbours {
                neighbour
                    .borrow_mut()
                    .edges
                    .push(self.nodes[node_index].clone());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Graph;
    use super::Node;
    use super::RRNode;
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

    fn graph_bfs() -> Graph<String> {
        let mut graph = Graph::new();
        let a = Node::new("A".to_owned());
        let b = Node::new("B".to_owned());
        let c = Node::new("C".to_owned());
        let d = Node::new("D".to_owned());
        let e = Node::new("E".to_owned());
        let f = Node::new("F".to_owned());
        let g = Node::new("G".to_owned());
        a.borrow_mut().edges.push(b.clone());
        a.borrow_mut().edges.push(c.clone());
        a.borrow_mut().edges.push(f.clone());
        b.borrow_mut().edges.push(c.clone());
        b.borrow_mut().edges.push(d.clone());
        d.borrow_mut().edges.push(c.clone());
        d.borrow_mut().edges.push(a.clone());
        e.borrow_mut().edges.push(g.clone());
        e.borrow_mut().edges.push(c.clone());
        f.borrow_mut().edges.push(a.clone());
        f.borrow_mut().edges.push(c.clone());
        g.borrow_mut().edges.push(e.clone());
        g.borrow_mut().edges.push(d.clone());
        graph.nodes.push(a);
        graph.nodes.push(b);
        graph.nodes.push(c);
        graph.nodes.push(d);
        graph.nodes.push(e);
        graph.nodes.push(f);
        graph.nodes.push(g);
        graph
    }

    #[test]
    fn bfs() {
        let graph = graph_bfs();
        println!("{}", graph.to_string());
        let bfs = graph.get_bfs_nodes(RRNode::clone_from_rc(&graph.nodes[0]));
        println!("{}", bfs);
        unimplemented!()
    }

    #[test]
    fn is_complete() {
        assert!(!graph_1().is_complete());
        assert!(graph_2().is_complete());
        assert!(!graph_3().is_complete());
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

        unimplemented!()
    }

    #[test]
    fn transpose() {
        let mut graph = graph_1();
        println!("{}", graph);
        graph.transpose();
        println!("{}", graph);
    }

    #[test]
    fn basics() {
        let graph = graph_1();
        println!("{}", graph);
    }
}

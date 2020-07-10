// VecDeque could also be used (and would probably be more efficient), but for sorting, the needed method is not stable yet

struct PriorityQueueVector<K: Ord, V> {
    data: Vec<PQEntry<K, V>>,
}

struct PQEntry<K: Ord, V> {
    key: K,
    elem: V,
}

// todo: tests
// todo: iter
impl<K: Ord, V> PriorityQueueVector<K, V> {
    pub fn new() -> Self {
        PriorityQueueVector { data: Vec::new() }
    }
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
    pub fn insert(&mut self, elem: V, key: K) {
        if let Some(_) = self.find_elem_by_key(&key) {
            // keys must be unique. could also replace old value. todo (parameter or second method)
            // here, V is dropped!
            return;
        }
        let idx = self
            .data
            .binary_search_by_key(&&key, |pq_entry| &&pq_entry.key)
            .unwrap_or_else(|x| x);
        let elem = PQEntry { key, elem };
        self.data.insert(idx, elem);
    }
    pub fn pop_min(&mut self) -> Option<V> {
        // self.data.pop().map(|pq_entry| pq_entry.elem)
        //todo: this should be possible with some method get_checked(index) or something, but it seems that this wouldn't remove the element.
        if !self.is_empty() {
            Some(self.data.remove(0).elem)
        } else {
            None
        }
    }
    // uses the first element as smallest element. could also interpret this in other way, but then I'd have to define
    // my own comparison thing, as I actually did below. So this *is* possible, just a bit more inconvenient.
    pub fn peek_min(&mut self) -> Option<&V> {
        self.data.first().map(|pq_entry| &pq_entry.elem)
        // self.data.last().map(|pq_entry| &pq_entry.elem)
    }
    pub fn get_elem(&mut self, key: &K) -> Option<V> {
        //todo: better access syntax?
        let idx = self
            .data
            .binary_search_by_key(&key, |pq_entry| &&pq_entry.key)
            .ok()?;
        let elem = self.data.remove(idx);
        Some(elem.elem)
    }
    pub fn peek_elem(&self, key: &K) -> Option<&V> {
        self.peek_pq_entry(key).map(|pq_entry| &pq_entry.elem)
    }
    fn peek_pq_entry(&self, key: &K) -> Option<&PQEntry<K, V>> {
        let idx = self
            .data
            .binary_search_by_key(&key, |pq_entry| &&pq_entry.key)
            .ok()?;
        Some(&self.data[idx])
    }
    fn find_elem_by_key(&self, key: &K) -> Option<usize> {
        self.data.iter().position(|pq_entry| &pq_entry.key == key)
    }
}

impl<K: Ord, V: Eq> PriorityQueueVector<K, V> {
    // just gives the first element. (key is unique)
    fn find_elem(&self, elem: &V) -> Option<usize> {
        self.data.iter().position(|pq_entry| &pq_entry.elem == elem)
    }
    pub fn decr_key(&mut self, elem: &V, smaller_key: K) {
        if let Some(idx) = self.find_elem(&elem) {
            if &self.data[idx].key > &smaller_key {
                let PQEntry { key: _, elem } = self.data.remove(idx);
                self.insert(elem, smaller_key);
            }
        }
    }
}

// I don't actually need this, although it does work, since I discovered binary_search_by_key().
// We don't actually need to declare PartialEq here explicitly, since it is required by Ord anyway.
// Note: This could though be used for an alternative implementation, where the smallest element is at the top of the vector, which might have better performance
impl<K: PartialEq + Ord, V> PartialEq for PQEntry<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

// LOL. this is about transitive things it seems and reuses the implementation of PartialEq.
//impl<K: PartialEq + Ord, V> Eq for PQEntry<K, V> {}

//impl<K: Ord, V> PartialOrd for PQEntry<K, V> {
//    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
//        Some(self.key.cmp(&other.key))
//        //todo: order?
//        // Some(other.key.cmp(&self.key))
//    }
//}

//impl<K: Ord, V> Ord for PQEntry<K, V> {
//    fn cmp(&self, other: &Self) -> Ordering {
//        self.partial_cmp(&other).unwrap()
//    }
//}

#[cfg(test)]
mod tests {
    use super::PriorityQueueVector;

    #[test]
    fn basics() {
        let mut s: PriorityQueueVector<i32, String> = PriorityQueueVector::new();
        assert_eq!(s.peek_min(), None);
        assert_eq!(s.is_empty(), true);
        s.insert(String::from("first"), 1);
        s.insert(String::from("second"), 2);
        s.insert(String::from("third"), 3);
        assert_eq!(s.peek_min(), Some(&String::from("first")));
        assert_eq!(s.pop_min(), Some(String::from("first")));
        assert_eq!(s.pop_min(), Some(String::from("second")));
        assert_eq!(s.pop_min(), Some(String::from("third")));
        assert_eq!(s.pop_min(), None);
        assert_eq!(s.peek_min(), None);
        s.insert(String::from("first"), 4);
        s.insert(String::from("second"), 5);
        s.insert(String::from("third"), 6);
        assert_eq!(s.peek_min(), Some(&String::from("first")));
        s.decr_key(&String::from("second"), 1);
        assert_eq!(s.pop_min(), Some(String::from("second")));
    }
}

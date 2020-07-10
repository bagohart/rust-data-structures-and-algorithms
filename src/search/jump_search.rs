use crate::search::linear_search;
use std::cmp::{self, Ordering};

// Slice must be ordered for this to work
pub fn jump_search<T: Ord + Eq>(arr: &[T], elem: &T, jump: usize) -> Option<usize> {
    assert!(jump > 0);

    let mut upper = 0;
    let mut lower;
    let len = arr.len();
    // Lots of off-by-one trickiness in here. I don't actually like this code o_O
    while upper < len - 1 {
        lower = upper;
        upper = cmp::min(upper + jump, len - 1);
        match arr[upper].cmp(elem) {
            Ordering::Equal => return Some(upper),
            Ordering::Greater => return linear_search::linear_search(&arr[lower..upper], elem),
            Ordering::Less => continue,
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::jump_search;

    #[test]
    fn basics() {
        let arr = [
            0, 1, 2, 4, 8, 9, 13, 27, 33, 34, 35, 36, 37, 40, 42, 53, 60, 71,
        ];
        let pos: Vec<usize> = (1..20)
            .map(|w| jump_search(&arr, &34, w).unwrap())
            .collect();
        pos.iter().all(|x| x == &9);
        let pos = jump_search(&arr, &34, 3);
        assert_eq!(pos, Some(9));
        let pos = jump_search(&arr, &1337, 3);
        assert_eq!(pos, None);
    }
}

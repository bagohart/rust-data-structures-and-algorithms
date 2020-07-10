use std::cmp::Ordering;
use std::fmt::Debug;

pub fn binary_search<T: Eq + Ord + Debug>(arr: &[T], elem: &T) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len() - 1;
    while left <= right {
        let mid = (left + right) / 2;
        println!("left={}, right={}, mid={}", left, right, mid);
        println!("arr[mid]={:?}", arr[mid]);
        match arr[mid].cmp(elem) {
            Ordering::Equal => return Some(mid),
            Ordering::Less => left = mid + 1,
            Ordering::Greater => right = mid - 1,
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::binary_search;

    #[test]
    fn basics() {
        let arr = [0, 1, 2, 3, 4, 5, 5, 6, 7, 9, 13, 20];
        let pos = binary_search(&arr, &9);
        assert_eq!(pos, Some(9));
        let pos = binary_search(&arr, &13);
        assert_eq!(pos, Some(10));
        let pos = binary_search(&arr, &3);
        assert_eq!(pos, Some(3));
        let pos = binary_search(&arr, &1337);
        assert_eq!(pos, None);
    }
}

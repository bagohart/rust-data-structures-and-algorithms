use std::fmt::Debug;

// merge does not work in-place, so we need unsafe rust tricks to implement this for not-Copy types.
// implement for copy types first, this should be easier
pub fn merge_sort_copy<T: Ord + Debug + Copy>(arr: &mut [T]) -> () {
    let len = arr.len();
    if len > 1 {
        let mid = len / 2; // I could round this up, so the arrays are more equal length... but there's no operator for that yet.
        let (left, right) = arr.split_at_mut(mid);
        merge_sort_copy(left);
        merge_sort_copy(right);
        let merged = merge_copy(left, right);
        arr.copy_from_slice(&merged);
    }
}

// must not overlap, but that's already enforced by Rust's mutable reference handling
// unchecked accesses to arrays would be faster but also more ugly
fn merge_copy<T: Ord + Debug + Copy>(arr1: &mut [T], arr2: &mut [T]) -> Vec<T> {
    let mut res: Vec<T> = Vec::with_capacity(arr1.len() + arr2.len());
    let mut left_slice = arr1;
    let mut right_slice = arr2;
    while !left_slice.is_empty() || !right_slice.is_empty() {
        if left_slice.is_empty() {
            res.push(*right_slice.first().unwrap());
            right_slice = right_slice.split_at_mut(1).1;
        } else if right_slice.is_empty() {
            res.push(*left_slice.first().unwrap());
            left_slice = left_slice.split_at_mut(1).1;
        } else {
            if left_slice[0] < right_slice[0] {
                res.push(*left_slice.first().unwrap());
                left_slice = left_slice.split_at_mut(1).1;
            } else {
                res.push(*right_slice.first().unwrap());
                right_slice = right_slice.split_at_mut(1).1;
            }
        }
    }
    res
}

// like the safe-version, but uses unsafe code to allow non-copy/clone types
pub fn merge_sort_unsafe<T: Ord + Debug>(arr: &mut [T]) -> () {
    let len = arr.len();
    if len > 1 {
        let mid = len / 2; // I could round this up, so the arrays are more equal length... but there's no operator for that yet.
        let (left, right) = arr.split_at_mut(mid);
        merge_sort_unsafe(left);
        merge_sort_unsafe(right);
        merge_unsafe(left, right);
    }
}

// todo. use magic unsafe code. uh oh.
fn merge_unsafe<T: Ord + Debug>(_arr1: &mut [T], _arr2: &mut [T]) -> () {
    unimplemented!();
}

#[cfg(test)]
mod tests {
    use super::merge_sort_copy;

    #[test]
    fn basics() {
        let unsorted_arr = [0, 20, 5, 7, 5, 9, 3, 4, 2, 13, 6, 1];
        let sorted_arr = [0, 1, 2, 3, 4, 5, 5, 6, 7, 9, 13, 20];

        let mut res = unsorted_arr.clone();
        merge_sort_copy(&mut res);
        assert_eq!(sorted_arr, res);

        let mut array_with_2 = [2, 0];
        merge_sort_copy(&mut array_with_2);
        assert_eq!([0, 2], array_with_2);
    }
}

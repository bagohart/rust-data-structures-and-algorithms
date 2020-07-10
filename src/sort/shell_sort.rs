use std::fmt::Debug;

pub fn shell_sort<T: Ord + Debug>(arr: &mut [T]) -> () {
    // could use other sequence, but this one looks nice.
    // for thorough testing, this would be passed as a parameter.
    let gaps = [701, 301, 132, 57, 23, 10, 4, 1];
    for gap in gaps.iter() {
        for i in *gap..arr.len() {
            let mut j = i;
            while j >= *gap && arr[j - *gap] > arr[j] {
                // shell sort with insertion sort as in most examples is impossible in safe rust
                // without indirection, so use swap to make it simple.
                arr.swap(j, j - *gap);
                j -= *gap;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::shell_sort;

    #[test]
    fn basics() {
        let unsorted_arr = [0, 20, 5, 7, 5, 9, 3, 4, 2, 13, 6, 1];
        let sorted_arr = [0, 1, 2, 3, 4, 5, 5, 6, 7, 9, 13, 20];

        let mut res = unsorted_arr.clone();
        shell_sort(&mut res);
        assert_eq!(sorted_arr, res);

        let mut array_with_2 = [2, 0];
        shell_sort(&mut array_with_2);
        assert_eq!([0, 2], array_with_2);
    }
}

use std::fmt::Debug;

pub fn insertion_sort<T: Ord + Debug>(arr: &mut [T]) -> () {
    for i in 1..arr.len() {
        let v = &arr[i];
        let mut j = i;
        while j > 0 && arr[j - 1] > *v {
            // find element. this could be done via binary search instead.
            j -= 1;
        }
        arr[j..i + 1].rotate_right(1);
    }
}

#[cfg(test)]
mod tests {
    use super::insertion_sort;

    #[test]
    fn basics() {
        let unsorted_arr = [0, 20, 5, 7, 5, 9, 3, 4, 2, 13, 6, 1];
        let sorted_arr = [0, 1, 2, 3, 4, 5, 5, 6, 7, 9, 13, 20];
        let mut res = unsorted_arr.clone();
        insertion_sort(&mut res);
        assert_eq!(sorted_arr, res);

        // let mut res = unsorted_arr.clone();
        // insertion_sort(&mut res);
        // assert_eq!(sorted_arr, res);

        // let mut res = unsorted_arr.clone();
        // insertion_sort(&mut res);
        // assert_eq!(sorted_arr, res);

        // let mut res = unsorted_arr.clone();
        // insertion_sort(&mut res);
        // assert_eq!(sorted_arr, res);

        let mut array_with_2 = [2, 0];
        insertion_sort(&mut array_with_2);
        assert_eq!([0, 2], array_with_2);
    }
}

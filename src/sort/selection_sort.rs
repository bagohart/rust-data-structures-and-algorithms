use std::fmt::Debug;

pub fn selection_sort_min<T: Ord + Debug>(arr: &mut [T]) -> () {
    for i in 0..arr.len() {
        let mut min = &arr[i];
        let mut min_index = i;
        for j in i..arr.len() {
            if *min > arr[j] {
                min = &arr[j];
                min_index = j;
            }
        }
        arr.swap(i, min_index);
    }
}

pub fn selection_sort_max<T: Ord + Debug>(arr: &mut [T]) -> () {
    for i in (0..arr.len()).rev() {
        let mut max = &arr[0];
        let mut max_index = 0;
        for j in 0..i + 1 {
            if *max < arr[j] {
                max = &arr[j];
                max_index = j;
            }
        }
        arr.swap(i, max_index);
    }
}

pub fn selection_sort_min_max<T: Ord + Debug>(arr: &mut [T]) -> () {
    let mut left = 0;
    let mut right = arr.len() - 1;
    while left < right {
        let mut min = &arr[left];
        let mut max = &arr[left];
        let mut min_index = left;
        let mut max_index = left;
        for i in left..right + 1 {
            if *max < arr[i] {
                max = &arr[i];
                max_index = i;
            }
            if *min > arr[i] {
                min = &arr[i];
                min_index = i;
            }
        }
        println!("\nmin={:?}, max={:?}, left={:?}, right={:?}", min, max, left, right);
        println!("arr before  ={:?}", arr);
        arr.swap(left, min_index);
        println!("arr min swap={:?}", arr);
        if max_index == left { 
            // This is a bit tricky. Not sure if this is correct in all cases.
            max_index = min_index;
        }
        arr.swap(right, max_index);
        println!("arr max swap={:?}", arr);
        left += 1;
        right -= 1;
    }
}

#[cfg(test)]
mod tests {
    use super::selection_sort_max;
    use super::selection_sort_min;
    use super::selection_sort_min_max;

    #[test]
    fn basics() {
        let unsorted_arr = [0, 20, 5, 7, 5, 9, 3, 4, 2, 13, 6, 1];
        let sorted_arr = [0, 1, 2, 3, 4, 5, 5, 6, 7, 9, 13, 20];

        let mut res = unsorted_arr.clone();
        selection_sort_min(&mut res);
        assert_eq!(sorted_arr, res);

        let mut res = unsorted_arr.clone();
        selection_sort_max(&mut res);
        assert_eq!(sorted_arr, res);

        let mut res = unsorted_arr.clone();
        selection_sort_min_max(&mut res);
        assert_eq!(sorted_arr, res);

        // let mut res = unsorted_arr.clone();
        // selection_sort(&mut res);
        // assert_eq!(sorted_arr, res);

        let mut array_with_2 = [2, 0];
        selection_sort_min(&mut array_with_2);
        assert_eq!([0, 2], array_with_2);

        let mut array_with_2 = [2, 0];
        selection_sort_max(&mut array_with_2);
        assert_eq!([0, 2], array_with_2);

        let mut array_with_2 = [2, 0];
        selection_sort_min_max(&mut array_with_2);
        assert_eq!([0, 2], array_with_2);
    }
}

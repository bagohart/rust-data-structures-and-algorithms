use std::fmt::Debug;

pub fn quick_sort<T: Ord + Debug + Copy>(arr: &mut [T]) -> () {
    if arr.is_empty() || arr.len() < 2 {
        return ();
    }

    let pivot_pos = partition(arr);
    let (left_arr, pivot_and_right_arr) = arr.split_at_mut(pivot_pos);
    let (_pivot, right_arr) = pivot_and_right_arr.split_at_mut(1);
    quick_sort(left_arr);
    quick_sort(right_arr);
}

// not sure how to do this without Copy types?
// this *should* be safe: pivot is never swapped by definition. But Rust doesn't know that.
// so this should be hackable with just a bit of unsafe Rust. yay. <- todo
fn partition<T: Ord + Debug + Copy>(arr: &mut [T]) -> usize {
    if arr.is_empty() {
        panic!("don't partition me if I'm empty!");
    }
    let pivot_pos = arr.len() - 1;
    let pivot = *arr.last().unwrap();

    let mut left = 0;
    let mut right = arr.len() - 1;
    loop {
        while left < right && arr[left] < pivot {
            left += 1;
        }
        while left < right && arr[right] >= pivot {
            right -= 1;
        }
        if left >= right {
            break;
        }
        arr.swap(left, right);
    }
    arr.swap(left, pivot_pos);
    left
}

#[cfg(test)]
mod tests {
    use super::quick_sort;

    #[test]
    fn basics() {
        let unsorted_arr = [0, 20, 5, 7, 5, 9, 3, 4, 2, 13, 6, 1];
        let sorted_arr = [0, 1, 2, 3, 4, 5, 5, 6, 7, 9, 13, 20];

        let mut res = unsorted_arr.clone();
        quick_sort(&mut res);
        assert_eq!(sorted_arr, res);

        let mut array_with_2 = [2, 0];
        quick_sort(&mut array_with_2);
        assert_eq!([0, 2], array_with_2);
    }
}

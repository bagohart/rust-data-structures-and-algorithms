// always has worse than worst case behaviour
// iterates as often as is sufficient, but that is more often than necessary!
pub fn bubble_sort_worse_than_worst_case<T: Ord>(arr: &mut [T]) -> () {
    for _ in 0..arr.len() {
        for i in 0..arr.len() - 1 {
            if arr[i] > arr[i + 1] {
                arr.swap(i, i + 1);
            }
        }
    }
}

// better than the first try, but still bad:
// does not detect early termination
// but shrinks the searched array on each iteration: in each iteration, an element bubbles to the current end,
// and then the current end is moved to the left
pub fn bubble_sort_worst_case<T: Ord>(arr: &mut [T]) -> () {
    for n in (0..arr.len()).rev() {
        for i in 0..n {
            if arr[i] > arr[i + 1] {
                arr.swap(i, i + 1);
            }
        }
    }
}

// like the last attempt, but aborts if in one iteration nothing was swapped
pub fn bubble_sort_detect_early_termination<T: Ord>(arr: &mut [T]) -> () {
    for n in (0..arr.len()).rev() {
        let mut swapped = false;
        for i in 0..n {
            if arr[i] > arr[i + 1] {
                arr.swap(i, i + 1);
                swapped = true;
            }
        }
        if !swapped {
            return;
        }
    }
}

// almost like the slides, but they seem broken for len = 2
// only sort the part of the list that is not yet sorted and terminate early if appropriate
// the swapped variable is subsumed in j, the border to the already sorted part
pub fn bubble_sort_best<T: Ord>(arr: &mut [T]) -> () {
    let mut n = arr.len() - 1;

    while n > 0 {
        let mut j = 0;
        for i in 0..n {
            if arr[i] > arr[i + 1] {
                arr.swap(i, i + 1);
                j = i + 1;
            }
        }
        n = j;
    }
}

#[cfg(test)]
mod tests {
    use super::bubble_sort_best;
    use super::bubble_sort_detect_early_termination;
    use super::bubble_sort_worse_than_worst_case;
    use super::bubble_sort_worst_case;

    #[test]
    fn basics() {
        let unsorted_arr = [0, 20, 5, 7, 5, 9, 3, 4, 2, 13, 6, 1];
        let sorted_arr = [0, 1, 2, 3, 4, 5, 5, 6, 7, 9, 13, 20];
        let mut res = unsorted_arr.clone();
        bubble_sort_worse_than_worst_case(&mut res);
        assert_eq!(sorted_arr, res);

        let mut res = unsorted_arr.clone();
        bubble_sort_worst_case(&mut res);
        assert_eq!(sorted_arr, res);

        let mut res = unsorted_arr.clone();
        bubble_sort_detect_early_termination(&mut res);
        assert_eq!(sorted_arr, res);

        let mut res = unsorted_arr.clone();
        bubble_sort_best(&mut res);
        assert_eq!(sorted_arr, res);

        let mut array_with_2 = [2, 0];
        bubble_sort_best(&mut array_with_2);
        assert_eq!([0, 2], array_with_2);
    }
}

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

pub fn merge_sort_unsafe<T: Ord + Debug>(arr: &mut [T]) -> () {
    let len = arr.len();
    if len > 1 {
        let mid = len / 2; // I could round this up, so the arrays are more equal length... but there's no operator for that yet.
        let (left, right) = arr.split_at_mut(mid);
        merge_sort_unsafe(left);
        merge_sort_unsafe(right);
        merge_unsafe(arr, mid);
    }
}

// I could reuse the BadLeak type from the quicksort algorithm here, and just push it around in vectors
// But that would be too easy. Not sure if it would be slower.
// ...
// actually maybe this is completely broken because of interior mutability.
// comparing might have side effects :)
// todo: think about if it really is. lol. because maybe it's not if things are not at all accessed any more later. hhm.
// ^ ok, I think it's ok. The things are copied away, and then they are not accessed anymore,
// so no ignored side-effects should be able to occur.
fn merge_unsafe<T: Ord + Debug>(arr: &mut [T], mid: usize) {
    let n = arr.len();
    assert!(n > mid);
    let len_left = mid;
    let len_right = n - mid;

    let mut sorted: Vec<T> = Vec::with_capacity(len_left + len_right);
    let mut top = sorted.as_mut_ptr();
    let (mut left_slice, mut right_slice) = arr.split_at_mut(mid);

    // copy the elements on the vector, but don't use push to avoid ownership
    // actually, we could use push, followed by .set_len(0) ... :)
    while !left_slice.is_empty() || !right_slice.is_empty() {
        if left_slice.is_empty() {
            // only elements from the right slice remain, copy all of them onto the vector
            unsafe {
                std::ptr::copy_nonoverlapping(right_slice.as_mut_ptr(), top, right_slice.len());
            }
            // top is invalid now, but it won't be used again
            break;
        } else if right_slice.is_empty() {
            // only elements from the left slice remain, copy all of them onto the vector
            unsafe {
                std::ptr::copy_nonoverlapping(left_slice.as_mut_ptr(), top, left_slice.len());
            }
            // top is invalid now, but it won't be used again
            break;
        } else {
            // <= needed for stability
            if left_slice[0] <= right_slice[0] {
                unsafe {
                    // I could use copy_nonoverlapping here too, but that seems overkill
                    std::ptr::write(top, std::ptr::read(left_slice.as_mut_ptr()));
                    top = top.add(1);
                }
                left_slice = left_slice.split_at_mut(1).1;
            } else {
                unsafe {
                    std::ptr::write(top, std::ptr::read(right_slice.as_mut_ptr()));
                    top = top.add(1);
                }
                right_slice = right_slice.split_at_mut(1).1;
            }
        }
    }

    // copy results back into original array. This cannot fail.
    // Note that we must sort the things in the vector without ownership. if we sort on the array with ownership,
    // then an element may be there twice, and then a panic comes and we get a double free.
    unsafe {
        std::ptr::copy_nonoverlapping(sorted.as_mut_ptr(), arr.as_mut_ptr(), n);
    }
}

// I would like to reopen the module from above. but how?
#[cfg(test)]
mod more_tests {
    use super::merge_sort_unsafe;

    #[test]
    fn basics() {
        let unsorted_arr = [0, 20, 5, 7, 5, 9, 3, 4, 2, 13, 6, 1];
        let sorted_arr = [0, 1, 2, 3, 4, 5, 5, 6, 7, 9, 13, 20];

        let mut res = unsorted_arr.clone();
        merge_sort_unsafe(&mut res);
        assert_eq!(sorted_arr, res);

        let mut array_with_2 = [2, 0];
        merge_sort_unsafe(&mut array_with_2);
        assert_eq!([0, 2], array_with_2);
    }
}

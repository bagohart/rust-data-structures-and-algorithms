use std::fmt::Debug;

// todo: without copy needs unsafe
// todo: could add lower and upper range. that would make array handling a bit more complicated though.
pub fn counting_sort_copy<T: Ord + Copy + Debug, KeyFunc>(
    arr: &mut [T],
    nr_keys: usize,
    by_key: KeyFunc,
) where
    KeyFunc: Fn(&T) -> usize,
{
    let n = arr.len();
    let mut sorted: Vec<Option<T>> = vec![None; n];
    let mut index: Vec<usize> = vec![0; nr_keys];

    for i in 0..n {
        let key = by_key(&arr[i]);
        assert!(key < nr_keys, "nr_keys was obviously too small!");
        index[key] += 1;
    }
    println!("index after first count={:?}", index);

    for i in 1..nr_keys {
        index[i] += index[i - 1];
    }
    // or:
    // let mut index: Vec<usize> = index
    //     .iter_mut()
    //     .scan(0usize, |sum, i| {
    //         *sum += *i;
    //         // println!("sum={}", sum);
    //         Some(*sum)
    //     })
    //     .collect();

    for i in (0..n).rev() {
        let key = by_key(&arr[i]);
        sorted[index[key] - 1] = Some(arr[i]);
        index[key] -= 1;
    }

    // write back to original slice
    for i in (0..n).rev() {
        arr[i] = sorted.pop().unwrap().unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::counting_sort_copy;

    #[test]
    fn basics() {
        //todo: is there a nicer way to write this without explicitly stating the length of the array?
        //^ no.
        let unsorted_arr = [0usize, 20, 5, 7, 5, 9, 3, 4, 2, 13, 6, 1];
        let sorted_arr = [0usize, 1, 2, 3, 4, 5, 5, 6, 7, 9, 13, 20];

        let mut res = unsorted_arr.clone();
        counting_sort_copy(&mut res, 22, |i| *i);
        assert_eq!(sorted_arr, res);

        let mut array_with_2 = [2, 0];
        counting_sort_copy(&mut array_with_2, 21, |i| *i);
        assert_eq!([0, 2], array_with_2);

        let unsorted_arr = [0usize, 2, 0, 2, 0, 0, 0, 1, 2, 1, 0, 1, 2, 1];
        let sorted_arr = [0usize, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2];

        let mut res = unsorted_arr.clone();
        counting_sort_copy(&mut res, 3, |i| *i);
        assert_eq!(sorted_arr, res);
    }
}

// works without Copy/Clone: Copy everything in a vector with ownership and back.
// actually I'm not sure how sound anything of this is. Although the > methods take a shared reference,
// there could be some interior mutability going on. This would be very bad. The same applies to the other 
// sorting functions where I did this.
// In this case, maybe it's better to just save the final indices and then copy it back and forth. hm.
//
// todo: think about this again with fresh eyes.
// ^ ok, this should be fine. The elements are copied, but not accessed.
// No methods are called on or with them. The copying happens only after any such access.
// Therefore, the objects cannot change and no changes are lost.
pub fn counting_sort_unsafe<T: Ord + Debug, KeyFunc>(arr: &mut [T], nr_keys: usize, by_key: KeyFunc)
where
    KeyFunc: Fn(&T) -> usize,
{
    let n = arr.len();
    // copy elements into this vector in the right order, but the vector doesn't get ownership
    let mut sorted_vec: Vec<T> = Vec::with_capacity(n);
    let sorted: &mut [T] = unsafe { std::slice::from_raw_parts_mut(sorted_vec.as_mut_ptr(), n) };
    let mut index: Vec<usize> = vec![0; nr_keys];

    for i in 0..n {
        let key = by_key(&arr[i]);
        assert!(key < nr_keys, "nr_keys was obviously too small!");
        index[key] += 1;
    }
    println!("index after first count={:?}", index);
    for i in 1..nr_keys {
        index[i] += index[i - 1];
    }

    for i in (0..n).rev() {
        let key = by_key(&arr[i]);
        unsafe {
            std::ptr::write(
                sorted.as_mut_ptr().add(index[key] - 1),
                std::ptr::read(arr.as_mut_ptr().add(i)),
            );
        }
        index[key] -= 1;
    }

    // copy back to original slice
    unsafe {
        std::ptr::copy_nonoverlapping(sorted.as_mut_ptr(), arr.as_mut_ptr(), n);
    }
}

#[cfg(test)]
mod more_tests {
    use super::counting_sort_unsafe;

    #[test]
    fn basics() {
        let unsorted_arr = [0usize, 20, 5, 7, 5, 9, 3, 4, 2, 13, 6, 1];
        let sorted_arr = [0usize, 1, 2, 3, 4, 5, 5, 6, 7, 9, 13, 20];

        let mut res = unsorted_arr.clone();
        counting_sort_unsafe(&mut res, 22, |i| *i);
        assert_eq!(sorted_arr, res);

        let mut array_with_2 = [2, 0];
        counting_sort_unsafe(&mut array_with_2, 21, |i| *i);
        assert_eq!([0, 2], array_with_2);

        let unsorted_arr = [0usize, 2, 0, 2, 0, 0, 0, 1, 2, 1, 0, 1, 2, 1];
        let sorted_arr = [0usize, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2];

        let mut res = unsorted_arr.clone();
        counting_sort_unsafe(&mut res, 3, |i| *i);
        assert_eq!(sorted_arr, res);
    }
}

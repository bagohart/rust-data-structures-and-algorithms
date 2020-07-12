use std::fmt::Debug;
use std::mem;
use std::ops::Deref;

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

pub fn quick_sort_unsafe_1<T: Ord + Debug>(arr: &mut [T]) -> () {
    if arr.is_empty() || arr.len() < 2 {
        return ();
    }

    let pivot_pos = partition_unsafe_1(arr);
    let (left_arr, pivot_and_right_arr) = arr.split_at_mut(pivot_pos);
    let (_pivot, right_arr) = pivot_and_right_arr.split_at_mut(1);
    quick_sort_unsafe_1(left_arr);
    quick_sort_unsafe_1(right_arr);
}

// This technique with a single read only pointer works here, since the element does not move.
// For other partition methods, it wouldn't. This might be a worthwhile challenge.
fn partition_unsafe_1<T: Ord + Debug>(arr: &mut [T]) -> usize {
    if arr.is_empty() {
        panic!("don't partition me if I'm empty!");
    }
    let pivot_pos = arr.len() - 1;
    let pivot = arr.last().unwrap() as *const T;

    let mut left = 0;
    let mut right = arr.len() - 1;
    loop {
        // The pivot is the rightmost element in the array, so it is usually not arr[left]
        // Exception: if on the first invocation, this loop walks left to the very end
        // In this case, the loop breaks, and the swap is a no-op.
        while left < right && &arr[left] < unsafe { &*pivot } {
            left += 1;
        }
        // if >= is implemented wrong, then arr[right] could point to the pivot after this loop.
        // Then the pivot is swapped away, which should never happen inside the loop.
        // However, this cannot lead to undefined behaviour, since there always is an element
        // in this position. The sort order is broken, of course, but we can't do anything about that anyway.
        while left < right && &arr[right] >= unsafe { &*pivot } {
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

// similar to quick_sort_unsafe_1, but stores the pivot element separately, using a newtype and mem::forget()
// todo: this is probably broken because of interior mutability. uh oh. think about this again.
// ^ ok, I think this is really broken. We compare the things with the copy of the pivot, but it is
// never written back, so any side effects there are lost.
pub fn quick_sort_unsafe_2<T: Ord + Debug>(arr: &mut [T]) -> () {
    if arr.is_empty() || arr.len() < 2 {
        return ();
    }

    let pivot_pos = partition_unsafe_2(arr);
    let (left_arr, pivot_and_right_arr) = arr.split_at_mut(pivot_pos);
    let (_pivot, right_arr) = pivot_and_right_arr.split_at_mut(1);
    quick_sort_unsafe_2(left_arr);
    quick_sort_unsafe_2(right_arr);
}

struct BadLeak<T> {
    elem: Option<T>,
}

impl<T> BadLeak<T> {
    fn new(elem: &T) -> Self {
        BadLeak {
            elem: unsafe { Some(std::ptr::read(elem as *const T)) },
        }
    }
}

impl<T> Drop for BadLeak<T> {
    fn drop(&mut self) {
        mem::forget(self.elem.take());
    }
}

impl<T> Deref for BadLeak<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.elem.as_ref().unwrap()
    }
}

fn partition_unsafe_2<T: Ord + Debug>(arr: &mut [T]) -> usize {
    if arr.is_empty() {
        panic!("don't partition me if I'm empty!");
    }
    let pivot_pos = arr.len() - 1;
    let pivot: BadLeak<T> = BadLeak::new(arr.last().unwrap());

    let mut left = 0;
    let mut right = arr.len() - 1;
    loop {
        // the pivot with which we compare here was actually copied away.
        // this is not actually necessary because we still use pivot_pos to keep track of it, but it works.
        // this is fun with unsafe Rust rather than reasonable.
        while left < right && &arr[left] <  &*pivot  {
            left += 1;
        }
        while left < right && &arr[right] >=  &*pivot  {
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
    use super::quick_sort_unsafe_1;
    use super::quick_sort_unsafe_2;

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

        let mut res = unsorted_arr.clone();
        quick_sort_unsafe_1(&mut res);
        assert_eq!(sorted_arr, res);

        let mut array_with_2 = [2, 0];
        quick_sort_unsafe_1(&mut array_with_2);
        assert_eq!([0, 2], array_with_2);

        let mut res = unsorted_arr.clone();
        quick_sort_unsafe_2(&mut res);
        assert_eq!(sorted_arr, res);

        let mut array_with_2 = [2, 0];
        quick_sort_unsafe_2(&mut array_with_2);
        assert_eq!([0, 2], array_with_2);
    }
}

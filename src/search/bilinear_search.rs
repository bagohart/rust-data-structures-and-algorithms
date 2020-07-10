pub fn bilinear_search<T: Eq + Ord>(arr: &[T], elem: &T) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len() - 1;
    while left < right {
        if &arr[left] == elem {
            return Some(left);
        } else if &arr[right] == elem {
            return Some(right);
        } else {
            left += 1;
            right -= 1;
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::bilinear_search;

    #[test]
    fn basics() {
        let arr = [0, 20, 5, 7, 5, 9, 3, 4, 2, 13, 6, 1];
        let pos = bilinear_search(&arr, &9);
        assert_eq!(pos, Some(5));
        let pos = bilinear_search(&arr, &13);
        assert_eq!(pos, Some(9));
        let pos = bilinear_search(&arr, &1337);
        assert_eq!(pos, None);
    }
}

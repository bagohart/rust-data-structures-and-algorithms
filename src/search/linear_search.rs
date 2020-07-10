// Does not work for float values because NaN :) u_U
pub fn linear_search<T: Eq + Ord>(arr: &[T], elem: &T) -> Option<usize> {
    for i in 0..arr.len() {
        if arr[i] == *elem {
            return Some(i);
        }
    }
    return None;
}

#[cfg(test)]
mod tests {
    use super::linear_search;

    #[test]
    fn basics() {
        let arr = [0, 20, 5, 7, 5, 9, 3, 4, 2, 13, 6, 1];
        let pos = linear_search(&arr, &9);
        assert_eq!(pos, Some(5));
        let pos = linear_search(&arr, &1337);
        assert_eq!(pos, None);
    }
}

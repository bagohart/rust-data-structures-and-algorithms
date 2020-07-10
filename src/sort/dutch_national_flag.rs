#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum FlagColor {
    Red,
    White,
    Blue,
}

// slides seem broken:
// 0 < i <= r  red
// r < i < u white
// u <= i < b unknown
// b <= i <= n blue
//
// try this instead: (could contain off by one errors...)
// red, white, unknown, blue regions
// red: 0 <= i < r
// white: r < i < u
// unknown: u <= i < b
// blue: b <= i < n
// 0 <= r <= u <= b <= n
pub fn dutch_national_flag_sort(arr: &mut [FlagColor]) -> () {
    let n = arr.len();
    let mut r = 0; // empty red region
    let mut b = n; // empty blue region
    let mut u = 0; // unknown region spans the whole array, empty white region

    // unknown region not empty yet
    while u < b {
        match arr[u] {
            FlagColor::Red => {
                // move red element to end of red region, possibly swap white element to end of white region
                arr.swap(u, r);
                r += 1; // red region got bigger
                u += 1; // unknown region got smaller, white region was moved (if it existed)
            }
            FlagColor::White => {
                u += 1; // white region got bigger, element already at correct position
            }
            FlagColor::Blue => {
                arr.swap(u, b - 1); // move element to beginning of blue region
                b -= 1;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::dutch_national_flag_sort;
    use super::FlagColor;

    #[test]
    fn basics() {
        let unsorted_arr = [
            FlagColor::Red,
            FlagColor::White,
            FlagColor::Blue,
            FlagColor::White,
            FlagColor::White,
            FlagColor::Blue,
            FlagColor::Red,
            FlagColor::Blue,
            FlagColor::Blue,
            FlagColor::Red,
        ];
        let sorted_arr = [
            FlagColor::Red,
            FlagColor::Red,
            FlagColor::Red,
            FlagColor::White,
            FlagColor::White,
            FlagColor::White,
            FlagColor::Blue,
            FlagColor::Blue,
            FlagColor::Blue,
            FlagColor::Blue,
        ];

        let mut res = unsorted_arr.clone();
        dutch_national_flag_sort(&mut res);
        assert_eq!(sorted_arr, res);
    }
}

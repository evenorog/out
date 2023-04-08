#[test]
fn slice_max() {
    let mut v = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let max = out::slice::max(&mut v, 5);
    assert_eq!(max, [9, 8, 7, 6, 5]);
}

#[test]
fn slice_min() {
    let mut v = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let min = out::slice::min(&mut v, 5);
    assert_eq!(min, [0, 1, 2, 3, 4]);
}

#[test]
#[cfg(feature = "alloc")]
fn iter_max() {
    let v = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let max = out::iter::max(v, 5);
    assert_eq!(max, [9, 8, 7, 6, 5]);
}

#[test]
#[cfg(feature = "alloc")]
fn iter_min() {
    let v = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let min = out::iter::min(v, 5);
    assert_eq!(min, [0, 1, 2, 3, 4]);
}

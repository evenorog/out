#[test]
fn slice_max() {
    let mut v = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let max = out::slice::max(&mut v, 5);
    max.sort();
    assert_eq!(max, [5, 6, 7, 8, 9]);
}

#[test]
fn slice_min() {
    let mut v = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let min = out::slice::min(&mut v, 5);
    min.sort();
    assert_eq!(min, [0, 1, 2, 3, 4]);
}

#[test]
fn iter_max() {
    let v = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut max = out::iter::max(v, 5);
    max.sort();
    assert_eq!(max, [5, 6, 7, 8, 9]);
}

#[test]
fn iter_min() {
    let v = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut min = out::iter::min(v, 5);
    min.sort();
    assert_eq!(min, [0, 1, 2, 3, 4]);
}

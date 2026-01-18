fn main(x: pub u64, y: pub u64) -> pub u64 {
    let mut z: u64 = 0;
    if y < 15 {
        z = 2 *x;
    } else {
        z = 3 + x;
    }
    z
}


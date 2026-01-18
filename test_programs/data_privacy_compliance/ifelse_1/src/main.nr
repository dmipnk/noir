fn main(x: pub u64, y: pub u64) -> pub u64 {
    let mut z: u64 = 0;
    if y < 10 {
        z = 2*x;
    } else if y < 20{
        z = 5;
    } else {
        z = 10;
    }
    z
}

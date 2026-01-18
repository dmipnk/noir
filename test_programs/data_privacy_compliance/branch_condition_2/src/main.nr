fn main(x: pub u64, y: pub u64) -> pub u64{
    let mut z: u64 = 0;
    if y < 20 {
        if y < 10 {
            z = 5;
        } else if (x == 10) & (y < 5){
            z = 10;
        } else {
            z = 7;
        }
    } else {
        z = 100;
    }
    z
}


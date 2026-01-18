fn main(x: u64, y: pub u64, a: pub u64) -> pub u64{
    let mut z: u64 = 0;
    if y < 15 {
        if a <30{
            z =5;
        } else if a < 40{
            z = 10; 
        } else if a < 60 {
            z = 3*x;
        } else {
            z = 20;
        }
    } else if y < 30{
        z = 5 -x;
    } else {
        z = 100;
    }
    z
}


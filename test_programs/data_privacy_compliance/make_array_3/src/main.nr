fn main(x: pub u16) -> pub [u16; 30] {
    let mut arr: [u16; 30] = [0 ;30];
    arr[15] = x;
    arr
}


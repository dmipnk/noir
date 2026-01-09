fn main(arr: [u8;7]) -> pub u8{
    let mut sum:u8 =0;
    for i in 0..6{
        sum += arr[i];
    }
    sum
}

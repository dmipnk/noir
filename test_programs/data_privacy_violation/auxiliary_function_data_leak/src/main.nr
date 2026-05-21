fn func(key:u32) -> u8{
    let mut res = key as u8;
    res += 42;
    res
}

fn main(key: u32) -> pub u8{
    let x:u8 = func(key*4);
    x
}

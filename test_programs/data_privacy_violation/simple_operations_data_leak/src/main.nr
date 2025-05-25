fn main(x: Field, y: pub Field,a: i32,b: pub i32) -> pub ( Field,  u16){
    let mut n = a-b;
    let mut d = x+y;
    let mut z = x*x;
    let mut f = y*x;
    d -= z+f;
    n += 2;
    n = n / (a*b);
    (d,n as u16)
}
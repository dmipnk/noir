fn main(inputs: pub [u8; 4]) -> pub [u8; 32] {
    let hash = std::hash::blake3(inputs);
    hash
}

fn main(inputs: [u8; 4]) -> pub [u8; 32] {
    let hash = std::hash::blake2s(inputs);
    hash
}

fn main(inputs:  [u64; 25]) -> pub [u64; 25] {
    let state = std::hash::keccakf1600(inputs);
    state
}


fn main(inputs: pub [Field; 4]) -> pub [Field;4] {

    let result = std::hash::poseidon2_permutation(inputs,4);

    result
}


fn main(inputs: [u8; 4], iv: pub [u8; 16], key: pub [u8; 16]) -> pub [u8; 16] {
    let ciphertext = std::aes128::aes128_encrypt(inputs, iv, key); // In this case, the output length will be 16 bytes.
    ciphertext
}

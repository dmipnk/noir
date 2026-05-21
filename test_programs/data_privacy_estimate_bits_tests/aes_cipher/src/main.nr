fn main(x: u8, inputs: [u8; 4], iv: pub [u8; 16], mut key: pub [u8; 16]) -> pub [u8; 16] {
    key[4] = x;
    let ciphertext = std::aes128::aes128_encrypt(inputs, iv, key); 
    ciphertext
}

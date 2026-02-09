use omega_core::{recover_valid_prefix, Frame};

#[test]
fn recovers_valid_prefix() {
    let f1 = Frame::new(1, vec![1, 2, 3]).encode();
    let f2 = Frame::new(2, vec![4, 5]).encode();
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&f1);
    bytes.extend_from_slice(&f2);
    bytes.extend_from_slice(&[0u8; 5]);

    let valid = recover_valid_prefix(&bytes);
    assert_eq!(valid, f1.len() + f2.len());
}

//! Small safe SHA-256 implementation used by standalone blocking tests.
//!
//! The crate already pins `sha2`; this local implementation keeps the WPR2
//! module directly compilable before `lib.rs` integration and is covered by
//! standard vectors plus Python blocking fingerprints.
// SPDX-License-Identifier: LGPL-3.0-or-later

const INITIAL: [u32; 8] = [
    0x6a09_e667,
    0xbb67_ae85,
    0x3c6e_f372,
    0xa54f_f53a,
    0x510e_527f,
    0x9b05_688c,
    0x1f83_d9ab,
    0x5be0_cd19,
];

const ROUND: [u32; 64] = [
    0x428a_2f98,
    0x7137_4491,
    0xb5c0_fbcf,
    0xe9b5_dba5,
    0x3956_c25b,
    0x59f1_11f1,
    0x923f_82a4,
    0xab1c_5ed5,
    0xd807_aa98,
    0x1283_5b01,
    0x2431_85be,
    0x550c_7dc3,
    0x72be_5d74,
    0x80de_b1fe,
    0x9bdc_06a7,
    0xc19b_f174,
    0xe49b_69c1,
    0xefbe_4786,
    0x0fc1_9dc6,
    0x240c_a1cc,
    0x2de9_2c6f,
    0x4a74_84aa,
    0x5cb0_a9dc,
    0x76f9_88da,
    0x983e_5152,
    0xa831_c66d,
    0xb003_27c8,
    0xbf59_7fc7,
    0xc6e0_0bf3,
    0xd5a7_9147,
    0x06ca_6351,
    0x1429_2967,
    0x27b7_0a85,
    0x2e1b_2138,
    0x4d2c_6dfc,
    0x5338_0d13,
    0x650a_7354,
    0x766a_0abb,
    0x81c2_c92e,
    0x9272_2c85,
    0xa2bf_e8a1,
    0xa81a_664b,
    0xc24b_8b70,
    0xc76c_51a3,
    0xd192_e819,
    0xd699_0624,
    0xf40e_3585,
    0x106a_a070,
    0x19a4_c116,
    0x1e37_6c08,
    0x2748_774c,
    0x34b0_bcb5,
    0x391c_0cb3,
    0x4ed8_aa4a,
    0x5b9c_ca4f,
    0x682e_6ff3,
    0x748f_82ee,
    0x78a5_636f,
    0x84c8_7814,
    0x8cc7_0208,
    0x90be_fffa,
    0xa450_6ceb,
    0xbef9_a3f7,
    0xc671_78f2,
];

#[derive(Clone, Debug)]
pub(super) struct Sha256 {
    state: [u32; 8],
    block: [u8; 64],
    block_len: usize,
    byte_len: u64,
}

impl Sha256 {
    pub(super) const fn new() -> Self {
        Self {
            state: INITIAL,
            block: [0; 64],
            block_len: 0,
            byte_len: 0,
        }
    }

    pub(super) fn update(&mut self, mut input: &[u8]) {
        self.byte_len = self
            .byte_len
            .saturating_add(u64::try_from(input.len()).unwrap_or(u64::MAX));
        if self.block_len != 0 {
            let take = (64 - self.block_len).min(input.len());
            self.block[self.block_len..self.block_len + take].copy_from_slice(&input[..take]);
            self.block_len += take;
            input = &input[take..];
            if self.block_len < 64 {
                return;
            }
            let block = self.block;
            self.compress(&block);
            self.block_len = 0;
        }
        while input.len() >= 64 {
            let mut block = [0_u8; 64];
            block.copy_from_slice(&input[..64]);
            self.compress(&block);
            input = &input[64..];
        }
        self.block[..input.len()].copy_from_slice(input);
        self.block_len = input.len();
    }

    pub(super) fn finalize(mut self) -> [u8; 32] {
        let bit_len = self.byte_len.wrapping_mul(8);
        self.block[self.block_len] = 0x80;
        self.block_len += 1;
        if self.block_len > 56 {
            self.block[self.block_len..].fill(0);
            let block = self.block;
            self.compress(&block);
            self.block = [0; 64];
        } else {
            self.block[self.block_len..56].fill(0);
        }
        self.block[56..64].copy_from_slice(&bit_len.to_be_bytes());
        let block = self.block;
        self.compress(&block);
        let mut output = [0_u8; 32];
        for (chunk, value) in output.chunks_exact_mut(4).zip(self.state) {
            chunk.copy_from_slice(&value.to_be_bytes());
        }
        output
    }

    #[allow(clippy::many_single_char_names)]
    fn compress(&mut self, block: &[u8; 64]) {
        let mut words = [0_u32; 64];
        for (index, chunk) in block.chunks_exact(4).enumerate() {
            let bytes = [chunk[0], chunk[1], chunk[2], chunk[3]];
            words[index] = u32::from_be_bytes(bytes);
        }
        for index in 16..64 {
            let left = words[index - 15];
            let right = words[index - 2];
            let s0 = left.rotate_right(7) ^ left.rotate_right(18) ^ (left >> 3);
            let s1 = right.rotate_right(17) ^ right.rotate_right(19) ^ (right >> 10);
            words[index] = words[index - 16]
                .wrapping_add(s0)
                .wrapping_add(words[index - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = self.state;
        for index in 0..64 {
            let big1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let choose = (e & f) ^ ((!e) & g);
            let first = h
                .wrapping_add(big1)
                .wrapping_add(choose)
                .wrapping_add(ROUND[index])
                .wrapping_add(words[index]);
            let big0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let second = big0.wrapping_add(majority);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(first);
            d = c;
            c = b;
            b = a;
            a = first.wrapping_add(second);
        }
        for (target, value) in self.state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *target = target.wrapping_add(value);
        }
    }
}

#[cfg(test)]
pub(super) fn digest(input: &[u8]) -> [u8; 32] {
    let mut digest = Sha256::new();
    digest.update(input);
    digest.finalize()
}

pub(super) fn hex(value: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(value.len() * 2);
    for byte in value {
        output.push(char::from(DIGITS[usize::from(byte >> 4)]));
        output.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    output
}

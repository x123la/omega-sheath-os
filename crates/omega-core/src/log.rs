use std::fs::File;
use memmap2::Mmap;
use crc32fast::Hasher as CrcHasher;
use serde::{Deserialize, Serialize};

pub const OMEGA_MAGIC: [u8; 8] = [b'O', b'M', b'E', b'G', b'A', 0, 1, 0];

/// A zero-copy view into an OMEGA log file using memory mapping.
pub struct OmegaLogView {
    mmap: Mmap,
    header: OmegaFileHeader,
}

impl OmegaLogView {
    pub fn open(file: &File) -> anyhow::Result<Self> {
        let mmap = unsafe { Mmap::map(file)? };
        if mmap.len() < 64 {
            anyhow::bail!("log file too small for header");
        }
        let header = OmegaFileHeader::decode(&mmap[0..64])
            .map_err(|e| anyhow::anyhow!("header error: {e}"))?;
        
        Ok(Self { mmap, header })
    }

    pub fn header(&self) -> &OmegaFileHeader {
        &self.header
    }

    /// Returns a zero-copy iterator over valid frames in the log.
    pub fn iter_frames(&self) -> FrameIterator<'_> {
        FrameIterator {
            data: &self.mmap[64..],
            off: 0,
        }
    }
}

pub struct FrameIterator<'a> {
    data: &'a [u8],
    off: usize,
}

impl<'a> Iterator for FrameIterator<'a> {
    type Item = &'a [u8]; // Returns the raw payload slice (zero-copy)

    fn next(&mut self) -> Option<Self::Item> {
        if self.off + 12 > self.data.len() {
            return None;
        }
        let len = u32::from_le_bytes(self.data[self.off..self.off+4].try_into().unwrap()) as usize;
        if len < 12 || self.off + len > self.data.len() {
            return None;
        }

        let crc = u32::from_le_bytes(self.data[self.off+4..self.off+8].try_into().unwrap());
        let frame_type = u16::from_le_bytes(self.data[self.off+8..self.off+10].try_into().unwrap());
        let res = u16::from_le_bytes(self.data[self.off+10..self.off+12].try_into().unwrap());
        let payload = &self.data[self.off+12..self.off+len];

        // Validation (Still necessary, but doesn't copy the payload)
        let mut h = CrcHasher::new();
        h.update(&frame_type.to_le_bytes());
        h.update(&res.to_le_bytes());
        h.update(payload);
        if h.finalize() != crc {
            return None;
        }

        self.off += len;
        Some(payload)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OmegaFileHeader {
    pub magic: [u8; 8],
    pub schema_version: u16,
    pub endian_flag: u8,
    pub hash_alg_id: u8,
    pub reserved0: [u8; 14],
    pub schema_hash: [u8; 32],
    pub reserved1: [u8; 6],
}

impl OmegaFileHeader {
    pub fn new(schema_version: u16, schema_hash: [u8; 32]) -> Self {
        Self {
            magic: OMEGA_MAGIC,
            schema_version,
            endian_flag: 1,
            hash_alg_id: 1,
            reserved0: [0; 14],
            schema_hash,
            reserved1: [0; 6],
        }
    }

    pub fn encode(&self) -> [u8; 64] {
        let mut out = [0u8; 64];
        out[0..8].copy_from_slice(&self.magic);
        out[8..10].copy_from_slice(&self.schema_version.to_le_bytes());
        out[10] = self.endian_flag;
        out[11] = self.hash_alg_id;
        out[12..26].copy_from_slice(&self.reserved0);
        out[26..58].copy_from_slice(&self.schema_hash);
        out[58..64].copy_from_slice(&self.reserved1);
        out
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() < 64 {
            return Err("header too short".to_string());
        }
        let mut magic = [0u8; 8];
        magic.copy_from_slice(&bytes[0..8]);
        let schema_version = u16::from_le_bytes([bytes[8], bytes[9]]);
        let endian_flag = bytes[10];
        let hash_alg_id = bytes[11];
        let mut reserved0 = [0u8; 14];
        reserved0.copy_from_slice(&bytes[12..26]);
        let mut schema_hash = [0u8; 32];
        schema_hash.copy_from_slice(&bytes[26..58]);
        let mut reserved1 = [0u8; 6];
        reserved1.copy_from_slice(&bytes[58..64]);

        Ok(Self {
            magic,
            schema_version,
            endian_flag,
            hash_alg_id,
            reserved0,
            schema_hash,
            reserved1,
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Frame {
    pub frame_len: u32,
    pub frame_crc32: u32,
    pub frame_type: u16,
    pub reserved: u16,
    pub frame_payload: Vec<u8>,
}

impl Frame {
    pub fn new(frame_type: u16, payload: Vec<u8>) -> Self {
        let frame_len = (12 + payload.len()) as u32;
        let mut crc_hasher = CrcHasher::new();
        crc_hasher.update(&frame_type.to_le_bytes());
        crc_hasher.update(&0u16.to_le_bytes());
        crc_hasher.update(&payload);
        let frame_crc32 = crc_hasher.finalize();

        Self {
            frame_len,
            frame_crc32,
            frame_type,
            reserved: 0,
            frame_payload: payload,
        }
    }

    pub fn validate_crc(&self) -> bool {
        let mut crc_hasher = CrcHasher::new();
        crc_hasher.update(&self.frame_type.to_le_bytes());
        crc_hasher.update(&self.reserved.to_le_bytes());
        crc_hasher.update(&self.frame_payload);
        crc_hasher.finalize() == self.frame_crc32
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.frame_len as usize);
        out.extend_from_slice(&self.frame_len.to_le_bytes());
        out.extend_from_slice(&self.frame_crc32.to_le_bytes());
        out.extend_from_slice(&self.frame_type.to_le_bytes());
        out.extend_from_slice(&self.reserved.to_le_bytes());
        out.extend_from_slice(&self.frame_payload);
        out
    }
}

pub fn recover_valid_prefix(bytes: &[u8]) -> usize {
    let mut off = 0usize;
    while off + 12 <= bytes.len() {
        let frame_len = u32::from_le_bytes(bytes[off..off + 4].try_into().unwrap()) as usize;
        if frame_len < 12 || off + frame_len > bytes.len() {
            break;
        }
        let crc = u32::from_le_bytes(bytes[off + 4..off + 8].try_into().unwrap());
        let frame_type = u16::from_le_bytes(bytes[off + 8..off + 10].try_into().unwrap());
        let reserved = u16::from_le_bytes(bytes[off + 10..off + 12].try_into().unwrap());
        let payload = &bytes[off + 12..off + frame_len];

        let mut h = CrcHasher::new();
        h.update(&frame_type.to_le_bytes());
        h.update(&reserved.to_le_bytes());
        h.update(payload);
        if h.finalize() != crc {
            break;
        }
        off += frame_len;
    }
    off
}

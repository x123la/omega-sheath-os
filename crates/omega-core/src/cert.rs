use std::time::{SystemTime, UNIX_EPOCH};

use anyhow::Context;
use ed25519_dalek::{Signer, SigningKey, Verifier, VerifyingKey};
use rand::rngs::StdRng;
use rand::{RngCore, SeedableRng};
use serde::{Deserialize, Serialize};

use crate::{hash_bytes, hash_ids, CheckerResult};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CertType {
    Merge = 1,
    Obstruction = 2,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MergeBody {
    pub merged_state_hash: [u8; 32],
    pub frontier_digest: [u8; 32],
    pub accepted_count: u32,
    pub witness_hash: [u8; 32],
    pub replay_seed: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ObstructionBody {
    pub conflict_set_len: u16,
    pub conflict_set: Vec<u128>,
    pub conflicting_payload_hashes: Vec<[u8; 32]>,
    pub violated_predicate_id: u32,
    pub witness_hash: [u8; 32],
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertificateEnvelope {
    pub cert_id: u128,
    pub cert_type: CertType,
    pub trace_root_hash: [u8; 32],
    pub checker_version: (u16, u16, u16),
    pub schema_version: u16,
    pub batch_id: u64,
    pub created_at_ns: u64,
    pub issuer_key_id: [u8; 16],
    // NEW: Rigid binary body instead of dynamic JSON
    pub body_bytes: Vec<u8>,
    pub body_hash: [u8; 32],
    pub signature: Vec<u8>,
    pub prev_cert_hash: [u8; 32],
    // NEW: BFT Quorum Signatures (Placeholder for perfect consensus)
    pub quorum_signatures: Vec<Vec<u8>>,
}

impl CertificateEnvelope {
    pub fn verify(&self, key: &VerifyingKey, quorum_keys: &[VerifyingKey], quorum_size: usize) -> anyhow::Result<()> {
        let calc_body_hash = hash_bytes(&self.body_bytes);
        if calc_body_hash != self.body_hash {
            anyhow::bail!("body hash mismatch");
        }
        let msg = envelope_message(self)?;
        let sig_bytes: [u8; 64] = self
            .signature
            .as_slice()
            .try_into()
            .map_err(|_| anyhow::anyhow!("signature length must be 64"))?;
        let sig = ed25519_dalek::Signature::from_bytes(&sig_bytes);
        key.verify(&msg, &sig)
            .with_context(|| "issuer signature verification failed")?;

        // BFT Quorum Check
        if quorum_size > 0 {
            let mut valid_votes = 0;
            for (i, q_sig_bytes) in self.quorum_signatures.iter().enumerate() {
                if i >= quorum_keys.len() { break; }
                let q_sig = ed25519_dalek::Signature::from_bytes(
                    q_sig_bytes.as_slice().try_into().map_err(|_| anyhow::anyhow!("bad quorum sig"))?
                );
                if quorum_keys[i].verify(&msg, &q_sig).is_ok() {
                    valid_votes += 1;
                }
            }
            if valid_votes < quorum_size {
                anyhow::bail!("BFT failure: quorum size {} not reached (valid votes: {})", quorum_size, valid_votes);
            }
        }
        Ok(())
    }
}

pub fn derive_signing_key(seed: u64) -> SigningKey {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut sk = [0u8; 32];
    rng.fill_bytes(&mut sk);
    SigningKey::from_bytes(&sk)
}

pub fn issuer_key_id(verifying_key: &VerifyingKey) -> [u8; 16] {
    let full = hash_bytes(&verifying_key.to_bytes());
    let mut out = [0u8; 16];
    out.copy_from_slice(&full[..16]);
    out
}

pub fn cert_hash(envelope: &CertificateEnvelope) -> anyhow::Result<[u8; 32]> {
    let bytes = envelope_message(envelope)?;
    Ok(hash_bytes(&bytes))
}

pub fn build_certificate(
    result: &CheckerResult,
    batch_id: u64,
    checker_version: (u16, u16, u16),
    schema_version: u16,
    replay_seed: u64,
    issuer_key: &SigningKey,
    prev_cert_hash: [u8; 32],
) -> anyhow::Result<CertificateEnvelope> {
    let verifying = issuer_key.verifying_key();
    let key_id = issuer_key_id(&verifying);

    let mut cert_id_rng = rand::rngs::StdRng::seed_from_u64(batch_id ^ replay_seed.rotate_left(13));
    let cert_id = cert_id_rng.next_u64() as u128 | ((cert_id_rng.next_u64() as u128) << 64);

    let (cert_type, body_bytes, trace_root_hash) = match result {
        CheckerResult::Merge {
            merged_state_hash,
            accepted_event_ids,
            witness_hash,
            ..
        } => {
            let mut buf = Vec::new();
            buf.extend_from_slice(merged_state_hash);
            let frontier_digest = hash_ids(accepted_event_ids);
            buf.extend_from_slice(&frontier_digest);
            buf.extend_from_slice(&(accepted_event_ids.len() as u32).to_le_bytes());
            buf.extend_from_slice(witness_hash);
            buf.extend_from_slice(&replay_seed.to_le_bytes());
            (CertType::Merge, buf, frontier_digest)
        }
        CheckerResult::Obstruction {
            conflict_set,
            conflicting_payload_hashes,
            violated_predicate_id,
            witness_hash,
        } => {
            let mut c = conflict_set.clone();
            c.sort_unstable();
            let mut buf = Vec::new();
            buf.extend_from_slice(&(c.len() as u32).to_le_bytes());
            for id in &c { buf.extend_from_slice(&id.to_le_bytes()); }
            buf.extend_from_slice(&(conflicting_payload_hashes.len() as u32).to_le_bytes());
            for h in conflicting_payload_hashes { buf.extend_from_slice(h); }
            buf.extend_from_slice(&violated_predicate_id.to_le_bytes());
            buf.extend_from_slice(witness_hash);
            (CertType::Obstruction, buf, hash_ids(&c))
        }
    };

    let body_hash = hash_bytes(&body_bytes);

    let mut env = CertificateEnvelope {
        cert_id,
        cert_type,
        trace_root_hash,
        checker_version,
        schema_version,
        batch_id,
        created_at_ns: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos() as u64,
        issuer_key_id: key_id,
        body_bytes,
        body_hash,
        signature: vec![0; 64],
        prev_cert_hash,
        quorum_signatures: Vec::new(),
    };

    let msg = envelope_message(&env)?;
    env.signature = issuer_key.sign(&msg).to_bytes().to_vec();
    Ok(env)
}

fn envelope_message(env: &CertificateEnvelope) -> anyhow::Result<Vec<u8>> {
    let mut data = Vec::new();
    data.extend_from_slice(&env.cert_id.to_le_bytes());
    data.extend_from_slice(&(env.cert_type.clone() as u8).to_le_bytes());
    data.extend_from_slice(&env.trace_root_hash);
    data.extend_from_slice(&env.checker_version.0.to_le_bytes());
    data.extend_from_slice(&env.checker_version.1.to_le_bytes());
    data.extend_from_slice(&env.checker_version.2.to_le_bytes());
    data.extend_from_slice(&env.schema_version.to_le_bytes());
    data.extend_from_slice(&env.batch_id.to_le_bytes());
    data.extend_from_slice(&env.created_at_ns.to_le_bytes());
    data.extend_from_slice(&env.issuer_key_id);
    data.extend_from_slice(&env.body_hash);
    data.extend_from_slice(&env.prev_cert_hash);
    Ok(data)
}

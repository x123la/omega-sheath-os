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
    pub body: serde_json::Value,
    pub body_hash: [u8; 32],
    pub signature: Vec<u8>,
    pub prev_cert_hash: [u8; 32],
}

impl CertificateEnvelope {
    pub fn verify(&self, key: &VerifyingKey) -> anyhow::Result<()> {
        let body_bytes = serde_json::to_vec(&self.body)?;
        let calc_body_hash = hash_bytes(&body_bytes);
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
            .with_context(|| "signature verification failed")?;
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
    let bytes = serde_json::to_vec(envelope)?;
    Ok(hash_bytes(&bytes))
}

pub fn build_certificate(
    result: &CheckerResult,
    batch_id: u64,
    checker_version: (u16, u16, u16),
    schema_version: u16,
    replay_seed: u64,
    prev_cert_hash: [u8; 32],
) -> anyhow::Result<CertificateEnvelope> {
    let signing = derive_signing_key(replay_seed ^ batch_id);
    let verifying = signing.verifying_key();
    let key_id = issuer_key_id(&verifying);

    let mut cert_id_rng = StdRng::seed_from_u64(batch_id ^ replay_seed.rotate_left(13));
    let cert_id = cert_id_rng.next_u64() as u128 | ((cert_id_rng.next_u64() as u128) << 64);

    let (cert_type, body_json, trace_root_hash) = match result {
        CheckerResult::Merge {
            merged_state_hash,
            accepted_event_ids,
            witness_hash,
            ..
        } => {
            let body = MergeBody {
                merged_state_hash: *merged_state_hash,
                frontier_digest: hash_ids(accepted_event_ids),
                accepted_count: accepted_event_ids.len() as u32,
                witness_hash: *witness_hash,
                replay_seed,
            };
            (
                CertType::Merge,
                serde_json::to_value(body)?,
                hash_ids(accepted_event_ids),
            )
        }
        CheckerResult::Obstruction {
            conflict_set,
            violated_predicate_id,
            witness_hash,
        } => {
            let mut c = conflict_set.clone();
            c.sort_unstable();
            let body = ObstructionBody {
                conflict_set_len: c.len() as u16,
                conflict_set: c.clone(),
                violated_predicate_id: *violated_predicate_id,
                witness_hash: *witness_hash,
            };
            (
                CertType::Obstruction,
                serde_json::to_value(body)?,
                hash_ids(&c),
            )
        }
    };

    let body_bytes = serde_json::to_vec(&body_json)?;
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
        body: body_json,
        body_hash,
        signature: vec![0; 64],
        prev_cert_hash,
    };

    let msg = envelope_message(&env)?;
    env.signature = signing.sign(&msg).to_bytes().to_vec();
    Ok(env)
}

fn envelope_message(env: &CertificateEnvelope) -> anyhow::Result<Vec<u8>> {
    let tuple = (
        env.cert_id,
        &env.cert_type,
        env.trace_root_hash,
        env.checker_version,
        env.schema_version,
        env.batch_id,
        env.created_at_ns,
        env.issuer_key_id,
        &env.body,
        env.body_hash,
        env.prev_cert_hash,
    );
    Ok(serde_json::to_vec(&tuple)?)
}

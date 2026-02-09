use blake3::Hasher;
use serde::{Deserialize, Serialize};

pub type NodeId = u32;
pub type StreamId = u16;
pub type EventId = u128;
pub type CertId = u128;
pub type BatchId = u64;
pub type SnapshotId = u64;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Event {
    pub event_id: EventId,
    pub node_id: NodeId,
    pub stream_id: StreamId,
    pub lamport: u64,
    pub mono_ts_ns: u64,
    pub event_kind: u16,
    pub flags: u16,
    pub deps_count: u16,
    pub payload_len: u32,
    pub payload_hash: [u8; 32],
    pub deps: Vec<EventId>,
    pub payload: Vec<u8>,
}

impl Event {
    pub fn validate_invariants(&self) -> Result<(), String> {
        if self.deps.len() != self.deps_count as usize {
            return Err("deps_count mismatch".into());
        }
        if self.payload.len() != self.payload_len as usize {
            return Err("payload_len mismatch".into());
        }
        let mut hasher = Hasher::new();
        hasher.update(&self.payload);
        let digest = *hasher.finalize().as_bytes();
        if digest != self.payload_hash {
            return Err("payload_hash mismatch".into());
        }
        Ok(())
    }

    pub fn ordering_key(&self) -> (u64, NodeId, StreamId, EventId) {
        (self.lamport, self.node_id, self.stream_id, self.event_id)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GlobalMerge {
    pub merged_state_hash: [u8; 32],
    pub accepted_event_ids: Vec<EventId>,
    pub frontier_digest: [u8; 32],
    pub consistency_witness_hash: [u8; 32],
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Obstruction {
    pub conflict_set: Vec<EventId>,
    pub violated_predicate_id: u32,
    pub witness_hash: [u8; 32],
    pub overlap_context_digest: [u8; 32],
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SnapshotManifest {
    pub snapshot_id: SnapshotId,
    pub created_at_ns: u64,
    pub base_checkpoint_offset: u64,
    pub frontier_digest: [u8; 32],
    pub merged_state_hash: [u8; 32],
    pub stream_heads_digest: [u8; 32],
    pub schema_hash: [u8; 32],
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReplayIncident {
    pub incident_id: u128,
    pub expected_hash: [u8; 32],
    pub observed_hash: [u8; 32],
    pub divergence_batch_id: u64,
    pub divergence_event_id: u128,
    pub metadata_digest: [u8; 32],
}

use uuid::Uuid;

use crate::{hash_bytes, ReplayIncident, SnapshotManifest};

pub fn dump_crash_state(events: &[crate::Event], reason: &str) {
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let filename = format!("/tmp/omega-crash-{}-{}.json", reason, now);
    if let Ok(file) = std::fs::File::create(filename) {
        let _ = serde_json::to_writer(file, events);
    }
}

pub fn replay_digest(snapshot: &SnapshotManifest, log_suffix: &[u8], replay_seed: u64) -> [u8; 32] {
    let mut data = serde_json::to_vec(snapshot).unwrap_or_default();
    data.extend_from_slice(log_suffix);
    data.extend_from_slice(&replay_seed.to_le_bytes());
    hash_bytes(&data)
}

pub fn compare_replay(
    snapshot: &SnapshotManifest,
    log_suffix: &[u8],
    replay_seed: u64,
    expected: [u8; 32],
    divergence_batch_id: u64,
    divergence_event_id: u128,
) -> Option<ReplayIncident> {
    let observed = replay_digest(snapshot, log_suffix, replay_seed);
    if observed == expected {
        return None;
    }

    let mut md = Vec::new();
    md.extend_from_slice(&expected);
    md.extend_from_slice(&observed);
    md.extend_from_slice(&divergence_batch_id.to_le_bytes());
    md.extend_from_slice(&divergence_event_id.to_le_bytes());

    let incident_id = Uuid::new_v4().as_u128();
    Some(ReplayIncident {
        incident_id,
        expected_hash: expected,
        observed_hash: observed,
        divergence_batch_id,
        divergence_event_id,
        metadata_digest: hash_bytes(&md),
    })
}

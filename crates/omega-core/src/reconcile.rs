use std::collections::{BTreeMap, BTreeSet, HashSet};

use blake3::Hasher;
use serde::{Deserialize, Serialize};

use crate::{Event, EventId, GlobalMerge, Obstruction};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CheckerResult {
    Merge {
        merged_state_hash: [u8; 32],
        accepted_ids_digest: [u8; 32],
        witness_hash: [u8; 32],
        accepted_event_ids: Vec<EventId>,
    },
    Obstruction {
        conflict_set: Vec<EventId>,
        // NEW: Cryptographic proof of the payloads that caused the conflict
        conflicting_payload_hashes: Vec<[u8; 32]>,
        violated_predicate_id: u32,
        witness_hash: [u8; 32],
    },
}

pub fn deterministic_sort(events: &mut [Event]) {
    events.sort_by_key(|e| e.ordering_key());
}

pub fn reconcile_events(mut events: Vec<Event>) -> CheckerResult {
    deterministic_sort(&mut events);
    
    let payload_map: BTreeMap<EventId, [u8; 32]> = events.iter().map(|e| (e.event_id, e.payload_hash)).collect();

    let mut per_stream = BTreeMap::<(u32, u16), u64>::new();
    let mut known_ids = HashSet::<EventId>::new();
    let mut duplicates = BTreeSet::<EventId>::new();

    for e in &events {
        if let Err(_) = e.validate_invariants() {
            let conflict_hashes = vec![e.payload_hash];
            crate::replay::dump_crash_state(&events, "obstruction");
            return CheckerResult::Obstruction {
                conflict_set: vec![e.event_id],
                conflicting_payload_hashes: conflict_hashes.clone(),
                violated_predicate_id: 2001,
                witness_hash: hash_obstruction(&[e.event_id], &conflict_hashes),
            };
        }

        if !known_ids.insert(e.event_id) {
            duplicates.insert(e.event_id);
        }

        let key = (e.node_id, e.stream_id);
        if let Some(prev) = per_stream.get(&key) {
            if e.lamport <= *prev {
                let conflict_hashes = vec![e.payload_hash];
                crate::replay::dump_crash_state(&events, "obstruction");
                return CheckerResult::Obstruction {
                    conflict_set: vec![e.event_id],
                    conflicting_payload_hashes: conflict_hashes.clone(),
                    violated_predicate_id: 1001,
                    witness_hash: hash_obstruction(&[e.event_id], &conflict_hashes),
                };
            }
        }
        per_stream.insert(key, e.lamport);
    }

    if !duplicates.is_empty() {
        let set = duplicates.into_iter().collect::<Vec<_>>();
        let mut hashes = Vec::new();
        for id in &set {
            if let Some(h) = payload_map.get(id) {
                hashes.push(*h);
            }
        }
        crate::replay::dump_crash_state(&events, "obstruction");
        return CheckerResult::Obstruction {
            witness_hash: hash_obstruction(&set, &hashes),
            conflict_set: set,
            conflicting_payload_hashes: hashes,
            violated_predicate_id: 1002,
        };
    }

    let all_ids = events.iter().map(|e| e.event_id).collect::<Vec<_>>();
    let batch_ids = all_ids.iter().copied().collect::<HashSet<_>>();
    let mut seen = HashSet::new();

    for e in &events {
        for d in &e.deps {
            if !seen.contains(d) {
                if batch_ids.contains(d) {
                    // Dependency is in the batch but not yet seen -> Future Dependency / Cycle
                    let mut hashes = vec![e.payload_hash];
                    if let Some(h) = payload_map.get(d) {
                         hashes.push(*h);
                    }
                    crate::replay::dump_crash_state(&events, "obstruction");
                    return CheckerResult::Obstruction {
                        conflict_set: vec![e.event_id, *d],
                        conflicting_payload_hashes: hashes.clone(),
                        violated_predicate_id: 2003,
                        witness_hash: hash_obstruction(&[e.event_id, *d], &hashes),
                    };
                } else {
                    // Dependency is not in the batch -> Missing Dependency
                    let hashes = vec![e.payload_hash];
                    crate::replay::dump_crash_state(&events, "obstruction");
                    return CheckerResult::Obstruction {
                        conflict_set: vec![e.event_id, *d],
                        conflicting_payload_hashes: hashes.clone(),
                        violated_predicate_id: 2002,
                        witness_hash: hash_obstruction(&[e.event_id, *d], &hashes),
                    };
                }
            }
        }
        seen.insert(e.event_id);
    }

    let mut state_hasher = Hasher::new();
    for e in &events {
        state_hasher.update(&e.payload_hash);
        state_hasher.update(&e.event_id.to_le_bytes());
    }
    let merged_state_hash = *state_hasher.finalize().as_bytes();

    let accepted_ids_digest = hash_ids(&all_ids);
    let witness_hash = hash_bytes(&[&merged_state_hash[..], &accepted_ids_digest[..]].concat());

    CheckerResult::Merge {
        merged_state_hash,
        accepted_ids_digest,
        witness_hash,
        accepted_event_ids: all_ids,
    }
}

pub fn into_global_merge(result: &CheckerResult) -> Option<GlobalMerge> {
    match result {
        CheckerResult::Merge {
            merged_state_hash,
            accepted_event_ids,
            witness_hash,
            ..
        } => {
            let frontier_digest = hash_ids(accepted_event_ids);
            Some(GlobalMerge {
                merged_state_hash: *merged_state_hash,
                accepted_event_ids: accepted_event_ids.clone(),
                frontier_digest,
                consistency_witness_hash: *witness_hash,
            })
        }
        _ => None,
    }
}

pub fn into_obstruction(result: &CheckerResult) -> Option<Obstruction> {
    match result {
        CheckerResult::Obstruction {
            conflict_set,
            violated_predicate_id,
            witness_hash,
            ..
        } => Some(Obstruction {
            overlap_context_digest: hash_ids(conflict_set),
            conflict_set: conflict_set.clone(),
            violated_predicate_id: *violated_predicate_id,
            witness_hash: *witness_hash,
        }),
        _ => None,
    }
}

pub fn hash_ids(ids: &[EventId]) -> [u8; 32] {
    let mut hasher = Hasher::new();
    for id in ids {
        hasher.update(&id.to_le_bytes());
    }
    *hasher.finalize().as_bytes()
}

pub fn hash_bytes(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = Hasher::new();
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

pub fn hash_obstruction(ids: &[EventId], payloads: &[[u8; 32]]) -> [u8; 32] {
    let mut hasher = Hasher::new();
    for id in ids { hasher.update(&id.to_le_bytes()); }
    for p in payloads { hasher.update(p); }
    *hasher.finalize().as_bytes()
}

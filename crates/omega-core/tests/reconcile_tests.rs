use std::collections::HashSet;
use sha2::{Sha256, Digest};
use omega_core::{reconcile_events, CheckerResult, Event};

fn mk_event(id: u128, lamport: u64, deps: Vec<u128>) -> Event {
    let payload = format!("{id}").into_bytes();
    let mut hasher = Sha256::new();
    hasher.update(&payload);
    let payload_hash = hasher.finalize().into();
    Event {
        event_id: id,
        node_id: 1,
        stream_id: 1,
        lamport,
        mono_ts_ns: id as u64,
        event_kind: 1,
        flags: 0,
        deps_count: deps.len() as u16,
        payload_len: payload.len() as u32,
        payload_hash,
        deps,
        payload,
    }
}

#[test]
fn merge_when_valid() {
    let events = vec![mk_event(1, 1, vec![]), mk_event(2, 2, vec![1])];
    let res = reconcile_events(events, &HashSet::new());
    assert!(matches!(res, CheckerResult::Merge { .. }));
}

#[test]
fn obstruction_on_missing_dep() {
    let events = vec![mk_event(1, 1, vec![]), mk_event(2, 2, vec![9])];
    let res = reconcile_events(events, &HashSet::new());
    match res {
        CheckerResult::Obstruction {
            violated_predicate_id,
            ..
        } => assert_eq!(violated_predicate_id, 2002),
        _ => panic!("expected obstruction"),
    }
}

#[test]
fn merge_with_prior_knowledge() {
    let mut prior = HashSet::new();
    prior.insert(100);
    
    // Event 1 depends on 100 which is not in this batch but is in 'prior'
    let events = vec![mk_event(1, 1, vec![100])];
    let res = reconcile_events(events, &prior);
    assert!(matches!(res, CheckerResult::Merge { .. }));
}

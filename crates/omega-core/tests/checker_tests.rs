use omega_core::{run_checker, validate_binding, CheckerBinding, CheckerInput, Event};

fn event(id: u128, lamport: u64, deps: Vec<u128>) -> Event {
    let payload = format!("evt-{id}").into_bytes();
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
        payload_hash: *blake3::hash(&payload).as_bytes(),
        deps,
        payload,
    }
}

#[test]
fn checker_preserves_binding() {
    let binding = CheckerBinding {
        checker_version: (0, 1, 0),
        schema_version: 1,
        schema_hash: [0; 32],
        predicate_catalog_hash: [0; 32],
    };

    let output = run_checker(CheckerInput {
        events: vec![event(1, 1, vec![])],
        prior_frontier_digest: [0; 32],
        binding: binding.clone(),
    });

    assert!(validate_binding(&binding, &output.binding).is_ok());
}

#[test]
fn checker_binding_mismatch_rejected() {
    let expected = CheckerBinding {
        checker_version: (0, 1, 0),
        schema_version: 1,
        schema_hash: [0; 32],
        predicate_catalog_hash: [0; 32],
    };
    let output = CheckerBinding {
        checker_version: (9, 9, 9),
        schema_version: 1,
        schema_hash: [0; 32],
        predicate_catalog_hash: [0; 32],
    };

    assert!(validate_binding(&expected, &output).is_err());
}

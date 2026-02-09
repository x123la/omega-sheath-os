use std::collections::HashSet;
use serde::{Deserialize, Serialize};

use crate::{reconcile_events, CheckerResult, Event, EventId};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct CheckerBinding {
    pub checker_version: (u16, u16, u16),
    pub schema_version: u16,
    pub schema_hash: [u8; 32],
    pub predicate_catalog_hash: [u8; 32],
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckerInput {
    pub events: Vec<Event>,
    pub prior_frontier_digest: [u8; 32],
    // NEW: The actual set of IDs for validation. In production, 
    // this might be a Bloom filter or persistent store handle.
    pub prior_known_ids: HashSet<EventId>,
    pub binding: CheckerBinding,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckerOutput {
    pub result: CheckerResult,
    pub binding: CheckerBinding,
}

pub fn run_checker(input: CheckerInput) -> CheckerOutput {
    let result = reconcile_events(input.events, &input.prior_known_ids);
    CheckerOutput {
        result,
        binding: input.binding,
    }
}

pub fn validate_binding(expected: &CheckerBinding, output: &CheckerBinding) -> Result<(), String> {
    if expected != output {
        return Err("checker/schema/predicate binding mismatch".to_string());
    }
    Ok(())
}

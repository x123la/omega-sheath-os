use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricRecord {
    pub seq_id: u64,
    pub metric: String,
    pub value: f64,
    pub batch_id: Option<u64>,
    pub cert_id: Option<u128>,
}

pub fn metric_line(record: &MetricRecord) -> anyhow::Result<String> {
    Ok(serde_json::to_string(record)?)
}

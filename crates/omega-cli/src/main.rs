use std::collections::BTreeMap;
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::ExitCode;

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use omega_core::{
    build_certificate, cert_hash, compare_replay, deterministic_sort, hash_bytes, metric_line,
    recover_valid_prefix, run_checker, validate_binding, CheckerBinding, CheckerInput,
    CheckerOutput, CheckerResult, Event, MetricRecord, OmegaFileHeader, SnapshotManifest,
    OMEGA_MAGIC,
};

#[derive(Debug, Parser)]
#[command(name = "omega")]
#[command(about = "OMEGA-SHEAF-OS reference CLI")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Debug, Subcommand)]
enum Command {
    Ingest {
        #[arg(long)]
        input: PathBuf,
    },
    Reconcile {
        #[arg(long)]
        input: PathBuf,
        #[arg(long, default_value_t = 1)]
        batch_id: u64,
        #[arg(long, default_value_t = 42)]
        replay_seed: u64,
        #[arg(long)]
        output: Option<PathBuf>,
    },
    Certify {
        #[arg(long)]
        result: PathBuf,
        #[arg(long, default_value_t = 1)]
        batch_id: u64,
        #[arg(long, default_value_t = 42)]
        replay_seed: u64,
        #[arg(long, default_value_t = 1)]
        schema_version: u16,
        #[arg(long)]
        output: PathBuf,
        #[arg(long)]
        cert_log: Option<PathBuf>,
    },
    Replay {
        #[arg(long)]
        snapshot: PathBuf,
        #[arg(long)]
        log_suffix: PathBuf,
        #[arg(long)]
        expected_hash_hex: String,
        #[arg(long, default_value_t = 42)]
        replay_seed: u64,
        #[arg(long, default_value_t = 0)]
        divergence_batch_id: u64,
        #[arg(long, default_value_t = 0)]
        divergence_event_id: u128,
    },
    Explain {
        #[arg(long)]
        input: PathBuf,
    },
    Bench {
        #[arg(long, default_value_t = 10000)]
        events: usize,
    },
    Doctor {
        #[arg(long, default_value = ".")]
        root: PathBuf,
    },
    ExportMetrics {
        #[arg(long)]
        input: PathBuf,
        #[arg(long)]
        output: PathBuf,
    },
    GenerateEvents {
        #[arg(long)]
        output: PathBuf,
        #[arg(long, default_value_t = 2)]
        count: usize,
    },
}

fn main() -> ExitCode {
    match run() {
        Ok(_) => ExitCode::from(0),
        Err(e) => {
            let code = classify_exit_code(&e);
            let status = serde_json::json!({
                "status": "error",
                "exit_code": code,
                "error": format!("{e:#}")
            });
            println!("{}", serde_json::to_string_pretty(&status).unwrap());
            ExitCode::from(code as u8)
        }
    }
}

fn classify_exit_code(err: &anyhow::Error) -> u16 {
    let msg = format!("{err:#}");
    if msg.contains("schema") {
        10
    } else if msg.contains("cert") || msg.contains("signature") {
        20
    } else if msg.contains("replay") || msg.contains("mismatch") {
        30
    } else if msg.contains("timeout") {
        40
    } else {
        50
    }
}

fn run() -> Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Command::Ingest { input } => cmd_ingest(input),
        Command::Reconcile {
            input,
            batch_id,
            replay_seed,
            output,
        } => cmd_reconcile(input, batch_id, replay_seed, output),
        Command::Certify {
            result,
            batch_id,
            replay_seed,
            schema_version,
            output,
            cert_log,
        } => cmd_certify(
            result,
            batch_id,
            replay_seed,
            schema_version,
            output,
            cert_log,
        ),
        Command::Replay {
            snapshot,
            log_suffix,
            expected_hash_hex,
            replay_seed,
            divergence_batch_id,
            divergence_event_id,
        } => cmd_replay(
            snapshot,
            log_suffix,
            expected_hash_hex,
            replay_seed,
            divergence_batch_id,
            divergence_event_id,
        ),
        Command::Explain { input } => cmd_explain(input),
        Command::Bench { events } => cmd_bench(events),
        Command::Doctor { root } => cmd_doctor(root),
        Command::ExportMetrics { input, output } => cmd_export_metrics(input, output),
        Command::GenerateEvents { output, count } => cmd_generate_events(output, count),
    }
}

fn cmd_ingest(input: PathBuf) -> Result<()> {
    let bytes = fs::read(&input).with_context(|| format!("failed to read {:?}", input))?;
    if bytes.len() < 64 {
        anyhow::bail!("schema error: omega file too small")
    }

    let header = OmegaFileHeader::decode(&bytes[0..64])
        .map_err(|e| anyhow::anyhow!("schema error: header decode failed: {e}"))?;
    if header.magic != OMEGA_MAGIC {
        anyhow::bail!("schema error: bad magic/version")
    }

    let valid = recover_valid_prefix(&bytes[64..]);
    let malformed = (bytes.len() - 64).saturating_sub(valid);
    let status = serde_json::json!({
        "status": "ok",
        "command": "ingest",
        "schema_version": header.schema_version,
        "valid_bytes_after_header": valid,
        "malformed_tail_bytes": malformed
    });
    println!("{}", serde_json::to_string_pretty(&status)?);
    Ok(())
}

fn parse_events(path: &PathBuf) -> Result<Vec<Event>> {
    let text = fs::read_to_string(path).with_context(|| format!("failed reading {:?}", path))?;
    if text.trim_start().starts_with('[') {
        let events: Vec<Event> = serde_json::from_str(&text)?;
        return Ok(events);
    }

    let f = fs::File::open(path)?;
    let r = BufReader::new(f);
    let mut out = Vec::new();
    for line in r.lines() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        out.push(serde_json::from_str::<Event>(&line)?);
    }
    Ok(out)
}

fn cmd_reconcile(
    input: PathBuf,
    batch_id: u64,
    replay_seed: u64,
    output: Option<PathBuf>,
) -> Result<()> {
    let mut events = parse_events(&input)?;
    deterministic_sort(&mut events);

    let binding = CheckerBinding {
        checker_version: (0, 1, 0),
        schema_version: 1,
        schema_hash: [0; 32],
        predicate_catalog_hash: [0; 32],
    };

    let checker_input = CheckerInput {
        events,
        prior_frontier_digest: [0; 32],
        binding: binding.clone(),
    };
    let checker_output = run_checker(checker_input);

    let out = serde_json::json!({
        "status": "ok",
        "command": "reconcile",
        "batch_id": batch_id,
        "replay_seed": replay_seed,
        "checker_output": checker_output
    });

    if let Some(path) = output {
        fs::write(&path, serde_json::to_vec_pretty(&out)?)?;
    }
    println!("{}", serde_json::to_string_pretty(&out)?);
    Ok(())
}

fn cmd_certify(
    result_path: PathBuf,
    batch_id: u64,
    replay_seed: u64,
    schema_version: u16,
    output: PathBuf,
    cert_log: Option<PathBuf>,
) -> Result<()> {
    let bytes = fs::read(&result_path)?;
    let root: serde_json::Value = serde_json::from_slice(&bytes)?;
    let expected_binding = CheckerBinding {
        checker_version: (0, 1, 0),
        schema_version,
        schema_hash: [0; 32],
        predicate_catalog_hash: [0; 32],
    };

    let result = if let Some(output_value) = root.get("checker_output") {
        let checker_output: CheckerOutput = serde_json::from_value(output_value.clone())?;
        validate_binding(&expected_binding, &checker_output.binding)
            .map_err(|e| anyhow::anyhow!("schema error: {e}"))?;
        checker_output.result
    } else {
        let result_value = root
            .get("result")
            .cloned()
            .context("missing checker_output/result field in reconcile output")?;
        serde_json::from_value::<CheckerResult>(result_value)?
    };

    let prev_hash = if let Some(log) = &cert_log {
        if log.exists() {
            hash_bytes(&fs::read(log)?)
        } else {
            [0u8; 32]
        }
    } else {
        [0u8; 32]
    };

    let env = build_certificate(
        &result,
        batch_id,
        (0, 1, 0),
        schema_version,
        replay_seed,
        prev_hash,
    )?;

    fs::write(&output, serde_json::to_vec_pretty(&env)?)?;
    if let Some(log) = cert_log {
        let mut f = fs::OpenOptions::new().create(true).append(true).open(log)?;
        writeln!(f, "{}", serde_json::to_string(&env)?)?;
    }

    let cert_digest = cert_hash(&env)?;
    let status = serde_json::json!({
        "status": "ok",
        "command": "certify",
        "cert_id": env.cert_id.to_string(),
        "cert_type": env.cert_type,
        "cert_hash_hex": hex::encode(cert_digest)
    });
    println!("{}", serde_json::to_string_pretty(&status)?);
    Ok(())
}

fn parse_hash32_hex(s: &str) -> Result<[u8; 32]> {
    let raw = hex::decode(s)?;
    if raw.len() != 32 {
        anyhow::bail!("replay mismatch: expected 32-byte hash hex")
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&raw);
    Ok(out)
}

fn cmd_replay(
    snapshot_path: PathBuf,
    log_suffix_path: PathBuf,
    expected_hash_hex: String,
    replay_seed: u64,
    divergence_batch_id: u64,
    divergence_event_id: u128,
) -> Result<()> {
    let snapshot: SnapshotManifest = serde_json::from_slice(&fs::read(snapshot_path)?)?;
    let log_suffix = fs::read(log_suffix_path)?;
    let expected = parse_hash32_hex(&expected_hash_hex)?;

    let incident = compare_replay(
        &snapshot,
        &log_suffix,
        replay_seed,
        expected,
        divergence_batch_id,
        divergence_event_id,
    );

    if let Some(incident) = incident {
        let status = serde_json::json!({
            "status": "error",
            "command": "replay",
            "incident": {
                "incident_id": incident.incident_id.to_string(),
                "expected_hash": incident.expected_hash,
                "observed_hash": incident.observed_hash,
                "divergence_batch_id": incident.divergence_batch_id,
                "divergence_event_id": incident.divergence_event_id.to_string(),
                "metadata_digest": incident.metadata_digest
            }
        });
        println!("{}", serde_json::to_string_pretty(&status)?);
        anyhow::bail!("replay mismatch")
    }

    let status = serde_json::json!({
        "status": "ok",
        "command": "replay",
        "result": "deterministic"
    });
    println!("{}", serde_json::to_string_pretty(&status)?);
    Ok(())
}

fn cmd_explain(input: PathBuf) -> Result<()> {
    let bytes = fs::read(&input)?;
    let value: serde_json::Value = serde_json::from_slice(&bytes)?;

    let msg = if value.get("cert_type").is_some() {
        let cert_type = value
            .get("cert_type")
            .cloned()
            .unwrap_or(serde_json::json!("Unknown"));
        serde_json::json!({
            "status": "ok",
            "command": "explain",
            "kind": "certificate",
            "cert_type": cert_type,
            "summary": value
        })
    } else if value.get("checker_output").is_some() || value.get("result").is_some() {
        serde_json::json!({
            "status": "ok",
            "command": "explain",
            "kind": "checker_result",
            "summary": value
        })
    } else {
        serde_json::json!({
            "status": "ok",
            "command": "explain",
            "kind": "generic",
            "summary": value
        })
    };

    println!("{}", serde_json::to_string_pretty(&msg)?);
    Ok(())
}

fn cmd_bench(events: usize) -> Result<()> {
    let mut generated = Vec::with_capacity(events);
    for i in 0..events {
        let payload = format!("event-{i}").into_bytes();
        let payload_hash = *blake3::hash(&payload).as_bytes();
        generated.push(Event {
            event_id: i as u128 + 1,
            node_id: (i % 32) as u32,
            stream_id: (i % 8) as u16,
            lamport: (i / 8) as u64 + 1,
            mono_ts_ns: i as u64,
            event_kind: 1,
            flags: 0,
            deps_count: 0,
            payload_len: payload.len() as u32,
            payload_hash,
            deps: Vec::new(),
            payload,
        });
    }

    let start = std::time::Instant::now();
    let result = run_checker(CheckerInput {
        events: generated,
        prior_frontier_digest: [0; 32],
        binding: CheckerBinding {
            checker_version: (0, 1, 0),
            schema_version: 1,
            schema_hash: [0; 32],
            predicate_catalog_hash: [0; 32],
        },
    })
    .result;
    let elapsed = start.elapsed();

    let obstruction = matches!(result, CheckerResult::Obstruction { .. });
    let status = serde_json::json!({
        "status": "ok",
        "command": "bench",
        "events": events,
        "elapsed_ms": elapsed.as_millis(),
        "obstruction": obstruction
    });
    println!("{}", serde_json::to_string_pretty(&status)?);
    Ok(())
}

fn cmd_doctor(root: PathBuf) -> Result<()> {
    let required = [
        "layers/lean4/Formal/OMEGA.lean",
        "layers/elixir/runtime/mix.exs",
        "layers/elixir/runtime/lib/omega_runtime/application.ex",
        "layers/zig/src/lib.zig",
        "layers/futhark/kernels.fut",
        "layers/tla/OMEGA.tla",
        "layers/nushell/pipeline.nu",
        "schemas/certificate.schema.json",
    ];

    let mut missing = Vec::new();
    for p in &required {
        let full = root.join(p);
        if !full.exists() {
            missing.push(p.to_string());
        }
    }

    let tools = [
        "cargo", "zig", "futhark", "lake", "nu", "java", "tlc", "elixir", "mix",
    ];
    let mut tool_status = BTreeMap::new();
    for t in tools {
        let installed = std::process::Command::new("bash")
            .arg("-lc")
            .arg(format!("command -v {t} >/dev/null 2>&1"))
            .status()?
            .success();
        tool_status.insert(t.to_string(), installed);
    }

    let status = serde_json::json!({
        "status": if missing.is_empty() { "ok" } else { "error" },
        "command": "doctor",
        "missing_files": missing,
        "toolchain": tool_status
    });
    println!("{}", serde_json::to_string_pretty(&status)?);

    if status["status"] == "error" {
        anyhow::bail!("schema error: project layout incomplete")
    }
    Ok(())
}

fn cmd_export_metrics(input: PathBuf, output: PathBuf) -> Result<()> {
    let f = fs::File::open(input)?;
    let r = BufReader::new(f);

    let mut seq = 0u64;
    let mut rows = Vec::new();
    for line in r.lines() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        let value: serde_json::Value = serde_json::from_str(&line)?;
        let metric = value
            .get("metric")
            .and_then(|v| v.as_str())
            .unwrap_or("unknown")
            .to_string();
        let val = value.get("value").and_then(|v| v.as_f64()).unwrap_or(0.0);
        let batch_id = value.get("batch_id").and_then(|v| v.as_u64());
        let cert_id = value
            .get("cert_id")
            .and_then(|v| v.as_str())
            .and_then(|s| s.parse::<u128>().ok());

        let rec = MetricRecord {
            seq_id: seq,
            metric,
            value: val,
            batch_id,
            cert_id,
        };
        seq += 1;
        rows.push(metric_line(&rec)?);
    }

    fs::write(&output, rows.join("\n") + "\n")?;
    let status = serde_json::json!({
        "status": "ok",
        "command": "export-metrics",
        "records": rows.len(),
        "output": output
    });
    println!("{}", serde_json::to_string_pretty(&status)?);
    Ok(())
}

fn cmd_generate_events(output: PathBuf, count: usize) -> Result<()> {
    let mut generated = Vec::with_capacity(count.max(2));

    for i in 0..count.max(2) {
        let payload = format!("event-{i}").into_bytes();
        let payload_hash = *blake3::hash(&payload).as_bytes();
        let deps = if i == 0 { vec![] } else { vec![i as u128] };

        generated.push(Event {
            event_id: i as u128 + 1,
            node_id: 1,
            stream_id: 1,
            lamport: i as u64 + 1,
            mono_ts_ns: i as u64 + 1,
            event_kind: 1,
            flags: 0,
            deps_count: deps.len() as u16,
            payload_len: payload.len() as u32,
            payload_hash,
            deps,
            payload,
        });
    }

    fs::write(&output, serde_json::to_vec_pretty(&generated)?)?;
    let status = serde_json::json!({
        "status": "ok",
        "command": "generate-events",
        "count": generated.len(),
        "output": output
    });
    println!("{}", serde_json::to_string_pretty(&status)?);
    Ok(())
}

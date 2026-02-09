use "collections"

primitive Ordering
  fun key(lamport: U64, node_id: U32, stream_id: U16, event_id: U128): String iso^ =>
    recover
      lamport.string() + ":" + node_id.string() + ":" + stream_id.string() + ":" + event_id.string()
    end

class val EventEnvelope
  let event_id: U128
  let node_id: U32
  let stream_id: U16
  let lamport: U64
  let deps_digest: String
  let payload_hash: String
  let ingest_seq_no: U64
  let raw_offset: U64

  new val create(
    event_id': U128,
    node_id': U32,
    stream_id': U16,
    lamport': U64,
    deps_digest': String,
    payload_hash': String,
    ingest_seq_no': U64,
    raw_offset': U64)
  =>
    event_id = event_id'
    node_id = node_id'
    stream_id = stream_id'
    lamport = lamport'
    deps_digest = deps_digest'
    payload_hash = payload_hash'
    ingest_seq_no = ingest_seq_no'
    raw_offset = raw_offset'

actor MetricsActor
  be metric(name: String, value: F64) =>
    None

actor SequencerActor
  let _metrics: MetricsActor
  new create(metrics: MetricsActor) => _metrics = metrics

  be enqueue(ev: EventEnvelope) =>
    _metrics.metric("sequencer.events", 1)

actor IngressActor
  let _sequencer: SequencerActor
  new create(sequencer: SequencerActor) => _sequencer = sequencer

  be ingest(ev: EventEnvelope) =>
    _sequencer.enqueue(ev)

actor Main
  new create(env: Env) =>
    let metrics = MetricsActor
    let sequencer = SequencerActor(metrics)
    let ingress = IngressActor(sequencer)

    let ev = EventEnvelope(
      1,
      1,
      1,
      1,
      "deps",
      "payload",
      1,
      0)

    ingress.ingest(ev)
    env.out.print("OMEGA Pony runtime skeleton initialized")

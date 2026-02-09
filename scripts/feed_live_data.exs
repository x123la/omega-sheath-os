# Synthetic Truth Stream for OC2 Visualization
IO.puts "[omega] Starting synthetic data feed..."

events = Enum.map(1..20, fn i ->
  payload = "synthetic-event-#{i}"
  payload_hash = :crypto.hash(:sha256, payload)
  
  %{
    event_id: i,
    node_id: 1,
    stream_id: 1,
    lamport: i,
    deps: if(i == 1, do: [], else: [i - 1]),
    payload: payload,
    payload_hash: payload_hash
  }
end)

Enum.each(events, fn ev ->
  IO.puts "[omega] Ingesting event ID: #{ev.event_id}"
  OmegaRuntime.IngressActor.ingest(ev)
  Process.sleep(500) # Controlled speed for visualization
end)

IO.puts "[omega] Feed complete."

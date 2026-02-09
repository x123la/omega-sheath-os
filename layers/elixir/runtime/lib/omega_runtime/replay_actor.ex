defmodule OmegaRuntime.ReplayActor do
  @moduledoc "Replay actor: deterministic digest verification and incident persistence."
  use GenServer

  def start_link(_opts), do: GenServer.start_link(__MODULE__, %{}, name: __MODULE__)

  def verify(snapshot_manifest, log_suffix, replay_seed, expected_hash) do
    GenServer.call(
      __MODULE__,
      {:verify, snapshot_manifest, log_suffix, replay_seed, expected_hash},
      :infinity
    )
  end

  @impl true
  def init(state), do: {:ok, state}

  @impl true
  def handle_call({:verify, snapshot, suffix, replay_seed, expected_hash}, _from, state) do
    observed = replay_digest(snapshot, suffix, replay_seed)

    if observed == expected_hash do
      {:reply, :ok, state}
    else
      incident_id = :binary.decode_unsigned(:crypto.strong_rand_bytes(16))
      
      # Match Rust: hash of (expected_hash + observed_hash) as binary
      metadata_digest = OmegaRuntime.digest(expected_hash <> observed)

      incident = %{
        incident_id: incident_id,
        expected_hash: expected_hash,
        observed_hash: observed,
        divergence_batch_id: 0,
        divergence_event_id: 0,
        metadata_digest: metadata_digest
      }

      dir = System.get_env("OMEGA_REPLAY_DIR", "/tmp/omega-runtime/replay")
      File.mkdir_p!(dir)
      path = Path.join(dir, "incident-#{incident.incident_id}.bin")
      File.write!(path, :erlang.term_to_binary(incident))

      {:reply, {:error, incident, path}, state}
    end
  end

  defp replay_digest(s, log_suffix, replay_seed) do
    # Match Rust: snapshot fields in LE + suffix + seed in LE
    data = 
      <<s.snapshot_id::little-size(64)>> <>
      <<s.created_at_ns::little-size(64)>> <>
      <<s.base_checkpoint_offset::little-size(64)>> <>
      s.frontier_digest <>
      s.merged_state_hash <>
      s.stream_heads_digest <>
      s.schema_hash <>
      log_suffix <>
      <<replay_seed::little-size(64)>>

    OmegaRuntime.digest(data)
  end
end

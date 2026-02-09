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
      incident = %{
        incident_id: :binary.decode_unsigned(:crypto.strong_rand_bytes(16)),
        expected_hash: expected_hash,
        observed_hash: observed,
        divergence_batch_id: 0,
        divergence_event_id: 0,
        metadata_digest: OmegaRuntime.digest(:erlang.term_to_binary({expected_hash, observed}))
      }

      dir = System.get_env("OMEGA_REPLAY_DIR", "/tmp/omega-runtime/replay")
      File.mkdir_p!(dir)
      path = Path.join(dir, "incident-#{incident.incident_id}.bin")
      File.write!(path, :erlang.term_to_binary(incident))

      {:reply, {:error, incident, path}, state}
    end
  end

  defp replay_digest(snapshot_manifest, log_suffix, replay_seed) do
    OmegaRuntime.digest(:erlang.term_to_binary({snapshot_manifest, log_suffix, replay_seed}))
  end
end

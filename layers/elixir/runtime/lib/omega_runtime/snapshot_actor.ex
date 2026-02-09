defmodule OmegaRuntime.SnapshotActor do
  @moduledoc "Snapshot actor: writes deterministic snapshot manifests for replay."
  use GenServer

  def start_link(_opts), do: GenServer.start_link(__MODULE__, %{snapshot_id: 0}, name: __MODULE__)

  def capture(frontier_digest, merged_state_hash, stream_heads_digest, schema_hash) do
    GenServer.call(
      __MODULE__,
      {:capture, frontier_digest, merged_state_hash, stream_heads_digest, schema_hash}
    )
  end

  @impl true
  def init(state), do: {:ok, state}

  @impl true
  def handle_call({:capture, frontier, merged, heads, schema}, _from, state) do
    next_id = state.snapshot_id + 1
    dir = System.get_env("OMEGA_SNAPSHOT_DIR", "/tmp/omega-runtime/snapshots")
    File.mkdir_p!(dir)

    manifest = %{
      snapshot_id: next_id,
      created_at_ns: OmegaRuntime.now_ns(),
      base_checkpoint_offset: 0,
      frontier_digest: frontier,
      merged_state_hash: merged,
      stream_heads_digest: heads,
      schema_hash: schema
    }

    path = Path.join(dir, "snapshot-#{next_id}.bin")
    File.write!(path, :erlang.term_to_binary(manifest))

    {:reply, {:ok, manifest, path}, %{state | snapshot_id: next_id}}
  end
end

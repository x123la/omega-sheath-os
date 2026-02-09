defmodule OmegaRuntime.CheckerGateway do
  @moduledoc "Formal checker boundary actor with deterministic merge/obstruction output."
  use GenServer

  @unknown_predicate_id 4_294_967_294

  def start_link(_opts), do: GenServer.start_link(__MODULE__, %{}, name: __MODULE__)

  def check(input), do: GenServer.call(__MODULE__, {:check, input}, :infinity)

  @impl true
  def init(state), do: {:ok, state}

  @impl true
  def handle_call({:check, %{events: events} = input}, _from, state) do
    result = evaluate(events, input)
    {:reply, result, state}
  end

  defp evaluate(events, _input) when not is_list(events),
    do: obstruction([], @unknown_predicate_id)

  defp evaluate(events, input) do
    ordered = OmegaRuntime.deterministic_sort(events)
    # Use prior_known_ids if provided in input, else empty set
    prior_known = Map.get(input, :prior_known_ids, MapSet.new())

    with :ok <- check_unique_ids(ordered, prior_known),
         :ok <- check_monotone_stream_lamport(ordered),
         :ok <- check_dependency_presence(ordered, prior_known) do
      accepted_event_ids = Enum.map(ordered, & &1.event_id)

      # Match Rust: hash(payload_hash + event_id_le_bytes) for each event
      merged_state_hash_bin = 
        Enum.reduce(ordered, :crypto.hash_init(:sha256), fn e, acc ->
          acc
          |> :crypto.hash_update(e.payload_hash)
          |> :crypto.hash_update(<<e.event_id::little-size(128)>>)
        end)
        |> :crypto.hash_final()

      # Match Rust: hash_ids (hash of all event_ids as little-endian u128)
      accepted_ids_digest = 
        Enum.reduce(accepted_event_ids, :crypto.hash_init(:sha256), fn id, acc ->
          :crypto.hash_update(acc, <<id::little-size(128)>>)
        end)
        |> :crypto.hash_final()

      witness_hash_bin = OmegaRuntime.digest(merged_state_hash_bin <> accepted_ids_digest)

      {:merge,
       %{
         accepted_event_ids: accepted_event_ids,
         merged_state_hash: merged_state_hash_bin,
         accepted_ids_digest: accepted_ids_digest,
         witness_hash: witness_hash_bin
       }}
    else
      {:obstruction, _} = obstruction -> obstruction
    end
  end

  defp check_unique_ids(events, prior_known) do
    ids = Enum.map(events, & &1.event_id)

    if length(ids) == length(Enum.uniq(ids)) do
      case Enum.find(events, fn e -> MapSet.member?(prior_known, e.event_id) end) do
        nil -> :ok
        duplicate_event -> 
          obstruction([duplicate_event.event_id], 1002, [duplicate_event.payload_hash])
      end
    else
      # Intra-batch duplicates
      duplicate_ids =
        ids
        |> Enum.frequencies()
        |> Enum.filter(fn {_k, v} -> v > 1 end)
        |> Enum.map(fn {k, _v} -> k end)
      
      # Collect hashes for these IDs
      hashes = 
        events 
        |> Enum.filter(fn e -> e.event_id in duplicate_ids end)
        |> Enum.map(& &1.payload_hash)

      obstruction(duplicate_ids, 1002, hashes)
    end
  end

  defp check_monotone_stream_lamport(events) do
    Enum.reduce_while(events, %{}, fn e, heads ->
      key = {e.node_id, e.stream_id}
      prev = Map.get(heads, key, 0)

      if e.lamport > prev do
        {:cont, Map.put(heads, key, e.lamport)}
      else
        {:halt, obstruction([e.event_id], 1001, [e.payload_hash])}
      end
    end)
    |> case do
      {:obstruction, _} = o -> o
      _ -> :ok
    end
  end

  defp check_dependency_presence(events, prior_known) do
    batch_ids = MapSet.new(Enum.map(events, & &1.event_id))

    Enum.reduce_while(events, prior_known, fn e, seen ->
      deps = if is_list(e.deps), do: e.deps, else: []

      case Enum.find(deps, fn d -> not MapSet.member?(seen, d) end) do
        nil ->
          {:cont, MapSet.put(seen, e.event_id)}

        missing_or_future ->
          if MapSet.member?(batch_ids, missing_or_future) do
            {:halt, obstruction([e.event_id, missing_or_future], 2003, [e.payload_hash])}
          else
            {:halt, obstruction([e.event_id, missing_or_future], 2002, [e.payload_hash])}
          end
      end
    end)
    |> case do
      %MapSet{} -> :ok
      other -> other
    end
  end

  defp obstruction(conflict_set, predicate_id, payload_hashes \\ []) do
    # Match Rust hash_obstruction: hash(ids_le + payloads)
    witness_hash =
      Enum.reduce(conflict_set, :crypto.hash_init(:sha256), fn id, acc ->
        :crypto.hash_update(acc, <<id::little-size(128)>>)
      end)
      |> (fn acc ->
            Enum.reduce(payload_hashes, acc, fn p, a -> :crypto.hash_update(a, p) end)
          end).()
      |> :crypto.hash_final()

    {:obstruction,
     %{
       conflict_set: Enum.uniq(conflict_set),
       conflicting_payload_hashes: payload_hashes,
       violated_predicate_id: predicate_id,
       witness_hash: witness_hash
     }}
  end
end

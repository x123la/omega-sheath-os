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

  defp evaluate(events, _input) do
    ordered = OmegaRuntime.deterministic_sort(events)

    with :ok <- check_unique_ids(ordered),
         :ok <- check_monotone_stream_lamport(ordered),
         :ok <- check_dependency_presence(ordered) do
      accepted_event_ids = Enum.map(ordered, & &1.event_id)

      payload_fingerprint =
        ordered
        |> Enum.map_join("|", fn e ->
          "#{e.event_id}:#{byte_size(serialize_payload(e.payload))}"
        end)
        |> OmegaRuntime.digest_hex()

      witness_hash = OmegaRuntime.digest_hex(payload_fingerprint)

      {:merge,
       %{
         accepted_event_ids: accepted_event_ids,
         merged_state_hash: payload_fingerprint,
         accepted_ids_digest:
           OmegaRuntime.digest_hex(
             Enum.join(Enum.map(accepted_event_ids, &Integer.to_string/1), ",")
           ),
         witness_hash: witness_hash
       }}
    else
      {:obstruction, _} = obstruction -> obstruction
    end
  end

  defp check_unique_ids(events) do
    ids = Enum.map(events, & &1.event_id)

    if length(ids) == length(Enum.uniq(ids)) do
      :ok
    else
      duplicates =
        ids
        |> Enum.frequencies()
        |> Enum.filter(fn {_k, v} -> v > 1 end)
        |> Enum.map(fn {k, _v} -> k end)

      {:obstruction, %{conflict_set: duplicates, violated_predicate_id: 1002}}
    end
  end

  defp check_monotone_stream_lamport(events) do
    Enum.reduce_while(events, %{}, fn e, heads ->
      key = {e.node_id, e.stream_id}
      prev = Map.get(heads, key, 0)

      if e.lamport > prev do
        {:cont, Map.put(heads, key, e.lamport)}
      else
        {:halt, {:obstruction, %{conflict_set: [e.event_id], violated_predicate_id: 1001}}}
      end
    end)
    |> case do
      :ok -> :ok
      %{} -> :ok
      {:obstruction, _} = o -> o
    end
  end

  defp check_dependency_presence(events) do
    known = MapSet.new(Enum.map(events, & &1.event_id))

    Enum.reduce_while(events, :ok, fn e, _acc ->
      deps = if is_list(e.deps), do: e.deps, else: []

      case Enum.find(deps, fn d -> not MapSet.member?(known, d) end) do
        nil ->
          {:cont, :ok}

        missing ->
          {:halt,
           {:obstruction, %{conflict_set: [e.event_id, missing], violated_predicate_id: 2002}}}
      end
    end)
  end

  defp obstruction(conflict_set, predicate_id) do
    {:obstruction,
     %{
       conflict_set: Enum.uniq(conflict_set),
       violated_predicate_id: predicate_id,
       witness_hash: OmegaRuntime.digest_hex(inspect(conflict_set))
     }}
  end

  defp serialize_payload(payload) when is_binary(payload), do: payload
  defp serialize_payload(payload) when is_list(payload), do: :erlang.term_to_binary(payload)
  defp serialize_payload(payload), do: :erlang.term_to_binary(payload)
end

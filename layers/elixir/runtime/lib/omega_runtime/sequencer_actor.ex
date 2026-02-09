defmodule OmegaRuntime.SequencerActor do
  @moduledoc "Sequencer actor: dedupe, per-stream lamport monotonicity, dependency readiness."
  use GenServer

  def start_link(_opts) do
    initial = %{seen: MapSet.new(), stream_heads: %{}, pending: %{}}
    GenServer.start_link(__MODULE__, initial, name: __MODULE__)
  end

  def enqueue(event_envelope), do: GenServer.cast(__MODULE__, {:enqueue, event_envelope})

  @impl true
  def init(state), do: {:ok, state}

  @impl true
  def handle_cast({:enqueue, envelope}, state) do
    case admit_event(envelope, state) do
      {:accepted, next_state} ->
        {:noreply, release_ready(next_state)}

      {:pending, next_state} ->
        {:noreply, next_state}

      {:dropped, next_state, reason} ->
        OmegaRuntime.MetricsActor.emit("sequencer.drop", 1, %{
          reason: reason,
          event_id: envelope.event_id
        })

        {:noreply, next_state}
    end
  end

  defp admit_event(envelope, state) do
    if MapSet.member?(state.seen, envelope.event_id) do
      {:dropped, state, :duplicate}
    else
      stream_key = {envelope.node_id, envelope.stream_id}
      prev_lamport = Map.get(state.stream_heads, stream_key, 0)

      if envelope.lamport <= prev_lamport do
        {:dropped, state, :non_monotone_lamport}
      else
        deps = normalize_deps(envelope.deps)

        if Enum.all?(deps, &MapSet.member?(state.seen, &1)) do
          push_to_reconcile(envelope, state.seen)
          broadcast(%{type: "sequencer_accepted", event_id: envelope.event_id})

          next = %{
            state
            | seen: MapSet.put(state.seen, envelope.event_id),
              stream_heads: Map.put(state.stream_heads, stream_key, envelope.lamport)
          }

          {:accepted, next}
        else
          broadcast(%{type: "sequencer_pending", event_id: envelope.event_id})
          next_pending = Map.put(state.pending, envelope.event_id, envelope)
          {:pending, %{state | pending: next_pending}}
        end
      end
    end
  end

  defp broadcast(payload) do
    Phoenix.PubSub.broadcast(OmegaRuntime.PubSub, "TruthEvents", {:broadcast, payload})
  end

  defp release_ready(state) do
    {ready, rest} =
      Enum.split_with(state.pending, fn {_id, ev} ->
        deps = normalize_deps(ev.deps)
        Enum.all?(deps, &MapSet.member?(state.seen, &1))
      end)

    next_state = %{state | pending: Map.new(rest)}

    Enum.reduce(ready, next_state, fn {_id, ev}, acc ->
      case admit_event(ev, acc) do
        {:accepted, s} -> s
        {:pending, s} -> s
        {:dropped, s, _} -> s
      end
    end)
  end

  defp push_to_reconcile(envelope, seen) do
    OmegaRuntime.ReconcileCoordinator.push(envelope, seen)
    OmegaRuntime.MetricsActor.emit("sequencer.accepted", 1, %{event_id: envelope.event_id})
  end

  defp normalize_deps(deps) when is_list(deps), do: deps
  defp normalize_deps(_), do: []
end

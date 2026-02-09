defmodule OmegaRuntime.IngressActor do
  @moduledoc "Ingress actor: schema and shape gate before sequencer admission."
  use GenServer

  @required_fields [:event_id, :node_id, :stream_id, :lamport, :deps, :payload]

  def start_link(_opts), do: GenServer.start_link(__MODULE__, %{}, name: __MODULE__)

  def ingest(event_envelope), do: GenServer.cast(__MODULE__, {:ingest, event_envelope})

  @impl true
  def init(state), do: {:ok, state}

  @impl true
  def handle_cast({:ingest, envelope}, state) do
    case normalize(envelope) do
      {:ok, ev} ->
        OmegaRuntime.MetricsActor.emit("ingress.events", 1, %{event_id: ev.event_id})
        OmegaRuntime.SequencerActor.enqueue(ev)

      {:error, reason} ->
        OmegaRuntime.MetricsActor.emit("ingress.malformed_ratio", 1, %{reason: reason})
    end

    {:noreply, state}
  end

  defp normalize(envelope) when is_map(envelope) do
    ev =
      envelope
      |> Enum.into(%{}, fn {k, v} -> {normalize_key(k), v} end)
      |> Map.put_new(:deps, [])
      |> Map.put_new(:payload, <<>>)

    with :ok <- require_fields(ev),
         :ok <- require_integer(ev.event_id, :event_id),
         :ok <- require_integer(ev.node_id, :node_id),
         :ok <- require_integer(ev.stream_id, :stream_id),
         :ok <- require_integer(ev.lamport, :lamport),
         :ok <- require_deps(ev.deps),
         :ok <- require_payload(ev.payload) do
      {:ok, ev}
    end
  end

  defp normalize(_), do: {:error, :not_a_map}

  defp normalize_key(k) when is_atom(k), do: k

  defp normalize_key(k) when is_binary(k) do
    case k do
      "event_id" -> :event_id
      "node_id" -> :node_id
      "stream_id" -> :stream_id
      "lamport" -> :lamport
      "deps" -> :deps
      "payload" -> :payload
      other -> other
    end
  end

  defp normalize_key(k), do: k

  defp require_fields(ev) do
    missing = Enum.reject(@required_fields, &Map.has_key?(ev, &1))
    if missing == [], do: :ok, else: {:error, {:missing_fields, missing}}
  end

  defp require_integer(v, _k) when is_integer(v) and v >= 0, do: :ok
  defp require_integer(_, k), do: {:error, {:bad_integer, k}}

  defp require_deps(deps) when is_list(deps) do
    if Enum.all?(deps, &(is_integer(&1) and &1 >= 0)), do: :ok, else: {:error, :bad_deps}
  end

  defp require_deps(_), do: {:error, :bad_deps}

  defp require_payload(payload) when is_binary(payload), do: :ok
  defp require_payload(payload) when is_list(payload), do: :ok
  defp require_payload(_), do: {:error, :bad_payload}
end

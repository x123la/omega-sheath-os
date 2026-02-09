defmodule OmegaRuntime.ReconcileCoordinator do
  @moduledoc "Coordinator actor: deterministic batch assembly and checker dispatch."
  use GenServer

  @default_batch_size 32
  @default_flush_ms 100

  def start_link(_opts) do
    state = %{queue: [], timer_ref: nil, batch_seq: 0, safe_mode: false}
    GenServer.start_link(__MODULE__, state, name: __MODULE__)
  end

  def push(event_envelope), do: GenServer.cast(__MODULE__, {:push, event_envelope})
  def flush, do: GenServer.cast(__MODULE__, :flush)
  def set_safe_mode(enabled), do: GenServer.cast(__MODULE__, {:safe_mode, enabled})

  @impl true
  def init(state), do: {:ok, state}

  @impl true
  def handle_cast({:safe_mode, enabled}, state) do
    {:noreply, %{state | safe_mode: enabled}}
  end

  @impl true
  def handle_cast({:push, envelope}, state) do
    queue = [envelope | state.queue] |> OmegaRuntime.deterministic_sort()
    next_state = %{state | queue: queue} |> ensure_timer()

    if length(queue) >= batch_size() do
      {:noreply, flush_queue(%{next_state | timer_ref: nil})}
    else
      {:noreply, next_state}
    end
  end

  @impl true
  def handle_cast(:flush, state) do
    {:noreply, flush_queue(%{state | timer_ref: nil})}
  end

  @impl true
  def handle_info(:flush_tick, state) do
    {:noreply, flush_queue(%{state | timer_ref: nil})}
  end

  defp ensure_timer(%{timer_ref: nil} = state) do
    ref = Process.send_after(self(), :flush_tick, flush_ms())
    %{state | timer_ref: ref}
  end

  defp ensure_timer(state), do: state

  defp flush_queue(%{queue: []} = state), do: state

  defp flush_queue(state) do
    batch = state.queue
    batch_id = state.batch_seq + 1

    result =
      OmegaRuntime.CheckerGateway.check(%{
        batch_id: batch_id,
        events: batch,
        checker_version: {0, 1, 0},
        schema_version: 1
      })

    case {state.safe_mode, result} do
      {true, {:merge, _}} ->
        OmegaRuntime.MetricsActor.emit("reconcile.safe_mode_merge_blocked", 1, %{
          batch_id: batch_id
        })

      _ ->
        OmegaRuntime.CertificateActor.persist(%{batch_id: batch_id, checker_result: result})
    end

    OmegaRuntime.MetricsActor.emit("reconcile.batch_size", length(batch), %{batch_id: batch_id})
    %{state | queue: [], batch_seq: batch_id}
  end

  defp batch_size do
    System.get_env("OMEGA_BATCH_SIZE", Integer.to_string(@default_batch_size))
    |> String.to_integer()
  end

  defp flush_ms do
    System.get_env("OMEGA_FLUSH_MS", Integer.to_string(@default_flush_ms))
    |> String.to_integer()
  end
end

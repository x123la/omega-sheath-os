defmodule OmegaRuntime.MetricsActor do
  @moduledoc "Append-only JSONL metrics collector actor with monotonic sequence IDs."
  use GenServer

  def start_link(_opts), do: GenServer.start_link(__MODULE__, nil, name: __MODULE__)

  def emit(metric, value, metadata \\ %{}) do
    GenServer.cast(__MODULE__, {:metric, metric, value, metadata})
  end

  @impl true
  def init(_state) do
    dir = System.get_env("OMEGA_METRICS_DIR", "/tmp/omega-runtime")
    File.mkdir_p!(dir)
    path = Path.join(dir, "metrics.jsonl")
    {:ok, %{seq: 0, path: path}}
  end

  @impl true
  def handle_cast({:metric, metric, value, metadata}, state) do
    line = encode_metric_line(state.seq, metric, value, metadata)
    File.write!(state.path, line <> "\n", [:append])
    {:noreply, %{state | seq: state.seq + 1}}
  end

  defp encode_metric_line(seq_id, metric, value, metadata) do
    md_json =
      metadata
      |> Enum.map(fn {k, v} ->
        key = OmegaRuntime.json_escape(to_string(k))
        val = OmegaRuntime.json_escape(inspect(v))
        "\"#{key}\":\"#{val}\""
      end)
      |> Enum.join(",")

    value_num = if is_number(value), do: value, else: 0

    "{" <>
      "\"seq_id\":#{seq_id}," <>
      "\"metric\":\"#{OmegaRuntime.json_escape(to_string(metric))}\"," <>
      "\"value\":#{value_num}," <>
      "\"metadata\":{#{md_json}}" <>
      "}"
  end
end

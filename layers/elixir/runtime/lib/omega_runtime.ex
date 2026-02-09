defmodule OmegaRuntime do
  @moduledoc """
  Layer B runtime helpers.

  This module centralizes deterministic ordering and digest helpers used across
  actors, ensuring ordering-critical paths are independent of arrival time.
  """

  @type event_id :: non_neg_integer()
  @type node_id :: non_neg_integer()
  @type stream_id :: non_neg_integer()
  @type lamport :: non_neg_integer()

  @spec ordering_key(map()) :: {lamport(), node_id(), stream_id(), event_id()}
  def ordering_key(%{
        lamport: lamport,
        node_id: node_id,
        stream_id: stream_id,
        event_id: event_id
      }) do
    {lamport, node_id, stream_id, event_id}
  end

  @spec deterministic_sort([map()]) :: [map()]
  def deterministic_sort(events) when is_list(events) do
    Enum.sort_by(events, &ordering_key/1)
  end

  @spec digest(binary()) :: binary()
  def digest(data) when is_binary(data) do
    :crypto.hash(:sha256, data)
  end

  @spec digest_hex(binary()) :: String.t()
  def digest_hex(data) when is_binary(data) do
    data
    |> digest()
    |> Base.encode16(case: :lower)
  end

  @spec now_ns() :: non_neg_integer()
  def now_ns do
    System.os_time(:nanosecond)
  end

  @spec json_escape(String.t()) :: String.t()
  def json_escape(text) do
    text
    |> String.replace("\\", "\\\\")
    |> String.replace("\"", "\\\"")
    |> String.replace("\n", "\\n")
    |> String.replace("\r", "\\r")
    |> String.replace("\t", "\\t")
  end
end

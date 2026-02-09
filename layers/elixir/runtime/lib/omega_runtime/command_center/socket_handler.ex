defmodule OmegaRuntime.CommandCenter.SocketHandler do
  @behaviour :cowboy_websocket

  def init(request, _state) do
    {:cowboy_websocket, request, %{}}
  end

  def websocket_init(state) do
    Phoenix.PubSub.subscribe(OmegaRuntime.PubSub, "TruthEvents")
    {:ok, state}
  end

  def websocket_handle({:text, _msg}, state) do
    # Handle incoming client commands if needed
    {:ok, state}
  end

  def websocket_info({:broadcast, event}, state) do
    {:reply, {:text, Jason.encode!(event)}, state}
  end

  def websocket_info(_info, state) do
    {:ok, state}
  end
end

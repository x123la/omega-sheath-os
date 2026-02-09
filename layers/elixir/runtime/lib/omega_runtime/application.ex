defmodule OmegaRuntime.Application do
  @moduledoc false
  use Application

  @impl true
  def start(_type, _args) do
    children = [
      {Phoenix.PubSub, name: OmegaRuntime.PubSub},
      {Task.Supervisor, name: OmegaRuntime.TaskSupervisor},
      {Registry, keys: :unique, name: OmegaRuntime.NodeRegistry},
      OmegaRuntime.MetricsActor,
      OmegaRuntime.CheckerGateway,
      OmegaRuntime.SequencerActor,
      OmegaRuntime.IngressActor,
      OmegaRuntime.ReconcileCoordinator,
      OmegaRuntime.CertificateActor,
      OmegaRuntime.SnapshotActor,
      OmegaRuntime.ReplayActor,
      {Plug.Cowboy,
       scheme: :http,
       plug: OmegaRuntime.CommandCenter.Router,
       options: [port: 4000, dispatch: dispatch()]}
    ]

    IO.puts "[omega] Kernel and Command Center live at http://localhost:4000"
    Supervisor.start_link(children, strategy: :one_for_one, name: OmegaRuntime.Supervisor)
  end

  defp dispatch do
    [
      {:_,
       [
         {"/ws", OmegaRuntime.CommandCenter.SocketHandler, []},
         {:_, Plug.Cowboy.Handler, {OmegaRuntime.CommandCenter.Router, []}}
       ]}
    ]
  end
end

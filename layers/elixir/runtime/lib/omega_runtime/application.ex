defmodule OmegaRuntime.Application do
  @moduledoc false
  use Application

  @impl true
  def start(_type, _args) do
    children = [
      {Task.Supervisor, name: OmegaRuntime.TaskSupervisor},
      OmegaRuntime.MetricsActor,
      OmegaRuntime.CheckerGateway,
      OmegaRuntime.SequencerActor,
      OmegaRuntime.IngressActor,
      OmegaRuntime.ReconcileCoordinator,
      OmegaRuntime.CertificateActor,
      OmegaRuntime.SnapshotActor,
      OmegaRuntime.ReplayActor
    ]

    Supervisor.start_link(children, strategy: :one_for_one, name: OmegaRuntime.Supervisor)
  end
end

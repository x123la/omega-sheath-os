defmodule OmegaRuntime.MixProject do
  use Mix.Project

  def project do
    [
      app: :omega_runtime,
      version: "0.1.0",
      elixir: "~> 1.16",
      start_permanent: Mix.env() == :prod,
      deps: []
    ]
  end

  def application do
    [
      extra_applications: [:logger],
      mod: {OmegaRuntime.Application, []}
    ]
  end
end

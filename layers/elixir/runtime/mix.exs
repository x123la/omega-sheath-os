defmodule OmegaRuntime.MixProject do
  use Mix.Project

  def project do
    [
      app: :omega_runtime,
      version: "0.1.0",
      elixir: "~> 1.16",
      start_permanent: Mix.env() == :prod,
      deps: [
        {:phoenix_pubsub, "~> 2.1"},
        {:plug_cowboy, "~> 2.0"},
        {:jason, "~> 1.4"},
        {:cors_plug, "~> 3.0"}
      ]
    ]
  end

  def application do
    [
      extra_applications: [:logger],
      mod: {OmegaRuntime.Application, []}
    ]
  end
end

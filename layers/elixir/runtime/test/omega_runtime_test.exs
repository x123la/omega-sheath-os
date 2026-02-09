defmodule OmegaRuntimeTest do
  use ExUnit.Case

  setup_all do
    {:ok, _} = Application.ensure_all_started(:omega_runtime)
    :ok
  end

  test "deterministic sort respects canonical ordering key" do
    events = [
      %{event_id: 9, node_id: 2, stream_id: 1, lamport: 7},
      %{event_id: 4, node_id: 1, stream_id: 1, lamport: 7},
      %{event_id: 2, node_id: 1, stream_id: 1, lamport: 5}
    ]

    sorted = OmegaRuntime.deterministic_sort(events)
    assert Enum.map(sorted, & &1.event_id) == [2, 4, 9]
  end

  test "checker gateway returns merge for valid batch" do
    batch = %{
      batch_id: 1,
      events: [
        %{event_id: 1, node_id: 1, stream_id: 1, lamport: 1, deps: [], payload: <<1>>},
        %{event_id: 2, node_id: 1, stream_id: 1, lamport: 2, deps: [1], payload: <<2>>}
      ],
      checker_version: {0, 1, 0},
      schema_version: 1
    }

    assert {:merge, body} = OmegaRuntime.CheckerGateway.check(batch)
    assert body.accepted_event_ids == [1, 2]
  end

  test "checker gateway returns obstruction on missing dependency" do
    batch = %{
      batch_id: 1,
      events: [
        %{event_id: 1, node_id: 1, stream_id: 1, lamport: 1, deps: [], payload: <<1>>},
        %{event_id: 2, node_id: 1, stream_id: 1, lamport: 2, deps: [9], payload: <<2>>}
      ],
      checker_version: {0, 1, 0},
      schema_version: 1
    }

    assert {:obstruction, body} = OmegaRuntime.CheckerGateway.check(batch)
    assert body.violated_predicate_id == 2002
  end

  test "certificate actor appends certificate files" do
    cert_dir = System.get_env("OMEGA_CERT_DIR", "/tmp/omega-runtime/certs")

    OmegaRuntime.CertificateActor.persist(%{
      batch_id: 42,
      checker_result: {:merge, %{accepted_event_ids: [1], witness_hash: "abc"}}
    })

    Process.sleep(50)

    assert File.exists?(Path.join(cert_dir, "cert.log"))
    assert File.exists?(Path.join(cert_dir, "cert.idx"))
    assert File.exists?(Path.join(cert_dir, "cert.hash"))
  end
end

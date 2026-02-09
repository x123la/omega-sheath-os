defmodule OmegaRuntime.CertificateActor do
  @moduledoc "Certificate actor: build, sign, and persist append-only cert log + sidecars."
  use GenServer

  def start_link(_opts), do: GenServer.start_link(__MODULE__, nil, name: __MODULE__)

  def persist(payload), do: GenServer.cast(__MODULE__, {:persist, payload})

  @impl true
  def init(_state) do
    cert_dir = System.get_env("OMEGA_CERT_DIR", "/tmp/omega-runtime/certs")
    File.mkdir_p!(cert_dir)

    {pub, priv} = :crypto.generate_key(:eddsa, :ed25519)
    key_id = pub |> binary_part(0, 16)

    state = %{
      cert_dir: cert_dir,
      key_id: key_id,
      priv: priv,
      seq: 0,
      prev_hash: <<0::256>>
    }

    {:ok, state}
  end

  @impl true
  def handle_cast({:persist, %{batch_id: batch_id, checker_result: checker_result}}, state) do
    cert = build_envelope(state, checker_result, batch_id)

    case append_certificate(state.cert_dir, cert, state.seq) do
      {:ok, cert_hash} ->
        OmegaRuntime.MetricsActor.emit("cert.persist", 1, %{batch_id: batch_id})
        {:noreply, %{state | seq: state.seq + 1, prev_hash: cert_hash}}

      {:error, reason} ->
        OmegaRuntime.MetricsActor.emit("cert.persist_fail", 1, %{reason: inspect(reason)})
        {:noreply, state}
    end
  end

  def handle_cast({:persist, _unexpected}, state), do: {:noreply, state}

  defp build_envelope(state, checker_result, batch_id) do
    {cert_type, body} =
      case checker_result do
        {:merge, body} ->
          {"Merge", body}

        {:obstruction, body} ->
          {"Obstruction", body}
      end

    body_bin = :erlang.term_to_binary(body)
    body_hash = OmegaRuntime.digest(body_bin)

    base = %{
      cert_id: cert_id(),
      cert_type: cert_type,
      trace_root_hash: body_hash,
      checker_version: {0, 1, 0},
      schema_version: 1,
      batch_id: batch_id,
      created_at_ns: OmegaRuntime.now_ns(),
      issuer_key_id: state.key_id,
      body: body,
      body_hash: body_hash,
      prev_cert_hash: state.prev_hash
    }

    signable = :erlang.term_to_binary(base)
    signature = :crypto.sign(:eddsa, :none, signable, [state.priv, :ed25519])
    Map.put(base, :signature, signature)
  end

  defp append_certificate(cert_dir, cert, seq) do
    encoded = :erlang.term_to_binary(cert)
    cert_hash = OmegaRuntime.digest(encoded)

    log_path = Path.join(cert_dir, "cert.log")
    idx_path = Path.join(cert_dir, "cert.idx")
    hash_path = Path.join(cert_dir, "cert.hash")

    with {:ok, log} <- :file.open(String.to_charlist(log_path), [:append, :binary]),
         {:ok, offset} <- :file.position(log, :eof),
         :ok <- :file.write(log, encoded),
         :ok <- :file.write(log, <<"\n">>),
         :ok <- :file.close(log),
         :ok <-
           File.write(
             idx_path,
             "#{cert.cert_id} #{offset}\n",
             [:append]
           ),
         :ok <-
           File.write(
             hash_path,
             "#{seq} #{Base.encode16(cert_hash, case: :lower)}\n",
             [:append]
           ) do
      {:ok, cert_hash}
    end
  end

  defp cert_id do
    :crypto.strong_rand_bytes(16)
    |> :binary.decode_unsigned()
  end
end

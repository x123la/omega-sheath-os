defmodule OmegaRuntime.CertificateActor do
  @moduledoc "Certificate actor: build, sign, and persist append-only cert log + sidecars."
  use GenServer

  def start_link(_opts), do: GenServer.start_link(__MODULE__, nil, name: __MODULE__)

  def persist(payload), do: GenServer.cast(__MODULE__, {:persist, payload})
  def collect_vote(cert, signature), do: GenServer.cast(__MODULE__, {:vote, cert, signature})

  @impl true
  def init(_state) do
    cert_dir = System.get_env("OMEGA_CERT_DIR", "/tmp/omega-runtime/certs")
    File.mkdir_p!(cert_dir)
    
    # Quorum peers for BFT-ready consensus
    nodes = System.get_env("OMEGA_NODES", "") |> String.split(",", trim: true) |> Enum.map(&String.to_atom/1)

    # Load persistent key from repo root or generate one
    key_path = System.get_env("OMEGA_KEY_PATH", "omega.key")
    {pub, priv} = case File.read(key_path) do
      {:ok, <<priv_bytes::binary-size(32)>>} ->
        :crypto.generate_key(:eddsa, :ed25519, priv_bytes)
      _ ->
        {p, s} = :crypto.generate_key(:eddsa, :ed25519)
        File.write!(key_path, s)
        {p, s}
    end
    
    key_id = pub |> binary_part(0, 16)

    state = %{
      cert_dir: cert_dir,
      key_id: key_id,
      priv: priv,
      seq: 0,
      prev_hash: <<0::256>>,
      quorum_nodes: nodes,
      pending_quorum: %{} # cert_id -> [signatures]
    }

    {:ok, state}
  end

  @impl true
  def handle_cast({:persist, %{batch_id: batch_id, checker_result: checker_result}}, state) do
    cert = build_envelope(state, checker_result, batch_id)
    
    # Broadcast to quorum nodes
    Enum.each(state.quorum_nodes, fn node -> 
      GenServer.cast({__MODULE__, node}, {:vote, cert, cert.signature})
    end)

    # Add our own vote
    {:noreply, process_vote(state, cert, cert.signature)}
  end

  @impl true
  def handle_cast({:vote, cert, signature}, state) do
    # Verify the signature before accepting the vote
    type_int = if cert.cert_type == "Merge", do: 1, else: 2
    signable = binary_envelope_message(cert, type_int)
    
    if :crypto.verify(:eddsa, :none, signable, signature, [cert.issuer_key_id, :ed25519]) do
       {:noreply, process_vote(state, cert, signature)}
    else
       OmegaRuntime.MetricsActor.emit("cert.invalid_vote", 1, %{cert_id: cert.cert_id})
       {:noreply, state}
    end
  end

  @impl true
  def handle_cast({:persist, _unexpected}, state), do: {:noreply, state}

  defp process_vote(state, cert, signature) do
    votes = Map.get(state.pending_quorum, cert.cert_id, [])
    # Unique signatures only
    new_votes = Enum.uniq([signature | votes])
    
    quorum_size = length(state.quorum_nodes)
    # Ensure at least 1 (our own) if no quorum nodes defined
    quorum_threshold = if quorum_size == 0, do: 1, else: quorum_size
    
    if length(new_votes) >= quorum_threshold do
      # FINALIZED
      final_cert = Map.put(cert, :quorum_signatures, new_votes)
      case append_certificate(state.cert_dir, final_cert, state.seq) do
        {:ok, cert_hash} ->
          OmegaRuntime.MetricsActor.emit("cert.finalized", 1, %{batch_id: cert.batch_id})
          broadcast(%{
            type: "certificate_finalized", 
            cert_id: cert.cert_id, 
            cert_type: cert.cert_type, 
            quorum_size: length(new_votes),
            batch_id: cert.batch_id
          })
          %{state | seq: state.seq + 1, prev_hash: cert_hash, pending_quorum: Map.delete(state.pending_quorum, cert.cert_id)}
        _ ->
          state
      end
    else
      broadcast(%{type: "certificate_pending", cert_id: cert.cert_id, votes: length(new_votes)})
      %{state | pending_quorum: Map.put(state.pending_quorum, cert.cert_id, new_votes)}
    end
  end

  defp broadcast(payload) do
    Phoenix.PubSub.broadcast(OmegaRuntime.PubSub, "TruthEvents", {:broadcast, payload})
  end

  defp build_envelope(state, checker_result, batch_id) do
    {cert_type, body_bytes, trace_root_hash} =
      case checker_result do
        {:merge, %{accepted_event_ids: ids} = body} ->
          # Match Rust: hash_ids of accepted_event_ids
          root = Enum.reduce(ids, :crypto.hash_init(:sha256), fn id, acc ->
            :crypto.hash_update(acc, <<id::little-size(128)>>)
          end) |> :crypto.hash_final()
          
          # Binary Body: merged_state + frontier_digest + count + witness + replay_seed
          buf = body.merged_state_hash <> 
                body.accepted_ids_digest <> 
                <<length(ids)::little-size(32)>> <> 
                body.witness_hash <> 
                <<42::little-size(64)>> # Seed placeholder

          {"Merge", buf, root}

        {:obstruction, %{conflict_set: ids} = body} ->
          # Match Rust: hash_ids of SORTED conflict_set
          sorted = Enum.sort(ids)
          root = Enum.reduce(sorted, :crypto.hash_init(:sha256), fn id, acc ->
            :crypto.hash_update(acc, <<id::little-size(128)>>)
          end) |> :crypto.hash_final()

          # Binary Body: conflict_len + ids + payload_len + payloads + predicate + witness
          ids_bin = Enum.map_join(sorted, "", &<<&1::little-size(128)>>)
          payloads_bin = Enum.map_join(body.conflicting_payload_hashes, "", & &1)
          
          buf = <<length(ids)::little-size(32)>> <> 
                ids_bin <> 
                <<length(body.conflicting_payload_hashes)::little-size(32)>> <>
                payloads_bin <>
                <<body.violated_predicate_id::little-size(32)>> <>
                body.witness_hash

          {"Obstruction", buf, root}
      end

    body_hash = OmegaRuntime.digest(body_bytes)

    base = %{
      cert_id: cert_id(batch_id, state.prev_hash),
      cert_type: cert_type,
      trace_root_hash: trace_root_hash,
      checker_version: {0, 1, 0},
      schema_version: 1,
      batch_id: batch_id,
      created_at_ns: OmegaRuntime.now_ns(),
      issuer_key_id: state.key_id,
      body_bytes: body_bytes,
      body_hash: body_hash,
      prev_cert_hash: state.prev_hash
    }

    type_int = if cert_type == "Merge", do: 1, else: 2
    signable_bin = binary_envelope_message(base, type_int)
    
    signature = :crypto.sign(:eddsa, :none, signable_bin, [state.priv, :ed25519])
    Map.put(base, :signature, signature)
  end

  defp binary_envelope_message(e, type_int) do
    # Match Rust packed binary: cert_id, type, trace_root, checker_v(3*u16), schema_v, batch, created, issuer_key_id, body_hash, prev_hash
    <<e.cert_id::little-size(128)>> <>
    <<type_int::8>> <>
    e.trace_root_hash <>
    <<0::little-size(16), 1::little-size(16), 0::little-size(16)>> <>
    <<e.schema_version::little-size(16)>> <>
    <<e.batch_id::little-size(64)>> <>
    <<e.created_at_ns::little-size(64)>> <>
    e.issuer_key_id <>
    e.body_hash <>
    e.prev_cert_hash
  end

  defp append_certificate(cert_dir, cert, seq) do
    # Log still uses JSON for the envelope for readability/CLI,
    # but the content is backed by the rigid binary hashes.
    encoded = """
    {
      "cert_id": #{cert.cert_id},
      "cert_type": "#{cert.cert_type}",
      "trace_root_hash": #{json_array(cert.trace_root_hash)},
      "checker_version": [0, 1, 0],
      "schema_version": #{cert.schema_version},
      "batch_id": #{cert.batch_id},
      "created_at_ns": #{cert.created_at_ns},
      "issuer_key_id": #{json_array(cert.issuer_key_id)},
      "body_bytes": #{json_array(cert.body_bytes)},
      "body_hash": #{json_array(cert.body_hash)},
      "signature": #{json_array(cert.signature)},
      "prev_cert_hash": #{json_array(cert.prev_cert_hash)},
      "quorum_signatures": []
    }
    """
    # Remove newlines/multispace from the template for single-line log format
    encoded = String.replace(encoded, ~r/\s+/, " ") |> String.replace("{ ", "{") |> String.replace(" }", "}")

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

  defp json_array(bin) when is_binary(bin) do
    content = :binary.bin_to_list(bin) |> Enum.join(",")
    "[#{content}]"
  end

  defp cert_id(batch_id, prev_hash) do
    # Incorporate prev_hash for higher entropy
    <<seed_tail::integer-size(32), _::binary>> = prev_hash
    :rand.seed(:exsss, {batch_id, seed_tail, 42})
    :rand.uniform(Bitwise.bsl(1, 128)) - 1
  end
end
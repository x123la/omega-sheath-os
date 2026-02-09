defmodule OmegaRuntime.CommandCenter.Router do
  use Plug.Router

  plug(Plug.Static,
    at: "/",
    from: :omega_runtime,
    gzip: false
  )
  plug(CORSPlug)
  plug(:match)
  plug(Plug.Parsers,
    parsers: [:json],
    pass: ["application/json"],
    json_decoder: Jason
  )
  plug(:dispatch)

  get "/" do
    conn
    |> put_resp_header("content-type", "text/html")
    |> send_file(200, "priv/static/index.html")
  end

  get "/api/status" do
    status = %{
      node: node(),
      kernel: "OMEGA-SHEAF-OS",
      state: "Mathematically Consistent"
    }
    send_resp(conn, 200, Jason.encode!(status))
  end

  post "/api/ingest" do
    OmegaRuntime.IngressActor.ingest(conn.body_params)
    send_resp(conn, 202, Jason.encode!(%{status: "accepted"}))
  end

  match _ do
    send_resp(conn, 404, "Not Found")
  end
end

#!/bin/sh
# Serve the relation map on localhost at a free random port and open it.
# Usage: docs/explorer/serve.sh   (Ctrl-C stops the server)
cd "$(dirname "$0")" || exit 1
exec python3 - <<'EOF'
import functools, http.server, random, socket, socketserver, webbrowser

def free_port():
    for _ in range(50):
        p = random.randint(20000, 60000)
        with socket.socket() as s:
            try:
                s.bind(("127.0.0.1", p))
                return p
            except OSError:
                pass
    raise SystemExit("no free port found")

port = free_port()
handler = functools.partial(http.server.SimpleHTTPRequestHandler, directory=".")
handler.log_message = lambda *a: None
with socketserver.TCPServer(("127.0.0.1", port), handler) as httpd:
    url = f"http://127.0.0.1:{port}/explorer.html"
    print(f"Relation map at {url}  (Ctrl-C to stop)", flush=True)
    try:
        webbrowser.open(url)
    except Exception:
        pass
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
EOF

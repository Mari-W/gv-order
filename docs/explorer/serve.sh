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

class Handler(http.server.SimpleHTTPRequestHandler):
    # The page POSTs what the reader points at; keep the latest in .cursor.json
    # and the last 200 events in .cursor.log, so the assistant can follow along.
    def do_POST(self):
        if self.path.rstrip("/").endswith("/cursor"):
            n = int(self.headers.get("Content-Length") or 0)
            body = self.rfile.read(min(n, 65536)).decode("utf-8", "replace")
            with open(".cursor.json", "w") as f:
                f.write(body + "\n")
            try:
                with open(".cursor.log") as f:
                    lines = f.readlines()[-199:]
            except OSError:
                lines = []
            with open(".cursor.log", "w") as f:
                f.writelines(lines + [body + "\n"])
            self.send_response(204)
            self.end_headers()
        else:
            self.send_error(404)
    def log_message(self, *a):
        pass

port = free_port()
handler = functools.partial(Handler, directory=".")
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

#!/usr/bin/env python3
"""Serve a proof map on localhost and open it in a browser.

usage: python3 -I serve.py <map.json> [--port N] [--no-open]

The server roots itself at the common parent of the page and the map, so the page loads the map,
its extension scripts and MathJax from the CDN. GET /__version answers the modification times of
the page and the map, and the page reloads itself when they change.
"""
import functools, http.server, os, random, socket, socketserver, sys, urllib.parse, webbrowser

args = sys.argv[1:]
if not args:
    sys.exit(__doc__)
port = None
if "--port" in args:
    i = args.index("--port"); port = int(args[i + 1]); del args[i:i + 2]
no_open = "--no-open" in args
args = [a for a in args if a != "--no-open"]
here = os.path.dirname(os.path.abspath(__file__))
page = os.path.join(here, "page", "index.html")
mapf = os.path.abspath(args[0])
root = os.path.commonpath([os.path.dirname(page), os.path.dirname(mapf)])
rel = lambda p: os.path.relpath(p, root).replace(os.sep, "/")


class Handler(http.server.SimpleHTTPRequestHandler):
    def do_GET(self):
        u = urllib.parse.urlparse(self.path)
        if u.path.endswith("/__version"):
            files = [page, mapf]
            body = ",".join(str(os.stat(f).st_mtime_ns) for f in files if os.path.exists(f)).encode()
            self.send_response(200)
            self.send_header("Content-Type", "text/plain")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        super().do_GET()

    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def log_message(self, *a):
        pass


def free_port():
    for _ in range(50):
        p = random.randint(20000, 60000)
        with socket.socket() as s:
            try:
                s.bind(("127.0.0.1", p)); return p
            except OSError:
                pass
    sys.exit("no free port")


port = port or free_port()
map_url = os.path.relpath(mapf, os.path.dirname(page)).replace(os.sep, "/")
url = f"http://127.0.0.1:{port}/{rel(page)}?map={urllib.parse.quote(map_url)}"
with socketserver.TCPServer(("127.0.0.1", port), functools.partial(Handler, directory=root)) as httpd:
    print(f"proof map at {url}  (Ctrl-C stops)", flush=True)
    if not no_open:
        try: webbrowser.open(url)
        except Exception: pass
    try: httpd.serve_forever()
    except KeyboardInterrupt: pass

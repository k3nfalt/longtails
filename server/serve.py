import argparse
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parent


class Handler(BaseHTTPRequestHandler):
    def respond(self, code, body, content_type="application/json"):
        self.send_response(code)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("Referrer-Policy", "no-referrer")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        url = urlsplit(self.path)
        if url.path not in ("/", "/index.html"):
            self.respond(404, b'"Not found"')
            return
        self.respond(
            200, (ROOT / "index.html").read_bytes(), "text/html; charset=utf-8"
        )

    def log_message(self, format, *args):
        pass


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Serve the generated website.")
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8000)
    args = parser.parse_args()
    with HTTPServer((args.host, args.port), Handler) as server:
        base = f"http://{args.host}:{server.server_port}"
        print(f"Website: {base}/", flush=True)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass

"""Inside the private network namespace: relay only to the supervisor's API proxy."""
import os
import select
import socket
import socketserver
import subprocess
import sys
import threading


class Relay(socketserver.BaseRequestHandler):
    def handle(self):
        with socket.socket(socket.AF_UNIX) as upstream:
            upstream.connect('/run/api-proxy.sock')
            peers = [self.request, upstream]
            while True:
                ready, _, _ = select.select(peers, [], [], 1800)
                if not ready:
                    return
                for source in ready:
                    data = source.recv(65536)
                    if not data:
                        return
                    (upstream if source is self.request else self.request).sendall(data)


class Server(socketserver.ThreadingTCPServer):
    daemon_threads = True


if __name__ == '__main__':
    with Server(('127.0.0.1', 0), Relay) as server:
        threading.Thread(target=server.serve_forever, daemon=True).start()
        proxy = f'http://127.0.0.1:{server.server_address[1]}'
        env = dict(os.environ, HTTPS_PROXY=proxy, HTTP_PROXY=proxy,
                   https_proxy=proxy, http_proxy=proxy, ALL_PROXY=proxy, NO_PROXY='')
        result = subprocess.run(sys.argv[1:], env=env)
        server.shutdown()
        sys.exit(result.returncode)

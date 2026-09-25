"""Allowlisted HTTPS CONNECT broker. No host-loopback network is exposed to workers."""
import contextlib
import ipaddress
from pathlib import Path
import select
import socket
import socketserver
import threading

ALLOWED = frozenset({'api.openai.com', 'chatgpt.com', 'auth.openai.com'})


def destination(line):
    method, authority, version = line.split()
    host, port = authority.rsplit(':', 1)
    if method != 'CONNECT' or version not in ('HTTP/1.0', 'HTTP/1.1') or host not in ALLOWED or port != '443':
        raise ValueError('Destination denied')
    return host


class Handler(socketserver.BaseRequestHandler):
    def handle(self):
        self.request.settimeout(30)
        try:
            header = b''
            while b'\r\n\r\n' not in header:
                chunk = self.request.recv(1)
                if not chunk or len(header) >= 8192:
                    raise ValueError('Invalid CONNECT header')
                header += chunk
            host = destination(header.split(b'\r\n', 1)[0].decode('ascii'))
            upstream = None
            for family, socktype, protocol, _, address in socket.getaddrinfo(host, 443, type=socket.SOCK_STREAM):
                if not ipaddress.ip_address(address[0]).is_global:
                    continue
                candidate = socket.socket(family, socktype, protocol)
                candidate.settimeout(20)
                try:
                    candidate.connect(address)  # Connect to the checked address; no DNS re-resolution.
                    upstream = candidate
                    break
                except OSError:
                    candidate.close()
            if upstream is None:
                raise ValueError('No permitted upstream')
            with upstream:
                self.request.sendall(b'HTTP/1.1 200 Connection Established\r\n\r\n')
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
        except (ValueError, UnicodeError, OSError):
            with contextlib.suppress(OSError):
                self.request.sendall(b'HTTP/1.1 403 Forbidden\r\nContent-Length: 0\r\n\r\n')


class Server(socketserver.ThreadingUnixStreamServer):
    daemon_threads = True


@contextlib.contextmanager
def broker(path):
    path = Path(path)
    with Server(str(path), Handler) as server:
        threading.Thread(target=server.serve_forever, daemon=True).start()
        try:
            yield path
        finally:
            server.shutdown()
    path.unlink(missing_ok=True)

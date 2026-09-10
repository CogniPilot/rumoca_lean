#!/usr/bin/env python3
"""One real stdio session checks the LSP/editor infrastructure boundary.
Parser semantics and range invariants are checked by the Lean package audit.
"""
import json
import select
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SERVER = ROOT / "packages/lsp/.lake/build/bin/rumoca-lsp"
URI = "file:///rumoca-lsp/Integrator.mo"
GOOD = "model Integrator\r\n  Real x;\r\nequation\r\n  der(x) = 1;\r\nend Integrator;\r\n"


def send(proc, method, params=None, request=None):
    message = {"jsonrpc": "2.0", "method": method}
    if params is not None:
        message["params"] = params
    if request is not None:
        message["id"] = request
    body = json.dumps(message, ensure_ascii=False).encode()
    proc.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode() + body)
    proc.stdin.flush()


def receive(proc):
    # Pipes are unbuffered so select observes every frame, including bursts.
    def line():
        data = bytearray()
        while not data.endswith(b"\n"):
            assert select.select([proc.stdout], [], [], 15)[0], "LSP response timed out"
            char = proc.stdout.read(1)
            assert char, "LSP closed output early"
            data.extend(char)
        return bytes(data)

    headers = {}
    while (entry := line()) != b"\r\n":
        key, value = entry.decode().split(":", 1)
        headers[key.lower()] = value.strip()
    size = int(headers["content-length"])
    body = bytearray()
    while len(body) < size:
        assert select.select([proc.stdout], [], [], 15)[0], "LSP body timed out"
        chunk = proc.stdout.read(size - len(body))
        assert chunk, "LSP closed output during a frame"
        body.extend(chunk)
    return json.loads(body)


def query(proc, method, ident, line=3, character=6):
    send(proc, method, {"textDocument": {"uri": URI}, "position": {
        "line": line, "character": character}}, request=ident)
    response = receive(proc)
    assert response["id"] == ident, response
    return response


def change(proc, version, text):
    send(proc, "textDocument/didChange", {"textDocument": {"uri": URI, "version": version},
        "contentChanges": [{"text": text}]})


def diagnostics(proc, version):
    message = receive(proc)
    assert message["method"] == "textDocument/publishDiagnostics", message
    assert message["params"]["version"] == version, message
    return message["params"]["diagnostics"]


with subprocess.Popen([str(SERVER)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                      stderr=subprocess.PIPE, bufsize=0) as proc:
    try:
        assert query(proc, "textDocument/hover", 1)["error"]["code"] == -32002
        send(proc, "initialize", {"processId": None, "rootUri": None,
                                  "capabilities": {}}, request=2)
        response = receive(proc)
        assert response["id"] == 2, response
        caps = response["result"]["capabilities"]
        assert caps["positionEncoding"] == "utf-16" and caps["textDocumentSync"]["change"] == 1
        send(proc, "initialized", {})
        send(proc, "textDocument/didOpen", {"textDocument": {"uri": URI,
            "languageId": "modelica", "version": -1, "text": GOOD}})
        assert diagnostics(proc, -1) == []
        result = query(proc, "textDocument/definition", 3)["result"]
        assert result == {"uri": URI, "range": {"start": {"line": 1, "character": 7},
                                                  "end": {"line": 1, "character": 8}}}, result
        assert "Real x" in query(proc, "textDocument/hover", 4)["result"]["contents"]["value"]
        assert query(proc, "textDocument/hover", 5, 3, 1000000000)["result"] is None
        change(proc, 0, GOOD.replace("der(x)", "der(y)"))
        error = diagnostics(proc, 0)[0]
        assert error["code"] == "resolve" and error["range"] == {
            "start": {"line": 3, "character": 6}, "end": {"line": 3, "character": 7}}, error
        assert query(proc, "textDocument/definition", 6)["result"] is None
        change(proc, -1, GOOD)  # Stale notification emits no result and cannot change the snapshot.
        assert query(proc, "textDocument/definition", 7)["result"] is None
        change(proc, 1, GOOD.replace("end Integrator", "end Different"))
        error = diagnostics(proc, 1)[0]
        assert error["range"]["start"] == {"line": 4, "character": 4}, error
        change(proc, 2, GOOD + "😀")
        error = diagnostics(proc, 2)[0]
        assert error["code"] == "lex" and error["range"] == {
            "start": {"line": 5, "character": 0}, "end": {"line": 5, "character": 2}}, error
        change(proc, 3, GOOD.rstrip()[:-1])
        error = diagnostics(proc, 3)[0]
        assert error["code"] == "parse" and error["range"]["start"] == error["range"]["end"], error
        change(proc, 4, GOOD)
        assert diagnostics(proc, 4) == []
        send(proc, "textDocument/didChange", {"textDocument": {"uri": URI, "version": 5},
            "contentChanges": [{"range": {}, "text": "corrupt"}]})
        assert receive(proc)["method"] == "window/logMessage"
        assert query(proc, "textDocument/definition", 8)["result"]["uri"] == URI
        assert query(proc, "notSupported", 9)["error"]["code"] == -32601
        send(proc, "textDocument/didClose", {"textDocument": {"uri": URI}})
        assert receive(proc)["params"]["diagnostics"] == []
        assert query(proc, "textDocument/hover", 10)["result"] is None
        send(proc, "shutdown", request=11)
        assert receive(proc) == {"jsonrpc": "2.0", "id": 11, "result": None}
        send(proc, "exit")
        assert proc.wait(timeout=10) == 0
        assert proc.stderr.read() == b""
    finally:
        if proc.poll() is None:
            proc.kill()
            proc.wait()
print("LSP stdio, diagnostics, CRLF/UTF-16, navigation and snapshot checks passed")

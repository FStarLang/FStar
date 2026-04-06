---
name: fstarmcp
description: Use the F* MCP server for interactive, incremental typechecking of F* and Pulse code
---

## Overview

The F* MCP server (`fstar-mcp`) provides an HTTP API wrapping F*'s `--ide` protocol.
It enables **incremental typechecking**: create a session once, then re-typecheck modified
code without restarting F* or reloading dependencies. This dramatically speeds up iterative
proof development.

Binary location: `../fstar-mcp/target/release/fstar-mcp` (relative to the FStar repo root).

## MCP Registration

The server is registered in `.copilot/mcp-config.json` at the repo root as an `http` type
server on `http://localhost:3001/`. Copilot CLI will auto-connect when the server is running.

## Starting the Server

The server must be started before Copilot CLI can use it:

```bash
# Start on port 3001 (matches mcp-config.json)
FSTAR_MCP_PORT=3001 ../fstar-mcp/target/release/fstar-mcp &

# With debug logging
RUST_LOG=fstar_mcp=debug FSTAR_MCP_PORT=3001 ../fstar-mcp/target/release/fstar-mcp &
```

The server runs on `http://127.0.0.1:3001`. All API calls are JSON-RPC 2.0 POST requests to `/`.

## API Protocol

All requests use JSON-RPC 2.0 over HTTP POST to the root endpoint `/`:

```bash
curl -s -X POST http://localhost:3001/ \
  -H 'Content-Type: application/json' \
  -H 'Accept: application/json' \
  -d '{"jsonrpc": "2.0", "method": "tools/call", "id": 1, "params": {"name": "TOOL_NAME", "arguments": {...}}}'
```

Responses contain `result.content[0].text` with a JSON string that must be parsed again.

## Workflow

### 1. Create a Session

```bash
curl -s -X POST http://localhost:3001/ \
  -H 'Content-Type: application/json' \
  -d '{"jsonrpc":"2.0","method":"tools/call","id":1,"params":{"name":"create_session","arguments":{
    "file_path": "/path/to/Module.fst",
    "cwd": "/project/root",
    "include_dirs": ["/path/to/lib", "/path/to/specs"],
    "options": ["--cache_dir", "/path/to/obj", "--already_cached", "Prims FStar"]
  }}}'
```

**Parameters:**
- `file_path` (string, optional): Path to the F* file. Must exist on disk. If omitted, creates a temp file.
- `cwd` (string, optional): Working directory. Defaults to file's directory.
- `include_dirs` (string[], optional): Directories for `--include`.
- `options` (string[], optional): Extra F* CLI options.

**Returns:** `session_id`, `status` ("ok"/"error"), `diagnostics[]`, `fragments[]`

The initial `create_session` typechecks the file's current contents on disk. The returned
`session_id` is used for all subsequent operations.

### 2. Typecheck Modified Code

```bash
curl -s -X POST http://localhost:3001/ \
  -d '{"jsonrpc":"2.0","method":"tools/call","id":2,"params":{"name":"typecheck_buffer","arguments":{
    "session_id": "UUID",
    "code": "module Foo\nlet x = 42",
    "kind": "full"
  }}}'
```

**Parameters:**
- `session_id` (string, required): From `create_session`.
- `code` (string, required): Full module source code. Must start with matching `module` declaration.
- `lax` (boolean, optional): Shortcut for `kind: "lax"`.
- `kind` (string, optional): `"full"` (default), `"lax"`, `"cache"`, `"reload-deps"`, `"verify-to-position"`, `"lax-to-position"`.
- `to_line` / `to_column` (integer, optional): For position-based kinds.

**Returns:** `status`, `diagnostics[]`, `fragments[]`

Each fragment has `start_line`, `end_line`, `start_column`, `end_column`, and `status` ("ok"/"failed").

### 3. Look Up Symbols

```bash
curl -s -X POST http://localhost:3001/ \
  -d '{"jsonrpc":"2.0","method":"tools/call","id":3,"params":{"name":"lookup_symbol","arguments":{
    "session_id": "UUID",
    "file_path": "/path/to/Module.fst",
    "line": 10, "column": 5,
    "symbol": "my_function"
  }}}'
```

**Returns:** `kind` ("symbol"/"module"/"not_found"), `name`, `type_info`, `defined_at`.

### 4. Other Tools

- **`list_sessions`**: List all active sessions with their file paths.
- **`restart_solver`**: Restart Z3 for a session (useful when solver gets stuck).
- **`get_proof_context`**: Get proof obligations from tactic-based proofs.
- **`update_buffer`**: Add/update files in F*'s virtual file system (vfs-add) for dependency resolution.
- **`close_session`**: Clean up a session.

## HaclPulse Configuration

For verifying HaclPulse code, use these include dirs and options:

```json
{
  "file_path": "/path/to/HaclPulse/code/sha3/Module.fst",
  "cwd": "/path/to/HaclPulse",
  "include_dirs": [
    "lib", "specs",
    "code/sha3", "code/chacha20", "code/salsa20", "code/sha2",
    "code/blake2", "code/curve25519", "code/poly1305",
    "obj",
    "../pulse/out/lib/pulse", "../pulse/out/lib/pulse/lib",
    "../karamel/krmllib", "../karamel/krmllib/obj"
  ],
  "options": [
    "--cache_dir", "obj",
    "--already_cached", "Prims FStar LowStar C Spec.Loops TestLib WasmSupport PulseCore Pulse.Lib Pulse.Class Pulse.Main",
    "--ext", "pulse:rvalues",
    "--ext", "fly_deps",
    "--ext", "optimize_let_vc",
    "--warn_error", "@240+241@247-272-274-288@319@328@331@332@337"
  ]
}
```

## Tips

- **Incremental workflow**: Create session once (slow, loads deps), then `typecheck_buffer`
  repeatedly (fast, only re-checks changed fragments).
- **Module name must match file path**: The `module` declaration in `code` must match the
  file name from `create_session` (e.g., file `Spec.Poly1305.fst` → `module Spec.Poly1305`).
- **Pulse files**: No special configuration beyond including pulse dirs. The `#lang-pulse`
  directive in the file is handled automatically.
- **Lax mode**: Use `"lax": true` for fast syntax/type checking without SMT verification.
- **Position-based verification**: Use `"kind": "verify-to-position"` with `to_line` to verify
  only up to a specific point — useful for large files where you're working on one function.
- **Symbol lookup**: Works after a successful typecheck. Useful for finding types and
  definition locations of functions you need to call.
- **Session replacement**: Creating a new session with the same `file_path` replaces the old one.

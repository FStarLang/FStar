# Verified protocol libraries for Pulse

This directory has a set of generic, verified building blocks for specifying
and implementing network protocols in F\* and Pulse. They started in
[miTLS-F\*](https://github.com/project-everest/mitls-fstar), which builds a
verified TLS 1.3 stack on them, along with several smaller protocols (FTP,
HTTP/1.1, TFTP, YMODEM, and a calculator). They were moved here so that other
projects can reuse them.

Runnable examples that use every module are in
[`share/pulse/examples/protocol`](../../../../share/pulse/examples/protocol).
The C runtime for the extern modules (`Pulse.Lib.TCP`, `Pulse.Lib.Memmove`)
is in [`share/pulse/runtime`](../../../../share/pulse/runtime).

## Layers

### Byte streams
| Module | Description |
|---|---|
| `Pulse.Lib.TCP.History` | Pure model of a bidirectional byte stream: `bytes`, `history` (received/sent), and the prefix/extension relations. Specification only. |
| `Pulse.Lib.TCP` | **Extern** channel API (`connect_tcp`, `listen_tcp`, `accept_tcp`, `read`, `read_full`, `write`, `close`). `is_channel ch received sent` tracks the full stream history. Includes `Pulse.Lib.TCP.History`. |
| `Pulse.Lib.Memmove` | **Extern** in-place (possibly overlapping) byte move within one array. |
| `Pulse.Lib.BufferedTCP.Internal` | Buffer-compaction and append-read primitives over a single receive buffer. |
| `Pulse.Lib.BufferedTCP` | A receive buffer over a `Pulse.Lib.TCP` channel. Leftover bytes are carried across reads, and the received history is the consumed prefix plus the pending suffix. |
| `Pulse.Lib.BufferedStream` | Framing loops over `BufferedTCP`. Layer 1 drives a *pure* message classifier (need-more / complete / malformed). Layer 2 drives an *effectful, relational* endpoint (`buffered_stream_endpoint`) for protocols, such as TLS, that cannot classify input purely. |

### Protocol specifications (pure)
| Module | Description |
|---|---|
| `Pulse.Lib.Protocol.StateMachine` | `state_machine` class: a relational step over wire and local events producing wire and local outputs, with traces and reachability. |
| `Pulse.Lib.Protocol.WireFormat` | `wire_format` class (ghost serializer/parser with round-trip law) and optional stream/prefix laws. |
| `Pulse.Lib.Protocol.WireFormatStateMachine` | `wire_format_state_machine`: a state machine paired with a wire format, and the byte-level trace semantics, in both stream and datagram flavours. |
| `Pulse.Lib.Protocol.FileTransfer` | Generic block-oriented file-transfer specification (sender/receiver, sequence numbers, windows, ACK/NAK). It is parametric in block size, window, classifier and projection, and instantiated by TFTP and YMODEM. |
| `Pulse.Lib.Protocol.Temporal` | Path-based LTL/CTL operators over an abstract step relation, plus a soundness bridge from inductive invariants to `A G` properties. |
| `Pulse.Lib.Protocol.SystemProduct` | Generic two-party product over a single-slot directed channel. |
| `Pulse.Lib.Protocol.MachineProduct` | Builds that product directly from the two endpoints' `state_machine`s. |

### Protocol implementations (Pulse)
| Module | Description |
|---|---|
| `Pulse.Lib.Protocol.Implementation` | `protocol_implementation` class. Pulse network and local handlers are proved to refine a `wire_format_state_machine` over concrete input/output buffers. |
| `Pulse.Lib.Protocol.Endpoint` | Driver-facing endpoint contract: persistent and per-action frames, I/O buffers, and finish hooks. |
| `Pulse.Lib.Protocol.Driver` | Generic fuel-bounded driver that runs an `Endpoint` over a `Pulse.Lib.TCP` channel. |
| `Pulse.Lib.Protocol.ChannelImplementation` | Application-level message channels whose application log (sent/received messages) is linked to the underlying byte-stream history. |

## Extraction
Most modules are specifications or generic code meant to be specialised and
extracted together with their clients. When extracting a client to C with
KaRaMeL:

* treat the externs as libraries:
  `-library Pulse.Lib.TCP,Pulse.Lib.Memmove -add-include '"Pulse_Lib_TCP_runtime.h"'`;
* compile and link `Pulse_Lib_TCP_runtime.c`, `pulse_tcp_sockets.c` and
  `Pulse_Lib_Memmove_runtime.c` from `share/pulse/runtime`;
* if your `--extract` setting excludes `Pulse`, add these modules back
  explicitly, for example
  `+Pulse.Lib.BufferedTCP,+Pulse.Lib.BufferedTCP.Internal,+Pulse.Lib.BufferedStream,+Pulse.Lib.Protocol`.

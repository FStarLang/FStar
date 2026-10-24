# echo -- verified length-prefixed echo server

A small example for the buffered-stream parts of the Pulse protocol libraries
(`pulse/lib/pulse/lib/protocol/`), the parts that `calc` and `tftp` do not use.

## Protocol

A frame is a 2-byte big-endian length `L` with `1 <= L <= 256`, followed by
`L` payload bytes. The server reads frames from a buffered TCP channel and
writes each one back unchanged (header and payload). It stops when either:

* the peer closes the stream (a 0-byte read) while waiting for more bytes, or
* a header has `L = 0` or `L > 256` (malformed).

When it stops, it closes the channel and returns an `echo_report` holding the
number of frames echoed and a status (`EchoClosed`, `EchoMalformed`,
`EchoBufferFull`, `EchoOutOfFuel`).

## What is proved

Both servers keep `Echo.Spec.echo_inv committed sent` true at every step:

* the server's sent byte history equals the prefix of its received history
  that it has consumed, and
* that prefix is a concatenation of well-formed frames (`is_frames`).

So the server only ever echoes complete, valid frames, exactly as received, in
order. In addition:

* The direct server's postcondition gives the reason it stopped:
  * on `EchoClosed`, the pending (unconsumed) bytes are an incomplete frame
    (`needs_more`);
  * on `EchoMalformed`, the classifier rejects them.
* Both servers do a read only when the pending bytes cannot form a frame
  (Layer-1 "process before read").

The receive buffer holds 300 bytes and a maximal frame is 258 bytes, so a
complete frame always fits. For the direct server this is proved:
`lemma_can_read` shows a read is always possible on `NeedMore`, and its
postcondition rules out `EchoBufferFull` and `EchoOutOfFuel`. The Layer-2
driver checks for a full buffer itself, so the endpoint server still handles
`DriveBufferFull`. That branch is unreachable for the same reason, but this is
not stated in its postcondition.

## Files and the library modules they exercise

| File | Contents | Library modules / functions exercised |
|------|----------|----------------------------------------|
| `spec/Echo.Spec.fst` | Pure frame classifier `classify` (NeedMore / `Yield n l` / `Reject Malformed`); the `stream_processor` instance `echo_sp` and proofs of its two laws (consumption bound, prefix stability); `is_frames`; `echo_inv` | `Pulse.Lib.BufferedStream.Classifier`: `stream_processor`, `classification`, `sp_consumption`, `sp_prefix_stable`, `needs_more` |
| `impl/Echo.Step.fst` | `classify_pending` (concrete classifier over the borrowed bytes, proved equal to `classify`); `echo_step`, which processes the pending bytes once | `Pulse.Lib.BufferedTCP`: `recall_model`, `borrow_pending`, `view_data`, `view_length`, `release_pending`, `write`, `commit_prefix` (compacts through `Pulse.Lib.Memmove`); `Classifier.step_commit`; `Pulse.Lib.Array.memcpy_l` |
| `impl/Echo.Report.fst` | `echo_status`, `echo_report` (the C-visible result) | -- |
| `impl/Echo.Server.Direct.fst` | Layer 1: a hand-written serve loop that classifies, echoes, and calls `read_more` only on `NeedMore` | `BufferedTCP`: `read_more`, `can_read`, `received_split`, `buffer_wf`; `Classifier`: `stream_invariant`, `lemma_step_commit_preserves`, `lemma_step_commit_extends` |
| `impl/Echo.Server.Endpoint.fst` | Layer 2: the server as a `buffered_stream_endpoint` (`owns`, `process`, `read`, `terminal`, `buffer_full`, `read_auth`, ...), driven by `drive_until_conclusive` | `Pulse.Lib.BufferedStream`: `buffered_stream_endpoint`, `process_post`, `process_outcome`/`Processed`, `process_transition`, `read_delivers`, `drive_until_conclusive`, `drive_post`, `DriveYield`/`DriveReject`/... |
| `impl/Echo.Server.fst` | C entry points `echo_session_direct(ch)` and `echo_session_endpoint(ch, fuel)` | `BufferedTCP`: `wrap_empty` (wraps a `Pulse.Lib.TCP.channel`), `close` |
| `test_main.c` | Self-checking socketpair test (see below) | `Pulse_Lib_TCP_channel_of_fd` and the TCP runtime |

`Pulse.Lib.BufferedTCP.Internal` and `Pulse.Lib.TCP.History` are pulled in
through `BufferedTCP`.

### Not covered: `Pulse.Lib.Protocol.ChannelImplementation`

This example does not give the echo server a message-channel view (an
application log of frames linked to the byte history). That would require a
complete `Pulse.Lib.Protocol.Implementation.protocol_implementation` instance
for echo: about 20 fields, including the Pulse handlers and a
`WireFormatStateMachine` with a `valid_byte_trace`. `calc` already shows how
to build such an instance. Here the frame-level view is the `is_frames`
invariant on the consumed byte history.

## The C test

`test_main.c` runs every scenario against both servers. For each run it
creates `socketpair(AF_UNIX, SOCK_STREAM, 0, sv)`, so no ports are bound. A
pthread runs the verified server on one end, and `main` acts as the client on
the other end:

* **normal** (69 frames):
  * a single frame;
  * a frame split inside its header and inside its payload, with pauses, so
    the server appends reads;
  * several frames plus half a frame in one write;
  * more than 300 bytes in one write, including two maximal 258-byte frames,
    so the receive buffer fills and is compacted;
  * a burst of 60 frames of varied sizes;
  * then `shutdown(SHUT_WR)`.

  The test checks every echo byte for byte, then checks for EOF, `frames == 69`
  and status `EchoClosed`.
* **malformed (L=0)** and **malformed (L=257)**: two good frames, then a bad
  header. Exactly the two frames are echoed, the server hangs up, and the
  status is `EchoMalformed`.
* **EOF mid-frame**: one frame, then part of a second frame, then EOF. The
  test expects one echoed frame and status `EchoClosed`.

On success it prints `echo socket test passed` and exits 0; otherwise it exits
nonzero.

## Building

From the FStar root, once F* and the Pulse library are built:

```
make -k -j12 -C pulse/share/pulse/examples/protocol/echo
```

This verifies the modules (`Makefile`), then runs `c.Makefile` to:

1. extract to C with KaRaMeL, producing `_output/Echo_Verified.{c,h}`, whose
   only public functions are the two `echo_session_*` entry points;
2. compile it with the TCP and Memmove runtimes from
   `share/pulse/runtime`;
3. run the test.

## Notes on the library API

* Layer 2's `bse_read` returns `unit`, so it cannot report end-of-stream.
  The endpoint records a 0-byte `read_more` in a flag. The next `process`
  turns a `NeedMore` into `Reject PeerClosed`.
* `drive_until_conclusive` returns after the first conclusive decision, and
  its `drive_post` makes the histories existential. So the serve loop calls it
  repeatedly, and the echo invariants are carried inside `bse_owns`.
* `BufferedTCP.write` needs `is_buffered`, which is not available while the
  pending bytes are borrowed. `echo_step` therefore copies the frame into a
  separate output buffer (`memcpy_l`), releases the view, and then writes.
* The serve loops are unbounded `while` loops, so they (and their callers) are
  `divergent fn`s.

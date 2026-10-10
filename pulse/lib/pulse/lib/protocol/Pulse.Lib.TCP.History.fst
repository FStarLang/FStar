module Pulse.Lib.TCP.History

(* Pure model of a bidirectional byte stream (e.g. a TCP connection): the
   bytes received so far and the bytes sent so far, with prefix/extension
   relations. Shared by the extern channel API in Pulse.Lib.TCP and by the
   pure protocol specifications in Pulse.Lib.Protocol.*, which can depend on
   this module alone. Everything here is specification-only. *)

module Seq = FStar.Seq
module U8 = FStar.UInt8

unfold type bytes = Seq.seq U8.t

noextract
noeq
type history = {
  tcp_received: bytes;
  tcp_sent: bytes;
}

noextract let empty_history : history =
  {
    tcp_received = Seq.empty;
    tcp_sent = Seq.empty;
  }

noextract let append_received (h:history) (chunk:bytes) : history =
  { h with tcp_received = Seq.append h.tcp_received chunk }

noextract let append_sent (h:history) (chunk:bytes) : history =
  { h with tcp_sent = Seq.append h.tcp_sent chunk }

noextract let history_equal (h0 h1:history) : prop =
  Seq.equal h0.tcp_received h1.tcp_received /\
  Seq.equal h0.tcp_sent h1.tcp_sent

noextract let bytes_extends (old:bytes) (next:bytes) : prop =
  Seq.length old <= Seq.length next /\
  Seq.equal old (Seq.slice next 0 (Seq.length old))

noextract let history_extends (old next:history) : prop =
  bytes_extends old.tcp_received next.tcp_received /\
  bytes_extends old.tcp_sent next.tcp_sent

noextract let bytes_exact_prefix (prefix full:bytes) : prop =
  Seq.length prefix <= Seq.length full /\
  Seq.equal prefix (Seq.slice full 0 (Seq.length prefix))

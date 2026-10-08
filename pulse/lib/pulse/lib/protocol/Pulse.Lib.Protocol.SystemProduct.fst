module Pulse.Lib.Protocol.SystemProduct

(**
  A GENERIC two-party product over a single-slot directed channel.

  Both `Calc.System.sys_step` and `TLS13.System.tls_sys_step` are instances of
  this one construction: two communicating parties (a "client" and a "server")
  share a channel that holds at most one message in flight, directed either
  toward the server or toward the client.  The product interleaves the parties'
  moves subject to the single-slot channel discipline:

    - an OUTPUT move (a party sends) is enabled only when the channel is QUIET,
      and leaves the channel holding a message directed at the peer;
    - a DELIVER move (a party receives) is enabled only when the channel holds a
      message directed at that party, and returns the channel to QUIET;
    - an INTERNAL move (a party steps with no channel interaction) is enabled
      only when the channel is QUIET and leaves it QUIET;
    - a fused SERVE move (the server receives-and-immediately-responds) is
      enabled when the channel holds a message directed at the server, and
      leaves it holding the server's response directed at the client.

  The construction is parameterised over the CONCRETE system-state type `sys`
  through a `prod_iface`: the channel is observed via three predicates
  (`is_quiet` / `in_to_server` / `in_to_client`) and each move FAMILY is a
  relation on `sys` that performs the party-and-channel update.  A concrete
  system need not use every family; unused ones are instantiated with the empty
  relation `no_move`.  `product_step` ORs the seven families under the channel
  discipline above, yielding a `binrel sys` ready for `Pulse.Lib.Protocol.Temporal`.
**)

(** A move family that is never enabled (for transition kinds a system omits). **)
let no_move (#sys:Type) : sys -> sys -> prop = fun _ _ -> False

(** The interface a concrete two-party product exposes to the combinator. **)
noeq
type prod_iface (sys:Type) = {
  // ── channel observations ────────────────────────────────────────────────
  is_quiet     : sys -> prop;   // nothing in flight
  in_to_server : sys -> prop;   // a message is in flight toward the server
  in_to_client : sys -> prop;   // a message is in flight toward the client
  // ── move families (party + channel update; channel gating added below) ──
  client_send       : sys -> sys -> prop;  // client OUTPUT  (quiet -> to-server)
  server_send       : sys -> sys -> prop;  // server OUTPUT  (quiet -> to-client)
  deliver_to_client : sys -> sys -> prop;  // client DELIVER (to-client -> quiet)
  deliver_to_server : sys -> sys -> prop;  // server DELIVER (to-server -> quiet)
  client_local      : sys -> sys -> prop;  // client INTERNAL (quiet -> quiet)
  server_local      : sys -> sys -> prop;  // server INTERNAL (quiet -> quiet)
  server_serve      : sys -> sys -> prop;  // server SERVE fused (to-server -> to-client)
}

(** The generic product step: the seven move families under the single-slot
    directed-channel discipline. **)
let product_step (#sys:Type) (i:prod_iface sys) (a b:sys) : prop =
  (i.is_quiet a     /\ i.client_send a b)       \/
  (i.is_quiet a     /\ i.server_send a b)       \/
  (i.in_to_client a /\ i.deliver_to_client a b) \/
  (i.in_to_server a /\ i.deliver_to_server a b) \/
  (i.is_quiet a     /\ i.client_local a b)      \/
  (i.is_quiet a     /\ i.server_local a b)      \/
  (i.in_to_server a /\ i.server_serve a b)

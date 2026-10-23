module Pulse.Lib.Protocol.MachineProduct

(**
  A GENERIC two-party product built DIRECTLY from the two endpoints' state
  machines.

  `Pulse.Lib.Protocol.SystemProduct` already supplies the single-slot directed-channel
  DISCIPLINE (`product_step`), but it is agnostic about where the move families
  come from: each concrete system hands it seven hand-written relations, and each
  system also declares its own system-state record and its own channel type.
  That leaves message delivery specified twice — once in the endpoint state
  machines and again, independently, in the product.

  This module closes that gap.  Everything is defined here:

    - the CHANNEL type `chan` (single slot, directed);
    - the SYSTEM STATE type `sys` (client endpoint + server endpoint + channel);
    - the seven move families, DERIVED from the two endpoints'
      `Pulse.Lib.Protocol.StateMachine.state_machine`s.

  A concrete protocol supplies only a `machine_iface`: the two state machines,
  a tiny channel interface saying how an emission becomes an in-flight payload
  (`emit_c` / `emit_s`) and what wire message a payload carries (`carries`), and
  a declaration of which move kinds the protocol actually uses.  Sends,
  deliveries and internal moves are then *consequences* of `sm_step`, not
  separate definitions.

  The result is fed back through `Pulse.Lib.Protocol.SystemProduct.product_step`, so the
  channel discipline, and every proof that unfolds it, is unchanged.
**)

module SM = Pulse.Lib.Protocol.StateMachine
module SP = Pulse.Lib.Protocol.SystemProduct

(** ─────────────────────────────────────────────────────────────────────────
    The channel and the system state
    ───────────────────────────────────────────────────────────────────────── **)

(**
  The single-slot directed channel.  At most one message is in flight, and it is
  directed at exactly one of the two parties.  `payload` is whatever the protocol
  needs to keep about a message in transit: for a semantic channel that is just
  the message, for a wire-level channel it is the raw bytes (plus any sender-side
  ghost material the invariant wants to remember).
**)
noeq
type chan (payload:Type0) =
  | Quiet    : chan payload
  | ToServer : payload -> chan payload
  | ToClient : payload -> chan payload

(** The combined system state: the two endpoints and the channel between them. **)
noeq
type sys (cst:Type0) (sst:Type0) (payload:Type0) = {
  client:  cst;
  server:  sst;
  channel: chan payload;
}

(** ─────────────────────────────────────────────────────────────────────────
    The interface a protocol supplies
    ───────────────────────────────────────────────────────────────────────── **)

(**
  Which move kinds a protocol uses.  A protocol that never performs a given kind
  of move sets the corresponding flag to `False`, which makes that family empty
  (the role `Pulse.Lib.Protocol.SystemProduct.no_move` plays today).  Making this explicit
  keeps each instance's step relation exactly as large as it was, rather than
  silently admitting moves the protocol cannot actually perform.
**)
noeq
type move_kinds = {
  uses_client_send       : prop;
  uses_server_send       : prop;
  uses_deliver_to_client : prop;
  uses_deliver_to_server : prop;
  uses_client_local      : prop;
  uses_server_local      : prop;
  uses_server_serve      : prop;
}

(** A strict request/response protocol: the client sends, the server serves
    (receive-and-respond fused), the client receives.  Nothing else. **)
let request_response_moves : move_kinds = {
  uses_client_send       = True;
  uses_server_send       = False;
  uses_deliver_to_client = True;
  uses_deliver_to_server = False;
  uses_client_local      = False;
  uses_server_local      = False;
  uses_server_serve      = True;
}

(** A full-duplex protocol: either party may send, deliver, or step internally,
    but there is no fused receive-and-respond. **)
let full_duplex_moves : move_kinds = {
  uses_client_send       = True;
  uses_server_send       = True;
  uses_deliver_to_client = True;
  uses_deliver_to_server = True;
  uses_client_local      = True;
  uses_server_local      = True;
  uses_server_serve      = False;
}

(**
  The protocol-specific data the product needs.

  `cstep` and `sstep` are the two endpoints' STEP RELATIONS — typically the
  `sm_step` of an `SM.state_machine`, but the interface deliberately does NOT
  embed the state machines themselves.  Nothing in the product construction reads
  an endpoint's initial state: the product relates a pre-state to a post-state,
  and where a run starts is the caller's business.  Demanding a
  `state_machine` here would force an instance whose initial state is
  parameterised (by a configuration, say) to invent an arbitrary anchor just to
  fill a field no family reads.  Initial states are therefore supplied where they
  are actually needed: to `initial_sys`, and to the validity lemmas below.

  `emit_c a a' out p` relates a client step (pre-state, post-state, its output)
  to the payload `p` that consequently goes in flight.  It is RELATIONAL rather
  than a function so that a payload may record sender-side material that is not a
  function of the output alone — a wire-level channel, for instance, can carry a
  snapshot of the sender's model and the logical message that was sent, and can
  additionally constrain how the sender's own log grew.  `emit_s` is the mirror.

  `carries p w` says the in-flight payload `p` delivers the wire message `w` to
  its recipient.  For a semantic channel this is equality; for a wire-level
  channel it is "`w` serializes to the raw bytes of `p`", which is what makes a
  delivery feed the receiver real bytes that it parses itself.
**)
noeq
type machine_iface
  (cst:Type0) (sst:Type0) (payload:Type0)
  (wire:Type0) (cloc:Type0) (sloc:Type0) (lout:Type0)
  = {
  cstep   : cst -> SM.event wire cloc -> cst -> SM.step_output wire lout -> GTot prop;
  sstep   : sst -> SM.event wire sloc -> sst -> SM.step_output wire lout -> GTot prop;
  emit_c  : cst -> cst -> SM.step_output wire lout -> payload -> prop;
  emit_s  : sst -> sst -> SM.step_output wire lout -> payload -> prop;
  carries : payload -> wire -> prop;
  moves   : move_kinds;
}

(** ─────────────────────────────────────────────────────────────────────────
    The seven move families, derived from the endpoint state machines

    Every family below is a single `sm_step` of ONE endpoint, plus the channel
    bookkeeping.  The channel GATING (quiet / directed) is NOT imposed here: it
    is supplied once and for all by `SP.product_step`.
    ───────────────────────────────────────────────────────────────────────── **)

(** Client OUTPUT: a local event that emits on the wire.  The emitted payload
    goes in flight toward the server. **)
(** The witnessed part of [mp_client_send], as a named predicate.

    [eliminate exists] desugars to [FStar.Classical.Sugar.indefinite_descriptionN],
    whose precondition is a beta-redex under the quantifier prefix.  Keeping the
    matrix folded behind a definition (rather than inlining it at each
    elimination site) is what makes that obligation discharge. **)
let mp_client_send_body
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  (local:cloc) (c':cst) (out:SM.step_output wire lout) (p:payload)
  : prop =
  i.cstep a.client (SM.LocalEvent local) c' out /\
  Cons? out.SM.so_wire_outputs /\
  i.emit_c a.client c' out p /\
  b == { a with client = c'; channel = ToServer p }

let mp_client_send
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  : prop =
  i.moves.uses_client_send /\
  (exists (local:cloc) (c':cst) (out:SM.step_output wire lout) (p:payload).
     mp_client_send_body i a b local c' out p)

(** Server OUTPUT: the mirror of `mp_client_send`. **)
let mp_server_send
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  : prop =
  i.moves.uses_server_send /\
  (exists (local:sloc) (s':sst) (out:SM.step_output wire lout) (p:payload).
     i.sstep a.server (SM.LocalEvent local) s' out /\
     Cons? out.SM.so_wire_outputs /\
     i.emit_s a.server s' out p /\
     b == { a with server = s'; channel = ToClient p })

(** Client DELIVER: the in-flight payload carries a wire message, and the client
    takes a wire step on it.  The channel returns to quiet. **)
let mp_deliver_to_client
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  : prop =
  i.moves.uses_deliver_to_client /\
  (exists (p:payload) (w:wire) (c':cst) (out:SM.step_output wire lout).
     a.channel == ToClient p /\
     i.carries p w /\
     i.cstep a.client (SM.WireEvent w) c' out /\
     b == { a with client = c'; channel = Quiet })

(** Server DELIVER: the mirror of `mp_deliver_to_client`. **)
let mp_deliver_to_server
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  : prop =
  i.moves.uses_deliver_to_server /\
  (exists (p:payload) (w:wire) (s':sst) (out:SM.step_output wire lout).
     a.channel == ToServer p /\
     i.carries p w /\
     i.sstep a.server (SM.WireEvent w) s' out /\
     b == { a with server = s'; channel = Quiet })

(** Client INTERNAL: a local event that emits nothing on the wire. **)
let mp_client_local
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  : prop =
  i.moves.uses_client_local /\
  (exists (local:cloc) (c':cst) (out:SM.step_output wire lout).
     i.cstep a.client (SM.LocalEvent local) c' out /\
     out.SM.so_wire_outputs == [] /\
     b == { a with client = c' })

(** Server INTERNAL: the mirror of `mp_client_local`. **)
let mp_server_local
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  : prop =
  i.moves.uses_server_local /\
  (exists (local:sloc) (s':sst) (out:SM.step_output wire lout).
     i.sstep a.server (SM.LocalEvent local) s' out /\
     out.SM.so_wire_outputs == [] /\
     b == { a with server = s' })

(** Server SERVE (fused): ONE server wire step consumes the in-flight request and
    emits the response, which goes straight back out toward the client.  This is
    a single `sm_step`, so the "receive" and the "respond" cannot drift apart. **)
let mp_server_serve
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  : prop =
  i.moves.uses_server_serve /\
  (exists (p:payload) (w:wire) (s':sst) (out:SM.step_output wire lout) (p':payload).
     a.channel == ToServer p /\
     i.carries p w /\
     i.sstep a.server (SM.WireEvent w) s' out /\
     Cons? out.SM.so_wire_outputs /\
     i.emit_s a.server s' out p' /\
     b == { a with server = s'; channel = ToClient p' })

(** ─────────────────────────────────────────────────────────────────────────
    Feeding the derived families back through the channel discipline
    ───────────────────────────────────────────────────────────────────────── **)

(** The derived families, packaged for `Pulse.Lib.Protocol.SystemProduct`.  The channel
    observations read off `chan` uniformly — no protocol input needed. **)
let prod_iface_of
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  : SP.prod_iface (sys cst sst payload) = {
  is_quiet     = (fun s -> Quiet? s.channel);
  in_to_server = (fun s -> ToServer? s.channel);
  in_to_client = (fun s -> ToClient? s.channel);
  client_send       = mp_client_send i;
  server_send       = mp_server_send i;
  deliver_to_client = mp_deliver_to_client i;
  deliver_to_server = mp_deliver_to_server i;
  client_local      = mp_client_local i;
  server_local      = mp_server_local i;
  server_serve      = mp_server_serve i;
}

(** A single system transition: the derived families under the single-slot
    directed-channel discipline. **)
let machine_step
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  : prop =
  SP.product_step (prod_iface_of i) a b

(** The initial system: the two given endpoint states, nothing in flight.  The
    initial states are arguments rather than interface fields precisely because
    an instance may derive them from run-time configuration. **)
let initial_sys
  (#cst #sst #payload:Type0)
  (c0:cst) (s0:sst)
  : sys cst sst payload = {
  client  = c0;
  server  = s0;
  channel = Quiet;
}

(** The system is quiescent exactly when nothing is in flight. **)
let quiescent
  (#cst #sst #payload:Type0)
  (s:sys cst sst payload)
  : prop =
  Quiet? s.channel

(** ─────────────────────────────────────────────────────────────────────────
    Structural consequences of the construction

    These hold for EVERY instance, so no concrete system has to re-prove them.
    ───────────────────────────────────────────────────────────────────────── **)

(** A step out of a quiescent state is a send or an internal move; a step out of
    a directed state is the matching delivery (or a fused serve).  This is just
    `product_step` read through the uniform channel observations, but stating it
    once here is what lets an instance's inductiveness proof case-split on the
    channel alone. **)
let lemma_step_channel_cases
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  : Lemma
      (requires machine_step i a b)
      (ensures
        (Quiet? a.channel ==>
          (mp_client_send i a b \/ mp_server_send i a b \/
           mp_client_local i a b \/ mp_server_local i a b)) /\
        (ToServer? a.channel ==>
          (mp_deliver_to_server i a b \/ mp_server_serve i a b)) /\
        (ToClient? a.channel ==> mp_deliver_to_client i a b))
  = ()

(** Every move advances exactly one endpoint: the client families leave the
    server component untouched, and vice versa. **)
let lemma_client_moves_fix_server
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  : Lemma
      (requires
        mp_client_send i a b \/ mp_deliver_to_client i a b \/ mp_client_local i a b)
      (ensures b.server == a.server)
  = ()

let lemma_server_moves_fix_client
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  : Lemma
      (requires
        mp_server_send i a b \/ mp_deliver_to_server i a b \/
        mp_server_local i a b \/ mp_server_serve i a b)
      (ensures b.client == a.client)
  = ()

(** Each endpoint only ever moves by its OWN state machine.  This is the formal
    content of "delivery is not defined separately": whatever the product does to
    the client component, it is a single `cstep`. **)
let lemma_client_component_steps
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  : Lemma
      (requires
        mp_client_send i a b \/ mp_deliver_to_client i a b \/ mp_client_local i a b)
      (ensures
        (exists (ev:SM.event wire cloc) (out:SM.step_output wire lout).
           i.cstep a.client ev b.client out))
  = let goal =
      (exists (ev:SM.event wire cloc) (out:SM.step_output wire lout).
         i.cstep a.client ev b.client out) in
    eliminate
      (mp_client_send i a b) \/ (mp_deliver_to_client i a b \/ mp_client_local i a b)
    with begin
      eliminate exists (local:cloc) (c':cst) (out:SM.step_output wire lout) (p:payload).
        i.cstep a.client (SM.LocalEvent local) c' out /\
        Cons? out.SM.so_wire_outputs /\
        i.emit_c a.client c' out p /\
        b == ({ a with client = c'; channel = ToServer p } <: sys cst sst payload)
      with
        assert (i.cstep a.client (SM.LocalEvent local) b.client out)
    end
    and begin
      eliminate (mp_deliver_to_client i a b) \/ (mp_client_local i a b)
      with begin
        eliminate exists (p:payload) (w:wire) (c':cst) (out:SM.step_output wire lout).
          a.channel == ToClient p /\
          i.carries p w /\
          i.cstep a.client (SM.WireEvent w) c' out /\
          b == ({ a with client = c'; channel = Quiet } <: sys cst sst payload)
        with
          assert (i.cstep a.client (SM.WireEvent w) b.client out)
      end
      and begin
        eliminate exists (local:cloc) (c':cst) (out:SM.step_output wire lout).
          i.cstep a.client (SM.LocalEvent local) c' out /\
          out.SM.so_wire_outputs == [] /\
          b == ({ a with client = c' } <: sys cst sst payload)
        with
          assert (i.cstep a.client (SM.LocalEvent local) b.client out)
      end
    end

let lemma_server_component_steps
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  : Lemma
      (requires
        mp_server_send i a b \/ mp_deliver_to_server i a b \/
        mp_server_local i a b \/ mp_server_serve i a b)
      (ensures
        (exists (ev:SM.event wire sloc) (out:SM.step_output wire lout).
           i.sstep a.server ev b.server out))
  = let goal =
      (exists (ev:SM.event wire sloc) (out:SM.step_output wire lout).
         i.sstep a.server ev b.server out) in
    eliminate
      (mp_server_send i a b) \/
      (mp_deliver_to_server i a b \/ mp_server_local i a b \/ mp_server_serve i a b)
    with begin
      eliminate exists (local:sloc) (s':sst) (out:SM.step_output wire lout) (p:payload).
        i.sstep a.server (SM.LocalEvent local) s' out /\
        Cons? out.SM.so_wire_outputs /\
        i.emit_s a.server s' out p /\
        b == ({ a with server = s'; channel = ToClient p } <: sys cst sst payload)
      with
        assert (i.sstep a.server (SM.LocalEvent local) b.server out)
    end
    and begin
      eliminate
        (mp_deliver_to_server i a b) \/
        (mp_server_local i a b \/ mp_server_serve i a b)
      with begin
        eliminate exists (p:payload) (w:wire) (s':sst) (out:SM.step_output wire lout).
          a.channel == ToServer p /\
          i.carries p w /\
          i.sstep a.server (SM.WireEvent w) s' out /\
          b == ({ a with server = s'; channel = Quiet } <: sys cst sst payload)
        with
          assert (i.sstep a.server (SM.WireEvent w) b.server out)
      end
      and begin
        eliminate (mp_server_local i a b) \/ (mp_server_serve i a b)
        with begin
          eliminate exists (local:sloc) (s':sst) (out:SM.step_output wire lout).
            i.sstep a.server (SM.LocalEvent local) s' out /\
            out.SM.so_wire_outputs == [] /\
            b == ({ a with server = s' } <: sys cst sst payload)
          with
            assert (i.sstep a.server (SM.LocalEvent local) b.server out)
        end
        and begin
          eliminate exists (p:payload) (w:wire) (s':sst)
                           (out:SM.step_output wire lout) (p':payload).
            a.channel == ToServer p /\
            i.carries p w /\
            i.sstep a.server (SM.WireEvent w) s' out /\
            Cons? out.SM.so_wire_outputs /\
            i.emit_s a.server s' out p' /\
            b == ({ a with server = s'; channel = ToClient p' } <: sys cst sst payload)
          with
            assert (i.sstep a.server (SM.WireEvent w) b.server out)
        end
      end
    end

(** Either the client component is untouched (a server move) or it took a single
    step of its own machine (a client move).  This is the case split every
    instance-level inductiveness proof wants. **)
let lemma_client_moves_or_fixed
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  : Lemma
      (requires machine_step i a b)
      (ensures
        b.client == a.client \/
        (exists (ev:SM.event wire cloc) (out:SM.step_output wire lout).
           i.cstep a.client ev b.client out))
  = let goal =
      (b.client == a.client \/
       (exists (ev:SM.event wire cloc) (out:SM.step_output wire lout).
          i.cstep a.client ev b.client out)) in
    eliminate
      (mp_client_send i a b \/ mp_deliver_to_client i a b \/ mp_client_local i a b) \/
      (mp_server_send i a b \/ mp_deliver_to_server i a b \/
       mp_server_local i a b \/ mp_server_serve i a b)
    with lemma_client_component_steps i a b
    and lemma_server_moves_fix_client i a b

let lemma_server_moves_or_fixed
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  : Lemma
      (requires machine_step i a b)
      (ensures
        b.server == a.server \/
        (exists (ev:SM.event wire sloc) (out:SM.step_output wire lout).
           i.sstep a.server ev b.server out))
  = let goal =
      (b.server == a.server \/
       (exists (ev:SM.event wire sloc) (out:SM.step_output wire lout).
          i.sstep a.server ev b.server out)) in
    eliminate
      (mp_client_send i a b \/ mp_deliver_to_client i a b \/ mp_client_local i a b) \/
      (mp_server_send i a b \/ mp_deliver_to_server i a b \/
       mp_server_local i a b \/ mp_server_serve i a b)
    with lemma_client_moves_fix_server i a b
    and lemma_server_component_steps i a b

(** Consequently each endpoint stays a valid state of its own machine along every
    system run: the product can never drive an endpoint off its state machine.

    "Valid" is relative to where the endpoint's run STARTED, so the anchor is an
    explicit argument.  An instance whose initial state depends on a run-time
    configuration can therefore instantiate these at the real anchor, rather than
    at some arbitrary one baked into the interface. **)
let machine_of
  (#state #wire #loc #lout:Type0)
  (step:state -> SM.event wire loc -> state -> SM.step_output wire lout -> GTot prop)
  (init:state)
  : SM.state_machine state wire loc lout = {
  SM.sm_initial_state = init;
  SM.sm_step          = step;
}

let lemma_client_valid_preserved
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (c0:cst)
  (a b:sys cst sst payload)
  : Lemma
      (requires machine_step i a b /\ SM.valid_state (machine_of i.cstep c0) a.client)
      (ensures SM.valid_state (machine_of i.cstep c0) b.client)
  = let m = machine_of i.cstep c0 in
    lemma_client_moves_or_fixed i a b;
    eliminate
      (b.client == a.client) \/
      (exists (ev:SM.event wire cloc) (out:SM.step_output wire lout).
         i.cstep a.client ev b.client out)
    with ()
    and
      eliminate exists (ev:SM.event wire cloc) (out:SM.step_output wire lout).
        i.cstep a.client ev b.client out
      with SM.lemma_valid_state_after_step m a.client ev b.client out

let lemma_server_valid_preserved
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (s0:sst)
  (a b:sys cst sst payload)
  : Lemma
      (requires machine_step i a b /\ SM.valid_state (machine_of i.sstep s0) a.server)
      (ensures SM.valid_state (machine_of i.sstep s0) b.server)
  = let m = machine_of i.sstep s0 in
    lemma_server_moves_or_fixed i a b;
    eliminate
      (b.server == a.server) \/
      (exists (ev:SM.event wire sloc) (out:SM.step_output wire lout).
         i.sstep a.server ev b.server out)
    with ()
    and
      eliminate exists (ev:SM.event wire sloc) (out:SM.step_output wire lout).
        i.sstep a.server ev b.server out
      with SM.lemma_valid_state_after_step m a.server ev b.server out

(** ─────────────────────────────────────────────────────────────────────────
    Introduction lemmas

    Eliminating a derived family is automatic — unfolding it hands the SMT solver
    an existential it can destruct.  INTRODUCING one is not: `i.cstep`, `i.emit_c`
    and `i.carries` are higher-order record fields, and the solver will not
    synthesise the witnesses in applied form on its own.  Every instance that
    needs to build a family therefore hits the same wall, and works around it with
    the same ad-hoc bridging asserts.

    These seven lemmas do that work once.  The caller supplies the witnesses
    explicitly; because the hypotheses mention the interface's fields in already
    applied form, the concrete instance discharges them by delta-reducing its own
    (literal) interface record, which is a typechecking step rather than a
    solver search.
    ───────────────────────────────────────────────────────────────────────── **)

let lemma_mp_client_send_intro
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  (local:cloc) (c':cst) (out:SM.step_output wire lout) (p:payload)
  : Lemma
      (requires
        i.moves.uses_client_send /\
        i.cstep a.client (SM.LocalEvent local) c' out /\
        Cons? out.SM.so_wire_outputs /\
        i.emit_c a.client c' out p /\
        b == ({ a with client = c'; channel = ToServer p } <: sys cst sst payload))
      (ensures mp_client_send i a b)
  = introduce exists (local0:cloc) (c'0:cst) (out0:SM.step_output wire lout) (p0:payload).
      mp_client_send_body i a b local0 c'0 out0 p0
    with local c' out p
    and ()

let lemma_mp_server_send_intro
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  (local:sloc) (s':sst) (out:SM.step_output wire lout) (p:payload)
  : Lemma
      (requires
        i.moves.uses_server_send /\
        i.sstep a.server (SM.LocalEvent local) s' out /\
        Cons? out.SM.so_wire_outputs /\
        i.emit_s a.server s' out p /\
        b == ({ a with server = s'; channel = ToClient p } <: sys cst sst payload))
      (ensures mp_server_send i a b)
  = ()

let lemma_mp_deliver_to_client_intro
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  (p:payload) (w:wire) (c':cst) (out:SM.step_output wire lout)
  : Lemma
      (requires
        i.moves.uses_deliver_to_client /\
        a.channel == ToClient p /\
        i.carries p w /\
        i.cstep a.client (SM.WireEvent w) c' out /\
        b == ({ a with client = c'; channel = Quiet } <: sys cst sst payload))
      (ensures mp_deliver_to_client i a b)
  = ()

let lemma_mp_deliver_to_server_intro
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  (p:payload) (w:wire) (s':sst) (out:SM.step_output wire lout)
  : Lemma
      (requires
        i.moves.uses_deliver_to_server /\
        a.channel == ToServer p /\
        i.carries p w /\
        i.sstep a.server (SM.WireEvent w) s' out /\
        b == ({ a with server = s'; channel = Quiet } <: sys cst sst payload))
      (ensures mp_deliver_to_server i a b)
  = ()

let lemma_mp_client_local_intro
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  (local:cloc) (c':cst) (out:SM.step_output wire lout)
  : Lemma
      (requires
        i.moves.uses_client_local /\
        i.cstep a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [] /\
        b == ({ a with client = c' } <: sys cst sst payload))
      (ensures mp_client_local i a b)
  = ()

let lemma_mp_server_local_intro
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  (local:sloc) (s':sst) (out:SM.step_output wire lout)
  : Lemma
      (requires
        i.moves.uses_server_local /\
        i.sstep a.server (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [] /\
        b == ({ a with server = s' } <: sys cst sst payload))
      (ensures mp_server_local i a b)
  = ()

let lemma_mp_server_serve_intro
  (#cst #sst #payload #wire #cloc #sloc #lout:Type0)
  (i:machine_iface cst sst payload wire cloc sloc lout)
  (a b:sys cst sst payload)
  (p:payload) (w:wire) (s':sst) (out:SM.step_output wire lout) (p':payload)
  : Lemma
      (requires
        i.moves.uses_server_serve /\
        a.channel == ToServer p /\
        i.carries p w /\
        i.sstep a.server (SM.WireEvent w) s' out /\
        Cons? out.SM.so_wire_outputs /\
        i.emit_s a.server s' out p' /\
        b == ({ a with server = s'; channel = ToClient p' } <: sys cst sst payload))
      (ensures mp_server_serve i a b)
  = ()

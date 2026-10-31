module Pulse.Lib.LogicalAtomicity.Example.Helping
#lang-pulse

(**
Client-continuation helping with exclusive ownership transfer.

Two tasks race to claim a descriptor, but only the winner runs fetch_add and
commits the caller's logical-atomic continuation. The caller waits for phi,
including an exclusive payload, rather than performing the operation itself.
This exercises the helping motivation of TaDA/Iris-style atomic specs and
the transfer of client ghost code associated with HoCAP-style specifications.

An arbitrary AU is NOT sendable: its hidden state may be thread-local.
Instead, the descriptor stores a SendableTrade built from sendable captured
resources. The winning worker eliminates the trade and constructs its AU
locally. A lock and fractional ghost state enforce one claimant and one
collection; this is intentionally a locked protocol, not a lock-free one.

This establishes partial correctness, not fairness, eventual completion, or
general helping for every AU. The descriptor and payload are freed after
joins, but the counter invariant remains. Task.teardown_pool marks logical
completion and currently does not stop native worker threads; run repeated
tests in a bounded process or reuse pools as the queue client does.
*)

open Pulse.Lib.Pervasives
module C = Pulse.Lib.LogicalAtomicity.Example.Counter
module T = Pulse.Lib.LogicalAtomicity.Triple
module S = Pulse.Lib.SendableTrade
module B = Pulse.Lib.Box
module G = Pulse.Lib.GhostReference
module L = Pulse.Lib.SpinLock
module Task = Pulse.Lib.Task
module U32 = FStar.UInt32

(** Descriptor protocol: unclaimed request, winning worker in flight, result
available, then result collected. No transition returns to Pending. *)
type phase = | Pending | Running | Done | Taken

(** Running/Taken split the ghost authority with the worker/caller; Pending
and Done keep full authority inside the lock-protected descriptor. *)
let fraction s = if s = Running || s = Taken then 0.5R else 1.0R
(** Transferable recipe for an AU, not an assertion that arbitrary AUs send.
Its empty input means the winner need not supply additional ownership. *)
let request r inner credits phi = S.trade #emp_inames emp (C.update r inner credits phi)
(** Pending owns the recipe, Done owns phi, and in-flight/collected phases
leave these resources with the worker/caller instead of duplicating them. *)
let content r inner credits phi s v =
  if s = Pending then request r inner credits phi
  else if s = Done then phi v
  else emp
(** Lock invariant connecting runtime fields, phase authority, and the
request/result ownership appropriate to the phase. *)
let body status result ticket r inner credits phi =
  exists* s v.
    B.pts_to status s ** B.pts_to result v **
    G.pts_to ticket #(fraction s) s ** content r inner credits phi s v

(** Sending a descriptor requires sendability of each returned phi, while
Pending uses the existing SendableTrade rule rather than AU sendability. *)
instance send_content r inner credits phi s v
    {| inst:(n:U32.t -> is_send (phi n)) |}
  : is_send (content r inner credits phi s v) =
  if s = Pending then S.is_send_trade #emp_inames emp (C.update r inner credits phi)
  else if s = Done then inst v
  else is_send_placeless emp

(** Lift component sendability to the existential lock invariant. *)
instance send_body status result ticket r inner credits phi
    {| (n:U32.t -> is_send (phi n)) |}
  : is_send (body status result ticket r inner credits phi) =
  FStar.Tactics.Typeclasses.solve

(** Under the lock, transition Pending to Running and hand the winner its
request plus a half-ticket. Losing helpers acquire no operation capability. *)
divergent fn claim (#p:perm)
  (lock:L.lock) (status:B.box phase) (result:B.box U32.t) (ticket:G.ref phase)
  (r:B.box U32.t) inner credits phi
  preserves L.lock_alive lock #p (body status result ticket r inner credits phi)
  returns won:bool
  ensures cond won (request r inner credits phi ** G.pts_to ticket #0.5R Running) emp
{
  L.acquire lock;
  unfold body status result ticket r inner credits phi;
  with s v. _;
  let s = B.(!status);
  if (s = Pending) {
    rewrite content r inner credits phi s v as request r inner credits phi;
    G.write ticket Running;
    G.share ticket;
    B.(status := Running);
    fold content r inner credits phi Running v;
    fold body status result ticket r inner credits phi;
    L.release lock;
    fold cond true (request r inner credits phi ** G.pts_to ticket #0.5R Running) emp;
    true
  } else {
    fold body status result ticket r inner credits phi;
    L.release lock;
    fold cond false (request r inner credits phi ** G.pts_to ticket #0.5R Running) emp;
    false
  }
}

(** The winner's half-ticket identifies Running; reunite authority, store
the result, and transfer phi into Done for the caller to collect. *)
divergent fn complete (#p:perm)
  (lock:L.lock) (status:B.box phase) (result:B.box U32.t) (ticket:G.ref phase)
  (r:B.box U32.t) inner credits phi (old:U32.t)
  preserves L.lock_alive lock #p (body status result ticket r inner credits phi)
  requires G.pts_to ticket #0.5R Running ** phi old
{
  L.acquire lock;
  unfold body status result ticket r inner credits phi;
  with s v. _;
  G.pts_to_injective_eq ticket;
  rewrite each s as Running;
  unfold content r inner credits phi Running v;
  G.gather ticket;
  G.write ticket Done;
  B.(status := Done);
  B.(result := old);
  fold content r inner credits phi Done old;
  fold body status result ticket r inner credits phi;
  L.release lock;
}

(** Claim, locally construct the AU, execute fetch_add, then publish phi.
The caller's continuation runs on this helper, not on the waiting caller. *)
divergent fn help (#p:perm)
  (lock:L.lock) (status:B.box phase) (result:B.box U32.t) (ticket:G.ref phase)
  (r:B.box U32.t) inner credits phi
  preserves L.lock_alive lock #p (body status result ticket r inner credits phi)
{
  let won = claim lock status result ticket r inner credits phi;
  if won {
    elim_cond_true _ _ _;
    unfold request r inner credits phi;
    S.elim_trade #emp_inames emp (C.update r inner credits phi);
    let old = C.fetch_add r inner credits phi;
    complete lock status result ticket r inner credits phi old;
  } else {
    elim_cond_false _ _ _;
  }
}

(** Poll until Done, take phi once, and retain a Taken half-ticket for later
descriptor reclamation. The recursive wait has no fairness guarantee. *)
divergent fn rec await (#p:perm)
  (lock:L.lock) (status:B.box phase) (result:B.box U32.t) (ticket:G.ref phase)
  (r:B.box U32.t) inner credits phi
  preserves L.lock_alive lock #p (body status result ticket r inner credits phi)
  returns old:U32.t
  ensures phi old ** G.pts_to ticket #0.5R Taken
{
  L.acquire lock;
  unfold body status result ticket r inner credits phi;
  with s v. _;
  let s = B.(!status);
  if (s = Done) {
    rewrite content r inner credits phi s v as phi v;
    let old = B.(!result);
    G.write ticket Taken;
    G.share ticket;
    B.(status := Taken);
    fold content r inner credits phi Taken old;
    fold body status result ticket r inner credits phi;
    L.release lock;
    old
  } else {
    fold body status result ticket r inner credits phi;
    L.release lock;
    await lock status result ticket r inner credits phi
  }
}

(** Result ownership includes an exclusive payload and the exact old counter
value, so delivery is stronger than returning a numeric completion flag. *)
let delivered g payload n =
  G.pts_to g #0.5R 1ul ** B.pts_to payload 42ul ** pure (n == 0ul)

(** This concrete phi contains only transferable box/ghost ownership. *)
instance send_delivered g payload n : is_send (delivered g payload n) =
  FStar.Tactics.Typeclasses.solve

(** Full two-helper client: package the request, spawn competitors, recover
phi, join both, and reclaim descriptor and payload. The postcondition proves
old = 0 and ghost value = 1; it does not promise that scheduling terminates. *)
divergent fn two_helpers ()
  returns answer:(B.box U32.t & U32.t)
  ensures exists* i g.
    inv i (T.payload (C.alpha (fst answer)) (C.residual g)) **
    G.pts_to g #0.5R 1ul ** pure (snd answer == 0ul)
{
  let r = B.alloc 0ul;
  let g = G.alloc 0ul;
  G.share g;
  fold C.alpha r 0ul;
  fold C.residual g 0ul;
  fold T.payload (C.alpha r) (C.residual g);
  let i = new_invariant (T.payload (C.alpha r) (C.residual g));
  let payload = B.alloc 42ul;
  let inner = add_inv emp_inames i;
  let phi = delivered g payload;

  // Capture payload ownership along with the caller's ghost half; the
  // winner's commit returns both in delivered rather than dropping payload.
  ghost fn finish (n:U32.t) (_:unit) ()
    requires (G.pts_to g #0.5R 0ul ** B.pts_to payload 42ul) **
      C.residual g n ** C.beta r n ()
    ensures T.payload (C.alpha r) (C.residual g) ** phi n
  {
    unfold C.residual g n;
    G.pts_to_injective_eq g;
    rewrite each n as 0ul;
    G.gather g;
    G.write g 1ul;
    G.share g;
    unfold C.beta r 0ul ();
    assert pure (U32.add_mod 0ul 1ul == 1ul);
    rewrite C.alpha r (U32.add_mod 0ul 1ul) as C.alpha r 1ul;
    fold C.residual g 1ul;
    fold T.payload (C.alpha r) (C.residual g);
    fold delivered g payload 0ul;
    rewrite delivered g payload 0ul as phi n;
  };

  S.intro_trade #emp_inames emp (C.update r inner 1 phi)
    (inv i (T.payload (C.alpha r) (C.residual g)) **
      G.pts_to g #0.5R 0ul ** B.pts_to payload 42ul)
    fn _ {
      slprop_equivs ();
      T.from_invariant emp_inames i (C.alpha r) (C.residual g) (C.beta r) (fun n _ -> phi n)
        (G.pts_to g #0.5R 0ul ** B.pts_to payload 42ul) finish;
      rewrite each add_inv emp_inames i as inner;
      fold C.update r inner 1 phi;
    };
  fold request r inner 1 phi;

  let status = B.alloc Pending;
  let result = B.alloc 0ul;
  let ticket = G.alloc Pending;
  fold content r inner 1 phi Pending 0ul;
  fold body status result ticket r inner 1 phi;
  let lock = L.new_lock (body status result ticket r inner 1 phi);
  L.share lock;
  L.share #_ #0.5R lock;
  rewrite each (0.5R /. 2.0R) as 0.25R;
  rewrite each (1.0R /. 2.0R) as 0.5R;
  let pool = Task.setup_pool 2;
  let transferable =
    L.is_send_lock_alive lock 0.25R (body status result ticket r inner 1 phi)
      #(send_body status result ticket r inner 1 phi
          #(fun n -> send_delivered g payload n));
  let h1 = Task.spawn pool #_
    #(L.lock_alive lock #0.25R (body status result ticket r inner 1 phi))
    #(L.lock_alive lock #0.25R (body status result ticket r inner 1 phi))
    #transferable #transferable
    fn _ { help lock status result ticket r inner 1 phi };
  let h2 = Task.spawn pool #_
    #(L.lock_alive lock #0.25R (body status result ticket r inner 1 phi))
    #(L.lock_alive lock #0.25R (body status result ticket r inner 1 phi))
    #transferable #transferable
    fn _ { help lock status result ticket r inner 1 phi };
  let old = await lock status result ticket r inner 1 phi;
  Task.await h1;
  Task.await h2;
  Task.teardown_pool pool;
  drop_ (Task.pool_done pool);
  L.gather #_ #0.25R #0.25R lock;
  L.gather lock;
  L.acquire lock;
  unfold body status result ticket r inner 1 phi;
  with s v. _;
  G.pts_to_injective_eq ticket;
  rewrite each s as Taken;
  unfold content r inner 1 phi Taken v;
  G.gather ticket;
  G.free ticket;
  B.free status;
  B.free result;
  L.free lock;
  rewrite phi old as delivered g payload old;
  unfold delivered g payload old;
  B.free payload;
  (r, old)
}

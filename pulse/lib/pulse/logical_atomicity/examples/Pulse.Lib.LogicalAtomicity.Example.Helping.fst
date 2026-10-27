module Pulse.Lib.LogicalAtomicity.Example.Helping
#lang-pulse

open Pulse.Lib.Pervasives
module C = Pulse.Lib.LogicalAtomicity.Example.Counter
module T = Pulse.Lib.LogicalAtomicity.Triple
module S = Pulse.Lib.SendableTrade
module B = Pulse.Lib.Box
module G = Pulse.Lib.GhostReference
module L = Pulse.Lib.SpinLock
module Task = Pulse.Lib.Task
module U32 = FStar.UInt32

type phase = | Pending | Running | Done | Taken

let fraction s = if s = Running || s = Taken then 0.5R else 1.0R
let request r inner credits phi = S.trade #emp_inames emp (C.update r inner credits phi)
let content r inner credits phi s v =
  if s = Pending then request r inner credits phi
  else if s = Done then phi v
  else emp
let body status result ticket r inner credits phi =
  exists* s v.
    B.pts_to status s ** B.pts_to result v **
    G.pts_to ticket #(fraction s) s ** content r inner credits phi s v

instance send_content r inner credits phi s v
    {| inst:(n:U32.t -> is_send (phi n)) |}
  : is_send (content r inner credits phi s v) =
  if s = Pending then S.is_send_trade #emp_inames emp (C.update r inner credits phi)
  else if s = Done then inst v
  else is_send_placeless emp

instance send_body status result ticket r inner credits phi
    {| (n:U32.t -> is_send (phi n)) |}
  : is_send (body status result ticket r inner credits phi) =
  FStar.Tactics.Typeclasses.solve

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

let delivered g payload n =
  G.pts_to g #0.5R 1ul ** B.pts_to payload 42ul ** pure (n == 0ul)

instance send_delivered g payload n : is_send (delivered g payload n) =
  FStar.Tactics.Typeclasses.solve

// Two helpers race to claim one descriptor. The caller never executes fetch_add.
// This is a partial-correctness specification, not a fairness/progress claim.
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

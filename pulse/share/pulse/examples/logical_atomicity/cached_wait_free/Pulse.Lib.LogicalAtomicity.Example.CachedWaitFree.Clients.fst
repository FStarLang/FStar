module Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Clients
#lang-pulse

(**
Owned-state clients prove exact values and strong CAS results. Shared clients
construct their AU locally from a separate client invariant; CAS safely
registers it for helping without requiring the captured resources to be sendable.
The native harness additionally forces interleavings at primitive boundaries.
*)

open Pulse.Lib.Pervasives
module G = Pulse.Lib.GhostReference
module H = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Model
module N = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Storage
module Q = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.State
module R = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Read
module C = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.CAS
module D = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Actions
module T = Pulse.Lib.LogicalAtomicity.Triple

fn read_owned (#cells:N.arena) (q:Q.big_atomic cells) (#old:erased H.value)
  preserves Q.shared q ** Q.model q old
  returns v:H.value
  ensures pure (v == old)
{
  D.from_owned (Q.model q) (R.beta q) old;
  fold R.update q emp_inames 0 (fun v -> R.beta q old v);
  let v = R.read q emp_inames 0 (fun v -> R.beta q old v);
  unfold R.beta;
  v
}

fn cas_owned (#cells:N.arena) (q:Q.big_atomic cells)
  (expected:H.value) (node:N.id cells) (#old:erased H.value)
  preserves Q.shared q
  requires Q.model q old ** N.ticket cells node
  returns ok:bool
  ensures Q.model q (if ok then N.value cells node else old) **
    pure (ok == (reveal old = expected)) ** C.unused expected node ok
{
  D.from_owned_at (Q.mask q) (Q.model q) (C.beta q expected (N.value cells node)) old;
  fold C.update q expected (N.value cells node) (Q.mask q) 0
    (fun ok -> C.beta q expected (N.value cells node) old ok);
  let ok = C.cas q expected node (Q.mask q) 0
    (fun ok -> C.beta q expected (N.value cells node) old ok);
  unfold C.beta;
  ok
}

let a : H.value = (11ul, 12ul)
let b : H.value = (21ul, 22ul)
let c : H.value = (31ul, 32ul)

(** A--B--A reuses VALUES, not node identities. Also prove mismatch returns
false and equal expected/desired succeeds without consuming its node. *)
fn sequential ()
  returns v:H.value
  ensures pure (v == a) **
    (exists* (cells:N.arena) (q:Q.big_atomic cells). Q.shared q ** Q.model q a)
{
  let n0 = N.node a;
  let n1 = N.node b;
  let n2 = N.node a;
  let n3 = N.node c;
  let n4 = N.node a;
  let cells:N.arena = [n0; n1; n2; n3; n4];
  rewrite G.pts_to n0.N.token () as N.ticket cells 0;
  rewrite G.pts_to n1.N.token () as N.ticket cells 1;
  rewrite G.pts_to n2.N.token () as N.ticket cells 2;
  rewrite G.pts_to n3.N.token () as N.ticket cells 3;
  rewrite G.pts_to n4.N.token () as N.ticket cells 4;
  let q = Q.create cells 0;
  rewrite Q.model q (N.value cells 0) as Q.model q a;
  let first = read_owned q;
  let changed = cas_owned q a 1;
  assert pure changed;
  rewrite Q.model q (if changed then N.value cells 1 else a) as Q.model q b;
  rewrite C.unused #cells a 1 changed as emp;
  let back = cas_owned q b 2;
  assert pure back;
  rewrite Q.model q (if back then N.value cells 2 else b) as Q.model q a;
  rewrite C.unused #cells b 2 back as emp;
  let mismatch = cas_owned q b 3;
  assert pure (not mismatch);
  rewrite Q.model q (if mismatch then N.value cells 3 else a) as Q.model q a;
  rewrite C.unused #cells b 3 mismatch as N.ticket cells 3;
  let noop = cas_owned q a 4;
  assert pure noop;
  rewrite Q.model q (if noop then N.value cells 4 else a) as Q.model q a;
  rewrite C.unused #cells a 4 noop as N.ticket cells 4;
  unfold N.ticket cells 3;
  unfold N.ticket cells 4;
  G.free (N.at cells 3).N.token;
  G.free (N.at cells 4).N.token;
  read_owned q
}

let residual (_:H.value) = emp
let payload_equiv (#cells:N.arena) (q:Q.big_atomic cells)
  : Lemma (T.payload (Q.model q) residual ==
      (exists* (v:H.value). Q.model q v ** residual v)) =
  assert (T.payload (Q.model q) residual ==
    (exists* (v:H.value). Q.model q v ** residual v))
    by (FStar.Tactics.V2.trefl ())

let shared (#cells:N.arena) (q:Q.big_atomic cells) i =
  Q.shared q ** inv i (T.payload (Q.model q) residual)
instance send_shared (#cells:N.arena) q i : is_send (shared #cells q i) =
  FStar.Tactics.Typeclasses.solve
instance dup_shared (#cells:N.arena) q i : duplicable (shared #cells q i) =
  FStar.Tactics.Typeclasses.solve

ghost fn share_model (#cells:N.arena) (q:Q.big_atomic cells) (#v:erased H.value)
  requires Q.shared q ** Q.model q v
  returns i:iname
  ensures shared q i ** pure (i =!= q.Q.name)
{
  fold residual v;
  fold T.payload (Q.model q) residual;
  let i = fresh_invariant (add_inv emp_inames q.Q.name) (T.payload (Q.model q) residual);
  fold shared q i;
  i
}

fn read_shared (#cells:N.arena) (q:Q.big_atomic cells) (i:iname { i =!= q.Q.name })
  preserves shared q i
  returns v:H.value
{
  unfold shared;
  dup_inv i (T.payload (Q.model q) residual);
  slprop_equivs ();
  ghost fn finish (old v:H.value) ()
    requires emp ** residual old ** R.beta q old v
    ensures T.payload (Q.model q) residual ** emp
  {
    unfold residual;
    unfold R.beta;
    fold residual old;
    fold T.payload (Q.model q) residual;
  };
  payload_equiv q;
  T.from_invariant #H.value #H.value emp_inames i (Q.model q) residual (R.beta q) (fun _ _ -> emp) emp
    (fun old v _ -> finish old v ());
  fold R.update q (add_inv emp_inames i) 1 (fun _ -> emp);
  let v = R.read q (add_inv emp_inames i) 1 (fun _ -> emp);
  fold shared q i;
  v
}

fn cas_shared (#cells:N.arena) (q:Q.big_atomic cells) (i:iname { i =!= q.Q.name })
  (expected:H.value) (node:N.id cells)
  preserves shared q i
  requires N.ticket cells node
  returns ok:bool
  ensures C.unused expected node ok
{
  unfold shared;
  dup_inv i (T.payload (Q.model q) residual);
  slprop_equivs ();
  ghost fn finish (old:H.value) (ok:bool) ()
    requires emp ** residual old ** C.beta q expected (N.value cells node) old ok
    ensures T.payload (Q.model q) residual ** emp
  {
    unfold residual;
    unfold C.beta;
    fold residual (if ok then N.value cells node else old);
    fold T.payload (Q.model q) residual;
  };
  payload_equiv q;
  T.from_invariant #H.value #bool (Q.mask q) i (Q.model q) residual (C.beta q expected (N.value cells node))
    (fun _ _ -> emp) emp (fun old ok _ -> finish old ok ());
  fold C.update q expected (N.value cells node) (add_inv (Q.mask q) i) 1 (fun _ -> emp);
  let ok = C.cas q expected node (add_inv (Q.mask q) i) 1 (fun _ -> emp);
  fold shared q i;
  ok
}

let local_completion caller (marker:G.ref nat) ok =
  loc caller ** G.pts_to marker (if ok then 1 else 2)
let local_extra caller (marker:G.ref nat) = loc caller ** G.pts_to marker 0

(** This AU captures a non-sendable locality assertion and an exclusive
marker. Even when another thread helps, its callback executes at the original
caller's ghost locality and returns that caller's one-shot completion. *)
fn cas_shared_local (#cells:N.arena) (q:Q.big_atomic cells) (i:iname { i =!= q.Q.name })
  (expected:H.value) (node:N.id cells)
  preserves shared q i
  requires N.ticket cells node
  returns ok:bool
  ensures C.unused expected node ok
{
  unfold shared;
  dup_inv i (T.payload (Q.model q) residual);
  let caller = loc_get ();
  let marker = G.alloc #nat 0;
  ghost fn finish (old:H.value) (ok:bool) ()
    requires local_extra caller marker ** residual old **
      C.beta q expected (N.value cells node) old ok
    ensures T.payload (Q.model q) residual ** local_completion caller marker ok
  {
    unfold local_extra;
    let executing = loc_get ();
    loc_gather caller #executing;
    assert pure (executing == caller);
    G.write marker (if ok then 1 else 2);
    unfold residual;
    unfold C.beta;
    fold residual (if ok then N.value cells node else old);
    fold T.payload (Q.model q) residual;
    fold local_completion caller marker ok;
  };
  payload_equiv q;
  slprop_equivs ();
  fold local_extra caller marker;
  T.from_invariant #H.value #bool (Q.mask q) i (Q.model q) residual
    (C.beta q expected (N.value cells node))
    (fun _ ok -> local_completion caller marker ok)
    (local_extra caller marker) (fun old ok _ -> finish old ok ());
  fold C.update q expected (N.value cells node) (add_inv (Q.mask q) i) 1
    (local_completion caller marker);
  let ok = C.cas q expected node (add_inv (Q.mask q) i) 1 (local_completion caller marker);
  unfold local_completion;
  G.free marker;
  drop_ (loc caller);
  fold shared q i;
  ok
}

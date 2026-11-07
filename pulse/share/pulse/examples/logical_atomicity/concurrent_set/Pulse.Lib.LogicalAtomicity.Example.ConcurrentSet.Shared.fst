module Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Shared
#lang-pulse

(**
Unrestricted shared-set clients, independent of the paper's producer protocol.

Any number of callers may add, remove, or query any in-range key, including
repeated removal/reinsertion of the same node. The callback restores the
abstract model but discards its relation to the returned boolean. Thus this
wrapper guarantees safe shared use, while Operations supplies the stronger
logically atomic transition. Native history tests check the concrete results.
*)

open Pulse.Lib.Pervasives
module H = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Model
module Q = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.State
module O = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Operations
module T = Pulse.Lib.LogicalAtomicity.Triple

let residual (q:Q.set) (_:Q.contents q.Q.cells) = emp
noeq type handle = { set:Q.set; name:iname }
let shared (h:handle) =
  Q.is_set h.set ** inv h.name (T.payload (O.alpha h.set) (residual h.set))
let well_named (h:handle) = h.name =!= h.set.Q.name
instance send_shared h : is_send (shared h) = FStar.Tactics.Typeclasses.solve
instance dup_shared h : duplicable (shared h) = FStar.Tactics.Typeclasses.solve

fn create (n:nat)
  returns h:handle
  ensures pure (Q.capacity h.set == n /\ well_named h) ** shared h
{
  let q = Q.create n;
  fold O.alpha q (H.empty n);
  fold residual q (H.empty n);
  fold T.payload (O.alpha q) (residual q);
  let i = fresh_invariant (add_inv emp_inames q.Q.name) (T.payload (O.alpha q) (residual q));
  let h = { set=q; name=i };
  rewrite each q as h.set;
  rewrite each i as h.name;
  fold shared h;
  h
}

(** Instantiate the same AU contract for arbitrary interference. *)
ghost fn prepare (h:handle) (op:H.operation) (k:Q.key h.set)
  preserves shared h
  ensures O.update h.set op k (add_inv emp_inames h.name) 1 (fun _ -> emp)
{
  unfold shared;
  slprop_equivs ();
  dup_inv h.name (T.payload (O.alpha h.set) (residual h.set));
  ghost fn finish (s:Q.contents h.set.Q.cells) (r:bool) ()
    requires emp ** residual h.set s ** O.beta h.set op k s r
    ensures T.payload (O.alpha h.set) (residual h.set) ** emp
  {
    unfold residual;
    unfold O.beta;
    fold O.alpha h.set (H.after op s k);
    fold residual h.set (H.after op s k);
    fold T.payload (O.alpha h.set) (residual h.set);
  };
  T.from_invariant #(Q.contents h.set.Q.cells) #bool emp_inames h.name (O.alpha h.set) (residual h.set)
    (O.beta h.set op k) (fun _ _ -> emp) emp
    // Restore the explicit emp framing removed by the local Pulse callback.
    (fun s r _ -> Pulse.Lib.Core.sub_ghost
      (emp ** residual h.set s ** O.beta h.set op k s r)
      (fun _ -> T.payload (O.alpha h.set) (residual h.set) ** emp)
      (slprop_equiv_ext' _ _ ())
      (intro_slprop_post_equiv _ _ (fun _ -> slprop_equiv_ext' _ _ ()))
      (finish s r ()));
  fold O.update h.set op k (add_inv emp_inames h.name) 1 (fun _ -> emp);
  fold shared h;
}

divergent fn perform (h:handle { well_named h }) (op:H.operation) (k:Q.key h.set)
  preserves shared h
  returns r:bool
{
  prepare h op k;
  unfold shared;
  if (H.Add? op) {
    rewrite each op as H.Add;
    let r = O.add h.set k (add_inv emp_inames h.name) 1 (fun _ -> emp);
    fold shared h;
    r
  } else if (H.Remove? op) {
    rewrite each op as H.Remove;
    let r = O.remove h.set k (add_inv emp_inames h.name) 1 (fun _ -> emp);
    fold shared h;
    r
  } else {
    rewrite each op as H.Contains;
    let r = O.contains h.set k (add_inv emp_inames h.name) 1 (fun _ -> emp);
    fold shared h;
    r
  }
}

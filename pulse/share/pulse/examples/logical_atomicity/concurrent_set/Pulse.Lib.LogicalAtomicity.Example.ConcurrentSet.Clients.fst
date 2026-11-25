module Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Clients
#lang-pulse

(**
Sequential specialization of the logically atomic interface.

Private model ownership gives a zero-credit AU; exactly the same add/remove/
contains implementations are used by the concurrent clients. The regression
checks insertion order, duplicate insertion, absent removal, membership,
removal of head/middle/tail elements, and reinsertion of a recycled node.
Its final model is proved empty, not merely observed empty by a native test.
*)

open Pulse.Lib.Pervasives
module H = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Model
module Q = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.State
module O = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Operations
module D = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Actions

(** Turn private model ownership into the public AU and recover its exact beta. *)
divergent fn owned (q:Q.set) (op:H.operation) (k:Q.key q)
  (#s:erased (Q.contents q.Q.cells))
  preserves Q.is_set q
  requires Q.model q s
  returns r:bool
  ensures Q.model q (H.after op s k) ** pure (r == H.answer op s k)
{
  fold O.alpha q s;
  D.from_owned (O.alpha q) (O.beta q op k) s;
  fold O.update q op k emp_inames 0 (fun r -> O.beta q op k s r);
  match op {
    H.Add -> {
      let r = O.add q k emp_inames 0 (fun r -> O.beta q op k s r);
      unfold O.beta;
      r
    }
    H.Remove -> {
      let r = O.remove q k emp_inames 0 (fun r -> O.beta q op k s r);
      unfold O.beta;
      r
    }
    H.Contains -> {
      let r = O.contains q k emp_inames 0 (fun r -> O.beta q op k s r);
      unfold O.beta;
      r
    }
  }
}

(** Return the allocated set and a true diagnostic, with an exact empty model. *)
divergent fn sequential ()
  returns result:(Q.set & bool)
  ensures pure (Q.capacity (fst result) == 6 /\ snd result) **
    Q.is_set (fst result) ** Q.model (fst result) (H.empty 6)
{
  let q = Q.create 6;
  let a = owned q H.Add 1;
  let b = owned q H.Add 4;
  let c = owned q H.Add 2;
  let duplicate = owned q H.Add 4;
  let middle = owned q H.Remove 2;
  let absent = owned q H.Contains 2;
  let recycled = owned q H.Add 2;
  let missing = owned q H.Remove 6;
  let head = owned q H.Remove 1;
  let tail = owned q H.Remove 4;
  let last = owned q H.Remove 2;
  with s. assert (Q.model q s);
  FStar.Seq.lemma_eq_intro s (H.empty 6);
  rewrite Q.model q s as Q.model q (H.empty 6);
  let ok = a && b && c && not duplicate && middle && not absent &&
    recycled && not missing && head && tail && last;
  (q, ok)
}

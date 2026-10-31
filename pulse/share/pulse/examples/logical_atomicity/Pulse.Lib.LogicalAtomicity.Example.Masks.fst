module Pulse.Lib.LogicalAtomicity.Example.Masks

(**
Non-lexical invariant lifetimes using only verified library combinators.

The trace is {} -> {i} -> {i,j} -> {j} -> {}. Opening i then j and closing i
first is not expressible by nesting lexical invariant blocks, but is safe
because the masks and spatial bodies track all outstanding obligations.
This illustrates the motivation for Iris-style mask-changing updates,
remembering that these masks track OPEN rather than enabled invariants.

There are no observable steps here. Each opening consumes one later credit;
the final runner checks balance. This is not a relaxation of Pulse's
checker, nor permission to let invariant bodies escape into ordinary code.
*)

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks
module I = Pulse.Lib.LogicalAtomicity.Invariant

(** Compose the four ghost transitions, framing each other invariant's
resources. Extensional equality of {i,j} and {j,i} justifies reindexing at
the first close; it does not remove a name without restoring its body. *)
let non_lifo (i:iname) (j:iname { not (j == i) }) (p q:slprop)
  : M.gaction unit emp_inames emp_inames
      (inv i p ** inv j q ** later_credit 1 ** later_credit 1)
      (fun _ -> inv i p ** inv j q) =
  slprop_equivs ();
  let mi = add_inv emp_inames i in
  let mj = add_inv emp_inames j in
  FStar.GhostSet.lemma_equal_intro (add_inv mi j) (add_inv mj i);
  M.bind_ghost
    (M.sub_ghost
      (inv i p ** inv j q ** later_credit 1 ** later_credit 1)
      (fun _ -> inv j q ** later_credit 1 ** (inv i p ** p))
      (M.frame_ghost (inv j q ** later_credit 1) (I.open_inv emp_inames i p)))
    (fun _ ->
      M.bind_ghost
        (M.sub_ghost
          (inv j q ** later_credit 1 ** (inv i p ** p))
          (fun _ -> inv i p ** p ** (inv j q ** q))
          (M.frame_ghost (inv i p ** p) (I.open_inv mi j q)))
        (fun _ ->
          M.bind_ghost
            (M.reindex_ghost (add_inv mi j) mj
              (M.sub_ghost
                (inv i p ** p ** (inv j q ** q))
                (fun _ -> inv i p ** (inv j q ** q))
                (M.frame_ghost (inv j q ** q) (I.close_inv mj i p))))
            (fun _ ->
              M.sub_ghost
                (inv i p ** (inv j q ** q))
                (fun _ -> inv i p ** inv j q)
                (M.frame_ghost (inv i p) (I.close_inv emp_inames j q)))))

(** Run the balanced proof as an ordinary neutral atomic computation. The
returned resources are handles only; both bodies have been closed again. *)
let balanced (i:iname) (j:iname { not (j == i) }) (p q:slprop)
  : stt_atomic unit #Neutral all_inames
      (inv i p ** inv j q ** later_credit 1 ** later_credit 1)
      (fun _ -> inv i p ** inv j q) =
  M.run_closed (M.finish_ghost () (fun _ -> inv i p ** inv j q) (non_lifo i j p q))

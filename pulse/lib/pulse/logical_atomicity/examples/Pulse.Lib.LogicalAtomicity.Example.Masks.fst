module Pulse.Lib.LogicalAtomicity.Example.Masks

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks
module I = Pulse.Lib.LogicalAtomicity.Invariant

// Open i, open j, close i, close j: closing is deliberately not stack-shaped.
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

// The ghost resources never escape into an ordinary computation with open masks.
let balanced (i:iname) (j:iname { not (j == i) }) (p q:slprop)
  : stt_atomic unit #Neutral all_inames
      (inv i p ** inv j q ** later_credit 1 ** later_credit 1)
      (fun _ -> inv i p ** inv j q) =
  M.run_closed (M.finish_ghost () (fun _ -> inv i p ** inv j q) (non_lifo i j p q))

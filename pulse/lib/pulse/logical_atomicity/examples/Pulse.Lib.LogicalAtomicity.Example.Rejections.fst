module Pulse.Lib.LogicalAtomicity.Example.Rejections

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks
module I = Pulse.Lib.LogicalAtomicity.Invariant
module A = Pulse.Lib.LogicalAtomicity.Atomic

let open_once (i:iname) (p:slprop) = I.open_inv emp_inames i p

[@@expect_failure [19]]
let open_twice (i:iname) (p:slprop) =
  I.open_inv (add_inv emp_inames i) i p

[@@expect_failure [12]]
let escape_open_mask (i:iname) (p:slprop) =
  M.run_closed #(FStar.Ghost.erased unit) #Neutral
    #(inv i p ** later_credit 1) #(fun _ -> inv i p ** p)
    (M.ghost_to_action (I.open_inv emp_inames i p))

let one_observable (p:slprop)
  (f:M.action unit Observable emp_inames emp_inames p (fun _ -> p)) =
  M.bind f (fun _ -> M.return emp_inames () (fun _ -> p))

[@@expect_failure [19]]
let two_observables (p:slprop)
  (f:M.action unit Observable emp_inames emp_inames p (fun _ -> p)) =
  M.bind f (fun _ -> f)

[@@expect_failure [19]]
let missing_credit (inner:inames)
  (alpha:unit -> slprop) (beta phi:unit -> unit -> slprop)
  : M.gaction unit emp_inames inner
      (A.atomic_update emp_inames inner 1 alpha beta phi)
      (fun _ -> A.opened emp_inames inner alpha
        (A.atomic_update emp_inames inner 1 alpha beta phi) beta phi) =
  A.open_update emp_inames inner 1 alpha beta phi

let trivial_alpha (_:unit) = emp
let trivial_beta (_ _:unit) = emp

let commit_once () =
  A.commit emp_inames emp_inames trivial_alpha emp trivial_beta trivial_beta () ()

[@@expect_failure [19]]
let commit_twice () =
  M.bind_ghost (commit_once ()) (fun _ -> commit_once ())

[@@expect_failure [19]]
let abort_after_commit () =
  M.bind_ghost (commit_once ())
    (fun _ -> A.abort emp_inames emp_inames trivial_alpha emp trivial_beta trivial_beta ())

// Hidden captured state is not in general sendable; Helping uses SendableTrade.
[@@expect_failure [228]]
let send_arbitrary_update (inner:inames)
  (alpha:unit -> slprop) (beta phi:unit -> unit -> slprop)
  : is_send (A.atomic_update emp_inames inner 1 alpha beta phi) =
  FStar.Tactics.Typeclasses.solve

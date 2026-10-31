module Pulse.Lib.LogicalAtomicity.Example.Rejections

(**
Negative specifications for the logical-atomicity safety boundary.

Each expect_failure must be rejected for its annotated diagnostic class;
positive controls show that neighboring legal uses still typecheck. These
are misuse regressions, not axioms, runtime tests, or admitted implementations.
They protect mask balance, one-observable-step composition, explicit credit
accounting, one-use closing, and the absence of generic AU sendability.

Use --print_expected_failures when changing these APIs to inspect the actual
failure as well as its number: an unrelated failure with the same diagnostic
class is not evidence that the intended misuse remains rejected.
*)

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks
module I = Pulse.Lib.LogicalAtomicity.Invariant
module A = Pulse.Lib.LogicalAtomicity.Atomic

(** Positive control: a previously closed name may be opened. *)
let open_once (i:iname) (p:slprop) = I.open_inv emp_inames i p

(** Rejected: i is already in the current open mask. *)
[@@expect_failure [19]]
let open_twice (i:iname) (p:slprop) =
  I.open_inv (add_inv emp_inames i) i p

(** Rejected: run_closed cannot expose an unclosed invariant body. *)
[@@expect_failure [12]]
let escape_open_mask (i:iname) (p:slprop) =
  M.run_closed #(FStar.Ghost.erased unit) #Neutral
    #(inv i p ** later_credit 1) #(fun _ -> inv i p ** p)
    (M.ghost_to_action (I.open_inv emp_inames i p))

(** Positive control: a neutral return may follow one observable action. *)
let one_observable (p:slprop)
  (f:M.action unit Observable emp_inames emp_inames p (fun _ -> p)) =
  M.bind f (fun _ -> M.return emp_inames () (fun _ -> p))

(** Rejected: resource matching does not make two physical steps atomic. *)
[@@expect_failure [19]]
let two_observables (p:slprop)
  (f:M.action unit Observable emp_inames emp_inames p (fun _ -> p)) =
  M.bind f (fun _ -> f)

(** Rejected: owning an AU is not ownership of its opening credit. *)
[@@expect_failure [19]]
let missing_credit (inner:inames)
  (alpha:unit -> slprop) (beta phi:unit -> unit -> slprop)
  : M.gaction unit emp_inames inner
      (A.atomic_update emp_inames inner 1 alpha beta phi)
      (fun _ -> A.opened emp_inames inner alpha
        (A.atomic_update emp_inames inner 1 alpha beta phi) beta phi) =
  A.open_update emp_inames inner 1 alpha beta phi

(** Empty operation resources isolate the closing-capability obligation. *)
let trivial_alpha (_:unit) = emp
(** Even when beta and phi are emp, closing itself remains one-use. *)
let trivial_beta (_ _:unit) = emp

(** Positive control: one commit consumes its required closing capability. *)
let commit_once () =
  A.commit emp_inames emp_inames trivial_alpha emp trivial_beta trivial_beta () ()

(** Rejected: the first commit does not return a second closing capability. *)
[@@expect_failure [19]]
let commit_twice () =
  M.bind_ghost (commit_once ()) (fun _ -> commit_once ())

(** Rejected: commit has already consumed the additive abort/commit choice. *)
[@@expect_failure [19]]
let abort_after_commit () =
  M.bind_ghost (commit_once ())
    (fun _ -> A.abort emp_inames emp_inames trivial_alpha emp trivial_beta trivial_beta ())

(** Rejected: hidden captured state is not in general sendable. Helping
transfers a SendableTrade recipe and constructs the AU on the worker. *)
[@@expect_failure [228]]
let send_arbitrary_update (inner:inames)
  (alpha:unit -> slprop) (beta phi:unit -> unit -> slprop)
  : is_send (A.atomic_update emp_inames inner 1 alpha beta phi) =
  FStar.Tactics.Typeclasses.solve

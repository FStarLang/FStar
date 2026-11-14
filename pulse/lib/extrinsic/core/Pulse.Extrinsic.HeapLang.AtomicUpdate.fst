module Pulse.Extrinsic.HeapLang.AtomicUpdate

(** Resource-parametric atomic-update specification, not a program proof.
    Opening retry yields an existential current abstract state and one closing
    resource. Abort restores retry; commitment consumes beta and closing to
    establish phi. The same spatial closing resource supports the alternative
    branches; the pure protocol evidence itself grants no duplicate ownership.

    This follows native Pulse's abort/commit organization but is a judgment,
    not a first-class Iris AU assertion or a history-based linearizability
    theorem. The multi-step CAS implementation and independent clients live in
    examples/; this module states only the logical protocol they share. *)

module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof

let opened (#a:Type0) (alpha closing:a -> S.slprop) =
  S.op_exists_Star (fun x -> S.star (alpha x) (closing x))

// Closing is one spatial resource shared by the alternative abort/commit rules.
// Abort restores retry ownership; commitment need not return it.
let protocol (#a #b:Type0) (outer inner:S.inames) (retry:S.slprop)
  (alpha:a -> S.slprop) (beta phi:a -> b -> S.slprop) (closing:a -> S.slprop) =
  P.update outer inner retry (opened alpha closing) /\
  (forall x. P.update inner outer (S.star (alpha x) (closing x)) retry) /\
  (forall x y. P.update inner outer (S.star (beta x y) (closing x)) (phi x y))

module Pulse.Extrinsic.HeapLang.AtomicUpdate

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

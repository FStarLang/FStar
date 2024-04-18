module Misc.Norm1

(* This once triggered a very subtle normalizer failure due to dropping
the ascription during reduction, as it ocurred in the argument of an
application. Keeping here as mini test. *)

let fa_intro_lem (#a:Type) (#p:a -> Type) (f:(x:a -> squash (p x))) : Lemma (forall (x:a). p x) =
  FStar.Classical.lemma_forall_intro_gtot
    ((fun x -> FStar.IndefiniteDescription.elim_squash (f x)) <: (x:a -> GTot (p x)))

module DeltaDepthUnif

(* Misc tests about unification, unfolding, etc *)

open FStar.Reflection.V2
open FStar.Reflection.Typing
open FStar.Mul

assume val tyc : term -> Type0

let test (x : tyc bool_ty)
 : tyc (binder_sort (mk_binder (Sealed.seal "x") bool_ty Q_Explicit))
 = x

open FStar.Squash

assume val p : Type0

val test1 : (~p)
let test1 = return_squash (magic ())

assume val f : p -> False
val test2 : (~p)
let test2 = return_squash f

assume
val ty : int -> Type
let test3 (#n:nat) (x : ty 0) : ty (0 * n) = x

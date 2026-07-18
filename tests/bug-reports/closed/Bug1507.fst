module Bug1507

(*
 * This type should be rejected since f may be instantiated with an arrow
 *   that could lead to proof of False, e.g.
 *
 * let f_false : Type0 -> Type0 = fun a -> (a -> squash False)
 *
 * let g : f_false (mu f_false) =
 *   fun x ->
 *   match x with
 *   | Mu h -> h x
 *
 * let r1 : squash False = g (Mu g)
 *
 *)

[@@ expect_failure]
noeq
type mu (f: Type -> Type) = 
    | Mu of f (mu f)

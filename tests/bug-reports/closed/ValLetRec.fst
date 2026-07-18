module ValLetRec

(* See PR #2915 *)

type tt =
  | A of tt
  | B of int

type _cmpres =
  | Eq
  | Neq

type cmpres #t (x y : t) = c:_cmpres
type comparator_for (t:Type) = x:t -> y:t -> cmpres x y

val eq_cmp : #a:eqtype -> comparator_for a
let eq_cmp x y = if x = y then Eq else Neq

val cmp : comparator_for tt
let rec cmp (u1 u2 : tt) =
  match u1, u2 with
  | A x, A y -> cmp x y
  | B x, B y -> eq_cmp x y
  | _ -> Neq

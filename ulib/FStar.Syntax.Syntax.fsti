module FStar.Syntax.Syntax
open FStar.Reflection.Types

(* Do not look at me! *)
type hack = { sort:int }

noeq
type subst_elt =
  | DB : int -> namedv -> subst_elt
  | NM : namedv -> int -> subst_elt
  | NT : namedv -> term -> subst_elt
  | UN : int -> universe -> subst_elt
  | UD : univ_name -> int -> subst_elt
type subst_t = list subst_elt

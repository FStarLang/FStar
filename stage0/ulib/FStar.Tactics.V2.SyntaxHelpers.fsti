module FStar.Tactics.V2.SyntaxHelpers

open FStar.Reflection.V2
open FStar.Tactics.Effect
open FStar.Tactics.NamedView

(* These are fully-named variants of functions found in FStar.Reflection *)

[@@plugin]
val collect_arr_bs : typ -> Tac (list binder & comp)

[@@plugin]
val collect_arr : typ -> Tac (list typ & comp)

[@@plugin]
val collect_abs : term -> Tac (list binder & term)

[@@plugin]
val mk_arr (bs: list binder) (cod : comp) : Tac term

[@@plugin]
val mk_tot_arr (bs: list binder) (cod : term) : Tac term

[@@plugin]
val lookup_lb (lbs:list letbinding) (nm:name) : Tac letbinding

[@@plugin]
val inspect_unascribe (t:term) : Tac (tv:term_view{notAscription tv})

(* Helpers for dealing with nested applications and arrows *)

[@@plugin]
val collect_app (t:term) : Tac (term & list argv)

(* Destruct an application into [h]ead fv, [u]niverses, and [a]rguments. *)
[@@plugin]
val hua (t:term) : Tac (option (fv & universes & list argv))

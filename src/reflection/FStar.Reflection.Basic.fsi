#light "off"
module FStar.Reflection.Basic

open FStar.Ident
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.Order
open FStar.TypeChecker.Env
open FStar.Reflection.Data

(* Primitives *)
val compare_binder : binder -> binder -> order
val lookup_typ     : FStar.TypeChecker.Env.env -> list<string> -> sigelt_view
val is_free        : binder -> term -> bool
val binders_of_env : FStar.TypeChecker.Env.env -> binders
val type_of_binder : binder -> typ
val term_eq        : term -> term -> bool
val term_to_string : term -> string

(* Views *)
val inspect_fv    : fv -> list<string>
val pack_fv       : list<string> -> fv

val inspect_bv    : binder -> string
// no bv pack

val inspect_const : sconst -> vconst
val pack_const    : vconst -> sconst

val inspect       : term -> term_view
val pack          : term_view -> term

val inspect_comp  : comp -> comp_view
val pack_comp     : comp_view -> comp

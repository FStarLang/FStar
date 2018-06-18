#light "off"
module FStar.Reflection.Basic

open FStar.Ident
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.Order
module Env = FStar.TypeChecker.Env
open FStar.Reflection.Data

(* Primitives *)
val compare_bv     : bv -> bv -> order
val lookup_typ     : Env.env -> list<string> -> option<sigelt>
val is_free        : bv -> term -> bool
val lookup_attr    : term -> Env.env -> list<fv>
val binders_of_env : Env.env -> binders
val moduleof       : Env.env -> list<string>
val term_eq        : term -> term -> bool
val term_to_string : term -> string

(* Views *)
val inspect_fv    : fv -> list<string>
val pack_fv       : list<string> -> fv

val inspect_const : sconst -> vconst
val pack_const    : vconst -> sconst

val inspect_ln    : term -> term_view
val pack_ln       : term_view -> term

val inspect_comp  : comp -> comp_view
val pack_comp     : comp_view -> comp

val inspect_sigelt : sigelt -> sigelt_view
val pack_sigelt    : sigelt_view -> sigelt

val inspect_bv     : bv -> bv_view
val pack_bv        : bv_view -> bv

val inspect_binder : binder -> bv * aqualv
val pack_binder    : bv -> aqualv -> binder

val inspect_aqual  : aqual -> aqualv
val pack_aqual     : aqualv -> aqual

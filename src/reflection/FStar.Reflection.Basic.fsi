#light "off"
module FStar.Reflection.Basic

open FStar.Ident
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.Order
module Env = FStar.TypeChecker.Env
open FStar.Reflection.Data
open FStar.ST
module O = FStar.Options
module RD = FStar.Reflection.Data
module EMB = FStar.Syntax.Embeddings

(* Tying a knot into the environment which started execution.
 * Needed to inspect sigelts and the like without needing
 * to explicitly pass it in. This entire module should really be in
 * the TAC effect, and this crap is a symptom, let's move it. *)
val env_hook : ref<option<Env.env>>

(* Another hack to circumvent module recursion *)
val e_optionstate_hook : ref<option<EMB.embedding<O.optionstate>>>

(* Primitives *)
val compare_bv            : bv -> bv -> order
val lookup_typ            : Env.env -> list<string> -> option<sigelt>
val is_free               : bv -> term -> bool
val lookup_attr           : term -> Env.env -> list<fv>
val all_defs_in_env       : Env.env -> list<fv>
val defs_in_module        : Env.env -> name -> list<fv>
val binders_of_env        : Env.env -> binders
val moduleof              : Env.env -> list<string>
val term_eq               : term -> term -> bool
val term_to_string        : term -> string
val comp_to_string        : comp -> string
val env_open_modules      : Env.env -> list<name>
val sigelt_opts           : sigelt -> option<term>

val sigelt_attrs     : sigelt -> list<attribute>
val set_sigelt_attrs : list<attribute> -> sigelt -> sigelt

val sigelt_quals     : sigelt -> list<RD.qualifier>
val set_sigelt_quals : list<RD.qualifier> -> sigelt -> sigelt

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

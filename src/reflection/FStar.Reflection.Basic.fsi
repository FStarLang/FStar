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

(* Lazy unfoldings *)
val unfold_lazy_fvar   : lazyinfo -> term
val unfold_lazy_binder : lazyinfo -> term
val unfold_lazy_comp   : lazyinfo -> term
val unfold_lazy_env    : lazyinfo -> term

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

(* Embeddings, split out of here? *)
val embed_binder        : embedder<binder>
val unembed_binder      : unembedder<binder>

val embed_binders       : embedder<binders>
val unembed_binders     : unembedder<binders>

val embed_term          : embedder<term>
val unembed_term        : unembedder<term>

val embed_term_view     : embedder<term_view>
val unembed_term_view   : unembedder<term_view>

val embed_fvar          : embedder<fv>
val unembed_fvar        : unembedder<fv>

val embed_comp          : embedder<comp>
val unembed_comp        : unembedder<comp>

val embed_comp_view     : embedder<comp_view>
val unembed_comp_view   : unembedder<comp_view>

val embed_const         : embedder<vconst>
val unembed_const       : unembedder<vconst>

val embed_env           : embedder<FStar.TypeChecker.Env.env>
val unembed_env         : unembedder<FStar.TypeChecker.Env.env>

val embed_pattern       : embedder<pattern>
val unembed_pattern     : unembedder<pattern>

val embed_branch        : embedder<Data.branch>
val unembed_branch      : unembedder<Data.branch>

val embed_aqualv        : embedder<aqualv>
val unembed_aqualv      : unembedder<aqualv>

val embed_argv          : embedder<argv>
val unembed_argv        : unembedder<argv>

val embed_order         : embedder<order>
val unembed_order       : unembedder<order>

val embed_sigelt_view   : embedder<sigelt_view>
val unembed_sigelt_view : unembedder<sigelt_view>

val embed_ctor          : embedder<ctor>
val unembed_ctor        : unembedder<ctor>

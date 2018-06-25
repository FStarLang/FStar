#light "off"
module FStar.Reflection.Embeddings

open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.Order
open FStar.TypeChecker.Env
open FStar.Reflection.Data

(* Embeddings *)
val e_bv          : embedding<bv>
val e_binder      : embedding<binder>
val e_binder_view : embedding<binder_view>
val e_binders     : embedding<binders>
val e_term        : embedding<term>
val e_term_view   : embedding<term_view>
val e_fv          : embedding<fv>
val e_comp        : embedding<comp>
val e_comp_view   : embedding<comp_view>
val e_const       : embedding<vconst>
val e_env         : embedding<FStar.TypeChecker.Env.env>
val e_pattern     : embedding<pattern>
val e_branch      : embedding<Data.branch>
val e_aqualv      : embedding<aqualv>
val e_argv        : embedding<argv>
val e_order       : embedding<order>
val e_sigelt      : embedding<sigelt>
val e_sigelt_view : embedding<sigelt_view>
val e_bv_view     : embedding<bv_view>
val e_exp         : embedding<exp>
val e_attribute   : embedding<attribute>
val e_attributes  : embedding<list<attribute>> (* This seems rather silly, but `attributes` is a keyword *)

(* Useful for embedding antiquoted terms. They are only used for the embedding part,
 * so this is a bit hackish. *)
val e_term_aq       : antiquotations -> embedding<term>
val e_term_view_aq  : antiquotations -> embedding<term_view>

(* Lazy unfoldings *)
val unfold_lazy_bv     : lazyinfo -> term
val unfold_lazy_fvar   : lazyinfo -> term
val unfold_lazy_binder : lazyinfo -> term
val unfold_lazy_comp   : lazyinfo -> term
val unfold_lazy_env    : lazyinfo -> term
val unfold_lazy_sigelt : lazyinfo -> term

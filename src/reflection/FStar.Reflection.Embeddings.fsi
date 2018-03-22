#light "off"
module FStar.Reflection.Embeddings

open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.Order
open FStar.TypeChecker.Env
open FStar.Reflection.Data


(* Lazy unfoldings *)
val unfold_lazy_bv     : lazyinfo -> term
val unfold_lazy_fvar   : lazyinfo -> term
val unfold_lazy_binder : lazyinfo -> term
val unfold_lazy_comp   : lazyinfo -> term
val unfold_lazy_env    : lazyinfo -> term
val unfold_lazy_sigelt : lazyinfo -> term

(* Embeddings *)

val embed_bv            : embedder<bv>
val unembed_bv          : unembedder<bv>

val embed_binder        : embedder<binder>
val unembed_binder      : unembedder<binder>

val embed_binder_view   : embedder<(bv * aqualv)>
val unembed_binder_view : unembedder<(bv * aqualv)>

val embed_binders       : embedder<binders>
val unembed_binders     : unembedder<binders>

val embed_term_aq       : antiquotations -> embedder<term>
val embed_term          : embedder<term>
val unembed_term        : unembedder<term>

val embed_term_view_aq  : antiquotations -> embedder<term_view>
val embed_term_view     : embedder<term_view>
val unembed_term_view   : unembedder<term_view>

val embed_fv            : embedder<fv>
val unembed_fv          : unembedder<fv>

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

val embed_sigelt        : embedder<sigelt>
val unembed_sigelt      : unembedder<sigelt>

val embed_sigelt_view   : embedder<sigelt_view>
val unembed_sigelt_view : unembedder<sigelt_view>

val embed_bv_view       : embedder<bv_view>
val unembed_bv_view     : unembedder<bv_view>

val embed_exp       : embedder<exp>
val unembed_exp     : unembedder<exp>

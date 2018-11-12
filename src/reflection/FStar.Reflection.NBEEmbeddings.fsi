#light "off"
module FStar.Reflection.NBEEmbeddings

open FStar
open FStar.Syntax.Syntax
open FStar.TypeChecker.NBETerm
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
val e_comp        : embedding<FStar.Syntax.Syntax.comp>
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
val e_ident       : embedding<Ident.ident>
val e_univ_name   : embedding<univ_name>
val e_univ_names  : embedding<list<univ_name>>

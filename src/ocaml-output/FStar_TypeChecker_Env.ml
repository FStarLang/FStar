
open Prims
open FStar_Pervasives
type binding =
| Binding_var of FStar_Syntax_Syntax.bv
| Binding_lid of (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme)
| Binding_sig of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
| Binding_univ of FStar_Syntax_Syntax.univ_name
| Binding_sig_inst of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes)


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____43 -> begin
false
end))


let __proj__Binding_var__item___0 : binding  ->  FStar_Syntax_Syntax.bv = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
_0
end))


let uu___is_Binding_lid : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_lid (_0) -> begin
true
end
| uu____59 -> begin
false
end))


let __proj__Binding_lid__item___0 : binding  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme) = (fun projectee -> (match (projectee) with
| Binding_lid (_0) -> begin
_0
end))


let uu___is_Binding_sig : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_sig (_0) -> begin
true
end
| uu____89 -> begin
false
end))


let __proj__Binding_sig__item___0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt) = (fun projectee -> (match (projectee) with
| Binding_sig (_0) -> begin
_0
end))


let uu___is_Binding_univ : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_univ (_0) -> begin
true
end
| uu____119 -> begin
false
end))


let __proj__Binding_univ__item___0 : binding  ->  FStar_Syntax_Syntax.univ_name = (fun projectee -> (match (projectee) with
| Binding_univ (_0) -> begin
_0
end))


let uu___is_Binding_sig_inst : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_0) -> begin
true
end
| uu____139 -> begin
false
end))


let __proj__Binding_sig_inst__item___0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes) = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_0) -> begin
_0
end))

type delta_level =
| NoDelta
| Inlining
| Eager_unfolding_only
| Unfold of FStar_Syntax_Syntax.delta_depth
| UnfoldTac


let uu___is_NoDelta : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoDelta -> begin
true
end
| uu____178 -> begin
false
end))


let uu___is_Inlining : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____182 -> begin
false
end))


let uu___is_Eager_unfolding_only : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding_only -> begin
true
end
| uu____186 -> begin
false
end))


let uu___is_Unfold : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unfold (_0) -> begin
true
end
| uu____191 -> begin
false
end))


let __proj__Unfold__item___0 : delta_level  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| Unfold (_0) -> begin
_0
end))


let uu___is_UnfoldTac : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldTac -> begin
true
end
| uu____202 -> begin
false
end))

type mlift =
{mlift_wp : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ; mlift_term : (FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option}


let __proj__Mkmlift__item__mlift_wp : mlift  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| {mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term} -> begin
__fname__mlift_wp
end))


let __proj__Mkmlift__item__mlift_term : mlift  ->  (FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term} -> begin
__fname__mlift_term
end))

type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : mlift}


let __proj__Mkedge__item__msource : edge  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {msource = __fname__msource; mtarget = __fname__mtarget; mlift = __fname__mlift} -> begin
__fname__msource
end))


let __proj__Mkedge__item__mtarget : edge  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {msource = __fname__msource; mtarget = __fname__mtarget; mlift = __fname__mlift} -> begin
__fname__mtarget
end))


let __proj__Mkedge__item__mlift : edge  ->  mlift = (fun projectee -> (match (projectee) with
| {msource = __fname__msource; mtarget = __fname__mtarget; mlift = __fname__mlift} -> begin
__fname__mlift
end))

type effects =
{decls : (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}


let __proj__Mkeffects__item__decls : effects  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) Prims.list = (fun projectee -> (match (projectee) with
| {decls = __fname__decls; order = __fname__order; joins = __fname__joins} -> begin
__fname__decls
end))


let __proj__Mkeffects__item__order : effects  ->  edge Prims.list = (fun projectee -> (match (projectee) with
| {decls = __fname__decls; order = __fname__order; joins = __fname__joins} -> begin
__fname__order
end))


let __proj__Mkeffects__item__joins : effects  ->  (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list = (fun projectee -> (match (projectee) with
| {decls = __fname__decls; order = __fname__order; joins = __fname__joins} -> begin
__fname__joins
end))


type name_prefix =
Prims.string Prims.list


type proof_namespace =
(name_prefix * Prims.bool) Prims.list


type cached_elt =
(((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option)) FStar_Util.either * FStar_Range.range)


type goal =
FStar_Syntax_Syntax.term

type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.univ_names) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; lax : Prims.bool; lax_universes : Prims.bool; failhard : Prims.bool; nosynth : Prims.bool; tc_term : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t); type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; check_type_of : Prims.bool  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  guard_t; use_bv_sorts : Prims.bool; qtbl_name_and_index : (Prims.int FStar_Util.smap * (FStar_Ident.lident * Prims.int) FStar_Pervasives_Native.option); proof_ns : proof_namespace; synth_hook : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term; splice : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list; is_native_tactic : FStar_Ident.lid  ->  Prims.bool; identifier_info : FStar_TypeChecker_Common.id_info_table FStar_ST.ref; tc_hooks : tcenv_hooks; dsenv : FStar_Syntax_DsEnv.env; dep_graph : FStar_Parser_Dep.deps} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; preprocess : env  ->  goal  ->  (env * goal * FStar_Options.optionstate) Prims.list; solve : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : (FStar_Syntax_Syntax.universe Prims.list * FStar_TypeChecker_Common.univ_ineq Prims.list); implicits : (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list} 
 and tcenv_hooks =
{tc_push_in_gamma_hook : env  ->  binding  ->  Prims.unit}


let __proj__Mkenv__item__solver : env  ->  solver_t = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__solver
end))


let __proj__Mkenv__item__range : env  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__range
end))


let __proj__Mkenv__item__curmodule : env  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__curmodule
end))


let __proj__Mkenv__item__gamma : env  ->  binding Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__gamma
end))


let __proj__Mkenv__item__gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__gamma_cache
end))


let __proj__Mkenv__item__modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__modules
end))


let __proj__Mkenv__item__expected_typ : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__expected_typ
end))


let __proj__Mkenv__item__sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__sigtab
end))


let __proj__Mkenv__item__is_pattern : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__is_pattern
end))


let __proj__Mkenv__item__instantiate_imp : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__instantiate_imp
end))


let __proj__Mkenv__item__effects : env  ->  effects = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__effects
end))


let __proj__Mkenv__item__generalize : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__generalize
end))


let __proj__Mkenv__item__letrecs : env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.univ_names) Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__letrecs
end))


let __proj__Mkenv__item__top_level : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__top_level
end))


let __proj__Mkenv__item__check_uvars : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__check_uvars
end))


let __proj__Mkenv__item__use_eq : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__use_eq
end))


let __proj__Mkenv__item__is_iface : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__is_iface
end))


let __proj__Mkenv__item__admit : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__admit
end))


let __proj__Mkenv__item__lax : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__lax
end))


let __proj__Mkenv__item__lax_universes : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__lax_universes
end))


let __proj__Mkenv__item__failhard : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__failhard
end))


let __proj__Mkenv__item__nosynth : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__nosynth
end))


let __proj__Mkenv__item__tc_term : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t) = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__tc_term
end))


let __proj__Mkenv__item__type_of : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t) = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__type_of
end))


let __proj__Mkenv__item__universe_of : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__universe_of
end))


let __proj__Mkenv__item__check_type_of : env  ->  Prims.bool  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  guard_t = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__check_type_of
end))


let __proj__Mkenv__item__use_bv_sorts : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__use_bv_sorts
end))


let __proj__Mkenv__item__qtbl_name_and_index : env  ->  (Prims.int FStar_Util.smap * (FStar_Ident.lident * Prims.int) FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__qtbl_name_and_index
end))


let __proj__Mkenv__item__proof_ns : env  ->  proof_namespace = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__proof_ns
end))


let __proj__Mkenv__item__synth_hook : env  ->  env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__synth_hook
end))


let __proj__Mkenv__item__splice : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__splice
end))


let __proj__Mkenv__item__is_native_tactic : env  ->  FStar_Ident.lid  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__is_native_tactic
end))


let __proj__Mkenv__item__identifier_info : env  ->  FStar_TypeChecker_Common.id_info_table FStar_ST.ref = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__identifier_info
end))


let __proj__Mkenv__item__tc_hooks : env  ->  tcenv_hooks = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__tc_hooks
end))


let __proj__Mkenv__item__dsenv : env  ->  FStar_Syntax_DsEnv.env = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__dsenv
end))


let __proj__Mkenv__item__dep_graph : env  ->  FStar_Parser_Dep.deps = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; check_type_of = __fname__check_type_of; use_bv_sorts = __fname__use_bv_sorts; qtbl_name_and_index = __fname__qtbl_name_and_index; proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook; splice = __fname__splice; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv; dep_graph = __fname__dep_graph} -> begin
__fname__dep_graph
end))


let __proj__Mksolver_t__item__init : solver_t  ->  env  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__init
end))


let __proj__Mksolver_t__item__push : solver_t  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__push
end))


let __proj__Mksolver_t__item__pop : solver_t  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__pop
end))


let __proj__Mksolver_t__item__encode_modul : solver_t  ->  env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__encode_modul
end))


let __proj__Mksolver_t__item__encode_sig : solver_t  ->  env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__encode_sig
end))


let __proj__Mksolver_t__item__preprocess : solver_t  ->  env  ->  goal  ->  (env * goal * FStar_Options.optionstate) Prims.list = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__preprocess
end))


let __proj__Mksolver_t__item__solve : solver_t  ->  (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__solve
end))


let __proj__Mksolver_t__item__finish : solver_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__finish
end))


let __proj__Mksolver_t__item__refresh : solver_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__refresh
end))


let __proj__Mkguard_t__item__guard_f : guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun projectee -> (match (projectee) with
| {guard_f = __fname__guard_f; deferred = __fname__deferred; univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits} -> begin
__fname__guard_f
end))


let __proj__Mkguard_t__item__deferred : guard_t  ->  FStar_TypeChecker_Common.deferred = (fun projectee -> (match (projectee) with
| {guard_f = __fname__guard_f; deferred = __fname__deferred; univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits} -> begin
__fname__deferred
end))


let __proj__Mkguard_t__item__univ_ineqs : guard_t  ->  (FStar_Syntax_Syntax.universe Prims.list * FStar_TypeChecker_Common.univ_ineq Prims.list) = (fun projectee -> (match (projectee) with
| {guard_f = __fname__guard_f; deferred = __fname__deferred; univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits} -> begin
__fname__univ_ineqs
end))


let __proj__Mkguard_t__item__implicits : guard_t  ->  (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list = (fun projectee -> (match (projectee) with
| {guard_f = __fname__guard_f; deferred = __fname__deferred; univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits} -> begin
__fname__implicits
end))


let __proj__Mktcenv_hooks__item__tc_push_in_gamma_hook : tcenv_hooks  ->  env  ->  binding  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {tc_push_in_gamma_hook = __fname__tc_push_in_gamma_hook} -> begin
__fname__tc_push_in_gamma_hook
end))


type implicits =
(Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list


let rename_gamma : FStar_Syntax_Syntax.subst_elt Prims.list  ->  binding Prims.list  ->  binding Prims.list = (fun subst1 gamma -> (FStar_All.pipe_right gamma (FStar_List.map (fun uu___74_6261 -> (match (uu___74_6261) with
| Binding_var (x) -> begin
(

let y = (

let uu____6264 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Subst.subst subst1 uu____6264))
in (

let uu____6265 = (

let uu____6266 = (FStar_Syntax_Subst.compress y)
in uu____6266.FStar_Syntax_Syntax.n)
in (match (uu____6265) with
| FStar_Syntax_Syntax.Tm_name (y1) -> begin
(

let uu____6270 = (

let uu___89_6271 = y1
in (

let uu____6272 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___89_6271.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___89_6271.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6272}))
in Binding_var (uu____6270))
end
| uu____6275 -> begin
(failwith "Not a renaming")
end)))
end
| b -> begin
b
end)))))


let rename_env : FStar_Syntax_Syntax.subst_t  ->  env  ->  env = (fun subst1 env -> (

let uu___90_6283 = env
in (

let uu____6284 = (rename_gamma subst1 env.gamma)
in {solver = uu___90_6283.solver; range = uu___90_6283.range; curmodule = uu___90_6283.curmodule; gamma = uu____6284; gamma_cache = uu___90_6283.gamma_cache; modules = uu___90_6283.modules; expected_typ = uu___90_6283.expected_typ; sigtab = uu___90_6283.sigtab; is_pattern = uu___90_6283.is_pattern; instantiate_imp = uu___90_6283.instantiate_imp; effects = uu___90_6283.effects; generalize = uu___90_6283.generalize; letrecs = uu___90_6283.letrecs; top_level = uu___90_6283.top_level; check_uvars = uu___90_6283.check_uvars; use_eq = uu___90_6283.use_eq; is_iface = uu___90_6283.is_iface; admit = uu___90_6283.admit; lax = uu___90_6283.lax; lax_universes = uu___90_6283.lax_universes; failhard = uu___90_6283.failhard; nosynth = uu___90_6283.nosynth; tc_term = uu___90_6283.tc_term; type_of = uu___90_6283.type_of; universe_of = uu___90_6283.universe_of; check_type_of = uu___90_6283.check_type_of; use_bv_sorts = uu___90_6283.use_bv_sorts; qtbl_name_and_index = uu___90_6283.qtbl_name_and_index; proof_ns = uu___90_6283.proof_ns; synth_hook = uu___90_6283.synth_hook; splice = uu___90_6283.splice; is_native_tactic = uu___90_6283.is_native_tactic; identifier_info = uu___90_6283.identifier_info; tc_hooks = uu___90_6283.tc_hooks; dsenv = uu___90_6283.dsenv; dep_graph = uu___90_6283.dep_graph})))


let default_tc_hooks : tcenv_hooks = {tc_push_in_gamma_hook = (fun uu____6291 uu____6292 -> ())}


let tc_hooks : env  ->  tcenv_hooks = (fun env -> env.tc_hooks)


let set_tc_hooks : env  ->  tcenv_hooks  ->  env = (fun env hooks -> (

let uu___91_6302 = env
in {solver = uu___91_6302.solver; range = uu___91_6302.range; curmodule = uu___91_6302.curmodule; gamma = uu___91_6302.gamma; gamma_cache = uu___91_6302.gamma_cache; modules = uu___91_6302.modules; expected_typ = uu___91_6302.expected_typ; sigtab = uu___91_6302.sigtab; is_pattern = uu___91_6302.is_pattern; instantiate_imp = uu___91_6302.instantiate_imp; effects = uu___91_6302.effects; generalize = uu___91_6302.generalize; letrecs = uu___91_6302.letrecs; top_level = uu___91_6302.top_level; check_uvars = uu___91_6302.check_uvars; use_eq = uu___91_6302.use_eq; is_iface = uu___91_6302.is_iface; admit = uu___91_6302.admit; lax = uu___91_6302.lax; lax_universes = uu___91_6302.lax_universes; failhard = uu___91_6302.failhard; nosynth = uu___91_6302.nosynth; tc_term = uu___91_6302.tc_term; type_of = uu___91_6302.type_of; universe_of = uu___91_6302.universe_of; check_type_of = uu___91_6302.check_type_of; use_bv_sorts = uu___91_6302.use_bv_sorts; qtbl_name_and_index = uu___91_6302.qtbl_name_and_index; proof_ns = uu___91_6302.proof_ns; synth_hook = uu___91_6302.synth_hook; splice = uu___91_6302.splice; is_native_tactic = uu___91_6302.is_native_tactic; identifier_info = uu___91_6302.identifier_info; tc_hooks = hooks; dsenv = uu___91_6302.dsenv; dep_graph = uu___91_6302.dep_graph}))


let set_dep_graph : env  ->  FStar_Parser_Dep.deps  ->  env = (fun e g -> (

let uu___92_6309 = e
in {solver = uu___92_6309.solver; range = uu___92_6309.range; curmodule = uu___92_6309.curmodule; gamma = uu___92_6309.gamma; gamma_cache = uu___92_6309.gamma_cache; modules = uu___92_6309.modules; expected_typ = uu___92_6309.expected_typ; sigtab = uu___92_6309.sigtab; is_pattern = uu___92_6309.is_pattern; instantiate_imp = uu___92_6309.instantiate_imp; effects = uu___92_6309.effects; generalize = uu___92_6309.generalize; letrecs = uu___92_6309.letrecs; top_level = uu___92_6309.top_level; check_uvars = uu___92_6309.check_uvars; use_eq = uu___92_6309.use_eq; is_iface = uu___92_6309.is_iface; admit = uu___92_6309.admit; lax = uu___92_6309.lax; lax_universes = uu___92_6309.lax_universes; failhard = uu___92_6309.failhard; nosynth = uu___92_6309.nosynth; tc_term = uu___92_6309.tc_term; type_of = uu___92_6309.type_of; universe_of = uu___92_6309.universe_of; check_type_of = uu___92_6309.check_type_of; use_bv_sorts = uu___92_6309.use_bv_sorts; qtbl_name_and_index = uu___92_6309.qtbl_name_and_index; proof_ns = uu___92_6309.proof_ns; synth_hook = uu___92_6309.synth_hook; splice = uu___92_6309.splice; is_native_tactic = uu___92_6309.is_native_tactic; identifier_info = uu___92_6309.identifier_info; tc_hooks = uu___92_6309.tc_hooks; dsenv = uu___92_6309.dsenv; dep_graph = g}))


let dep_graph : env  ->  FStar_Parser_Dep.deps = (fun e -> e.dep_graph)


type env_t =
env


type sigtable =
FStar_Syntax_Syntax.sigelt FStar_Util.smap


let should_verify : env  ->  Prims.bool = (fun env -> (((not (env.lax)) && (not (env.admit))) && (FStar_Options.should_verify env.curmodule.FStar_Ident.str)))


let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match (((d), (q))) with
| (NoDelta, uu____6324) -> begin
true
end
| (Eager_unfolding_only, FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____6325), FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____6326), FStar_Syntax_Syntax.Visible_default) -> begin
true
end
| (Inlining, FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| uu____6327 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab : 'Auu____6334 . Prims.unit  ->  'Auu____6334 FStar_Util.smap = (fun uu____6340 -> (FStar_Util.smap_create default_table_size))


let new_gamma_cache : 'Auu____6343 . Prims.unit  ->  'Auu____6343 FStar_Util.smap = (fun uu____6349 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let initial_env : FStar_Parser_Dep.deps  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  (Prims.bool  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  guard_t)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun deps tc_term type_of universe_of check_type_of solver module_lid -> (

let uu____6445 = (new_gamma_cache ())
in (

let uu____6448 = (new_sigtab ())
in (

let uu____6451 = (

let uu____6464 = (FStar_Util.smap_create (Prims.parse_int "10"))
in ((uu____6464), (FStar_Pervasives_Native.None)))
in (

let uu____6479 = (FStar_Options.using_facts_from ())
in (

let uu____6480 = (FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty)
in (

let uu____6483 = (FStar_Syntax_DsEnv.empty_env ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = uu____6445; modules = []; expected_typ = FStar_Pervasives_Native.None; sigtab = uu____6448; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; failhard = false; nosynth = false; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = false; qtbl_name_and_index = uu____6451; proof_ns = uu____6479; synth_hook = (fun e g tau -> (failwith "no synthesizer available")); splice = (fun e tau -> (failwith "no splicer available")); is_native_tactic = (fun uu____6519 -> false); identifier_info = uu____6480; tc_hooks = default_tc_hooks; dsenv = uu____6483; dep_graph = deps})))))))


let dsenv : env  ->  FStar_Syntax_DsEnv.env = (fun env -> env.dsenv)


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


let query_indices : (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let push_query_indices : Prims.unit  ->  Prims.unit = (fun uu____6674 -> (

let uu____6675 = (FStar_ST.op_Bang query_indices)
in (match (uu____6675) with
| [] -> begin
(failwith "Empty query indices!")
end
| uu____6731 -> begin
(

let uu____6740 = (

let uu____6749 = (

let uu____6756 = (FStar_ST.op_Bang query_indices)
in (FStar_List.hd uu____6756))
in (

let uu____6812 = (FStar_ST.op_Bang query_indices)
in (uu____6749)::uu____6812))
in (FStar_ST.op_Colon_Equals query_indices uu____6740))
end)))


let pop_query_indices : Prims.unit  ->  Prims.unit = (fun uu____6911 -> (

let uu____6912 = (FStar_ST.op_Bang query_indices)
in (match (uu____6912) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals query_indices tl1)
end)))


let add_query_index : (FStar_Ident.lident * Prims.int)  ->  Prims.unit = (fun uu____7037 -> (match (uu____7037) with
| (l, n1) -> begin
(

let uu____7044 = (FStar_ST.op_Bang query_indices)
in (match (uu____7044) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals query_indices (((((l), (n1)))::hd1)::tl1))
end
| uu____7167 -> begin
(failwith "Empty query indices")
end))
end))


let peek_query_indices : Prims.unit  ->  (FStar_Ident.lident * Prims.int) Prims.list = (fun uu____7184 -> (

let uu____7185 = (FStar_ST.op_Bang query_indices)
in (FStar_List.hd uu____7185)))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push_stack : env  ->  env = (fun env -> ((

let uu____7286 = (

let uu____7289 = (FStar_ST.op_Bang stack)
in (env)::uu____7289)
in (FStar_ST.op_Colon_Equals stack uu____7286));
(

let uu___93_7350 = env
in (

let uu____7351 = (FStar_Util.smap_copy (gamma_cache env))
in (

let uu____7354 = (FStar_Util.smap_copy (sigtab env))
in (

let uu____7357 = (

let uu____7370 = (

let uu____7373 = (FStar_All.pipe_right env.qtbl_name_and_index FStar_Pervasives_Native.fst)
in (FStar_Util.smap_copy uu____7373))
in (

let uu____7398 = (FStar_All.pipe_right env.qtbl_name_and_index FStar_Pervasives_Native.snd)
in ((uu____7370), (uu____7398))))
in (

let uu____7439 = (

let uu____7442 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_Util.mk_ref uu____7442))
in {solver = uu___93_7350.solver; range = uu___93_7350.range; curmodule = uu___93_7350.curmodule; gamma = uu___93_7350.gamma; gamma_cache = uu____7351; modules = uu___93_7350.modules; expected_typ = uu___93_7350.expected_typ; sigtab = uu____7354; is_pattern = uu___93_7350.is_pattern; instantiate_imp = uu___93_7350.instantiate_imp; effects = uu___93_7350.effects; generalize = uu___93_7350.generalize; letrecs = uu___93_7350.letrecs; top_level = uu___93_7350.top_level; check_uvars = uu___93_7350.check_uvars; use_eq = uu___93_7350.use_eq; is_iface = uu___93_7350.is_iface; admit = uu___93_7350.admit; lax = uu___93_7350.lax; lax_universes = uu___93_7350.lax_universes; failhard = uu___93_7350.failhard; nosynth = uu___93_7350.nosynth; tc_term = uu___93_7350.tc_term; type_of = uu___93_7350.type_of; universe_of = uu___93_7350.universe_of; check_type_of = uu___93_7350.check_type_of; use_bv_sorts = uu___93_7350.use_bv_sorts; qtbl_name_and_index = uu____7357; proof_ns = uu___93_7350.proof_ns; synth_hook = uu___93_7350.synth_hook; splice = uu___93_7350.splice; is_native_tactic = uu___93_7350.is_native_tactic; identifier_info = uu____7439; tc_hooks = uu___93_7350.tc_hooks; dsenv = uu___93_7350.dsenv; dep_graph = uu___93_7350.dep_graph})))));
))


let pop_stack : Prims.unit  ->  env = (fun uu____7540 -> (

let uu____7541 = (FStar_ST.op_Bang stack)
in (match (uu____7541) with
| (env)::tl1 -> begin
((FStar_ST.op_Colon_Equals stack tl1);
env;
)
end
| uu____7607 -> begin
(failwith "Impossible: Too many pops")
end)))


let push : env  ->  Prims.string  ->  env = (fun env msg -> ((push_query_indices ());
(env.solver.push msg);
(push_stack env);
))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> ((env.solver.pop msg);
(pop_query_indices ());
(pop_stack ());
))


let incr_query_index : env  ->  env = (fun env -> (

let qix = (peek_query_indices ())
in (match (env.qtbl_name_and_index) with
| (uu____7636, FStar_Pervasives_Native.None) -> begin
env
end
| (tbl, FStar_Pervasives_Native.Some (l, n1)) -> begin
(

let uu____7668 = (FStar_All.pipe_right qix (FStar_List.tryFind (fun uu____7694 -> (match (uu____7694) with
| (m, uu____7700) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____7668) with
| FStar_Pervasives_Native.None -> begin
(

let next = (n1 + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(FStar_Util.smap_add tbl l.FStar_Ident.str next);
(

let uu___94_7708 = env
in {solver = uu___94_7708.solver; range = uu___94_7708.range; curmodule = uu___94_7708.curmodule; gamma = uu___94_7708.gamma; gamma_cache = uu___94_7708.gamma_cache; modules = uu___94_7708.modules; expected_typ = uu___94_7708.expected_typ; sigtab = uu___94_7708.sigtab; is_pattern = uu___94_7708.is_pattern; instantiate_imp = uu___94_7708.instantiate_imp; effects = uu___94_7708.effects; generalize = uu___94_7708.generalize; letrecs = uu___94_7708.letrecs; top_level = uu___94_7708.top_level; check_uvars = uu___94_7708.check_uvars; use_eq = uu___94_7708.use_eq; is_iface = uu___94_7708.is_iface; admit = uu___94_7708.admit; lax = uu___94_7708.lax; lax_universes = uu___94_7708.lax_universes; failhard = uu___94_7708.failhard; nosynth = uu___94_7708.nosynth; tc_term = uu___94_7708.tc_term; type_of = uu___94_7708.type_of; universe_of = uu___94_7708.universe_of; check_type_of = uu___94_7708.check_type_of; use_bv_sorts = uu___94_7708.use_bv_sorts; qtbl_name_and_index = ((tbl), (FStar_Pervasives_Native.Some (((l), (next))))); proof_ns = uu___94_7708.proof_ns; synth_hook = uu___94_7708.synth_hook; splice = uu___94_7708.splice; is_native_tactic = uu___94_7708.is_native_tactic; identifier_info = uu___94_7708.identifier_info; tc_hooks = uu___94_7708.tc_hooks; dsenv = uu___94_7708.dsenv; dep_graph = uu___94_7708.dep_graph});
))
end
| FStar_Pervasives_Native.Some (uu____7721, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(FStar_Util.smap_add tbl l.FStar_Ident.str next);
(

let uu___95_7730 = env
in {solver = uu___95_7730.solver; range = uu___95_7730.range; curmodule = uu___95_7730.curmodule; gamma = uu___95_7730.gamma; gamma_cache = uu___95_7730.gamma_cache; modules = uu___95_7730.modules; expected_typ = uu___95_7730.expected_typ; sigtab = uu___95_7730.sigtab; is_pattern = uu___95_7730.is_pattern; instantiate_imp = uu___95_7730.instantiate_imp; effects = uu___95_7730.effects; generalize = uu___95_7730.generalize; letrecs = uu___95_7730.letrecs; top_level = uu___95_7730.top_level; check_uvars = uu___95_7730.check_uvars; use_eq = uu___95_7730.use_eq; is_iface = uu___95_7730.is_iface; admit = uu___95_7730.admit; lax = uu___95_7730.lax; lax_universes = uu___95_7730.lax_universes; failhard = uu___95_7730.failhard; nosynth = uu___95_7730.nosynth; tc_term = uu___95_7730.tc_term; type_of = uu___95_7730.type_of; universe_of = uu___95_7730.universe_of; check_type_of = uu___95_7730.check_type_of; use_bv_sorts = uu___95_7730.use_bv_sorts; qtbl_name_and_index = ((tbl), (FStar_Pervasives_Native.Some (((l), (next))))); proof_ns = uu___95_7730.proof_ns; synth_hook = uu___95_7730.synth_hook; splice = uu___95_7730.splice; is_native_tactic = uu___95_7730.is_native_tactic; identifier_info = uu___95_7730.identifier_info; tc_hooks = uu___95_7730.tc_hooks; dsenv = uu___95_7730.dsenv; dep_graph = uu___95_7730.dep_graph});
))
end))
end)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> (match ((Prims.op_Equality r FStar_Range.dummyRange)) with
| true -> begin
e
end
| uu____7755 -> begin
(

let uu___96_7756 = e
in {solver = uu___96_7756.solver; range = r; curmodule = uu___96_7756.curmodule; gamma = uu___96_7756.gamma; gamma_cache = uu___96_7756.gamma_cache; modules = uu___96_7756.modules; expected_typ = uu___96_7756.expected_typ; sigtab = uu___96_7756.sigtab; is_pattern = uu___96_7756.is_pattern; instantiate_imp = uu___96_7756.instantiate_imp; effects = uu___96_7756.effects; generalize = uu___96_7756.generalize; letrecs = uu___96_7756.letrecs; top_level = uu___96_7756.top_level; check_uvars = uu___96_7756.check_uvars; use_eq = uu___96_7756.use_eq; is_iface = uu___96_7756.is_iface; admit = uu___96_7756.admit; lax = uu___96_7756.lax; lax_universes = uu___96_7756.lax_universes; failhard = uu___96_7756.failhard; nosynth = uu___96_7756.nosynth; tc_term = uu___96_7756.tc_term; type_of = uu___96_7756.type_of; universe_of = uu___96_7756.universe_of; check_type_of = uu___96_7756.check_type_of; use_bv_sorts = uu___96_7756.use_bv_sorts; qtbl_name_and_index = uu___96_7756.qtbl_name_and_index; proof_ns = uu___96_7756.proof_ns; synth_hook = uu___96_7756.synth_hook; splice = uu___96_7756.splice; is_native_tactic = uu___96_7756.is_native_tactic; identifier_info = uu___96_7756.identifier_info; tc_hooks = uu___96_7756.tc_hooks; dsenv = uu___96_7756.dsenv; dep_graph = uu___96_7756.dep_graph})
end))


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let toggle_id_info : env  ->  Prims.bool  ->  Prims.unit = (fun env enabled -> (

let uu____7766 = (

let uu____7767 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_toggle uu____7767 enabled))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____7766)))


let insert_bv_info : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env bv ty -> (

let uu____7827 = (

let uu____7828 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_insert_bv uu____7828 bv ty))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____7827)))


let insert_fv_info : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env fv ty -> (

let uu____7888 = (

let uu____7889 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_insert_fv uu____7889 fv ty))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____7888)))


let promote_id_info : env  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  Prims.unit = (fun env ty_map -> (

let uu____7951 = (

let uu____7952 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_promote uu____7952 ty_map))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____7951)))


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let uu___97_8017 = env
in {solver = uu___97_8017.solver; range = uu___97_8017.range; curmodule = lid; gamma = uu___97_8017.gamma; gamma_cache = uu___97_8017.gamma_cache; modules = uu___97_8017.modules; expected_typ = uu___97_8017.expected_typ; sigtab = uu___97_8017.sigtab; is_pattern = uu___97_8017.is_pattern; instantiate_imp = uu___97_8017.instantiate_imp; effects = uu___97_8017.effects; generalize = uu___97_8017.generalize; letrecs = uu___97_8017.letrecs; top_level = uu___97_8017.top_level; check_uvars = uu___97_8017.check_uvars; use_eq = uu___97_8017.use_eq; is_iface = uu___97_8017.is_iface; admit = uu___97_8017.admit; lax = uu___97_8017.lax; lax_universes = uu___97_8017.lax_universes; failhard = uu___97_8017.failhard; nosynth = uu___97_8017.nosynth; tc_term = uu___97_8017.tc_term; type_of = uu___97_8017.type_of; universe_of = uu___97_8017.universe_of; check_type_of = uu___97_8017.check_type_of; use_bv_sorts = uu___97_8017.use_bv_sorts; qtbl_name_and_index = uu___97_8017.qtbl_name_and_index; proof_ns = uu___97_8017.proof_ns; synth_hook = uu___97_8017.synth_hook; splice = uu___97_8017.splice; is_native_tactic = uu___97_8017.is_native_tactic; identifier_info = uu___97_8017.identifier_info; tc_hooks = uu___97_8017.tc_hooks; dsenv = uu___97_8017.dsenv; dep_graph = uu___97_8017.dep_graph}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  (FStar_Errors.raw_error * Prims.string) = (fun l -> (

let uu____8043 = (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_NameNotFound), (uu____8043))))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  (FStar_Errors.raw_error * Prims.string) = (fun v1 -> (

let uu____8051 = (

let uu____8052 = (FStar_Syntax_Print.bv_to_string v1)
in (FStar_Util.format1 "Variable \"%s\" not found" uu____8052))
in ((FStar_Errors.Fatal_VariableNotFound), (uu____8051))))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun uu____8055 -> (

let uu____8056 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____8056)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), uu____8094) -> begin
(

let n1 = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n1 - i)), (u))))))
in (

let uu____8124 = (FStar_Syntax_Subst.subst vs t)
in ((us), (uu____8124)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun uu___75_8137 -> (match (uu___75_8137) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun uu____8161 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let uu____8174 = (inst_tscheme t)
in (match (uu____8174) with
| (us, t1) -> begin
(

let uu____8185 = (FStar_Syntax_Subst.set_use_range r t1)
in ((us), (uu____8185)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed uu____8197 -> (match (uu____8197) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs1 = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in ((match ((Prims.op_disEquality (FStar_List.length insts) (FStar_List.length univs1))) with
| true -> begin
(

let uu____8212 = (

let uu____8213 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (

let uu____8214 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (

let uu____8215 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____8216 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" uu____8213 uu____8214 uu____8215 uu____8216)))))
in (failwith uu____8212))
end
| uu____8217 -> begin
()
end);
(

let uu____8218 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (FStar_Pervasives_Native.snd uu____8218));
))
end
| uu____8225 -> begin
(

let uu____8226 = (

let uu____8227 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" uu____8227))
in (failwith uu____8226))
end)
end))

type tri =
| Yes
| No
| Maybe


let uu___is_Yes : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Yes -> begin
true
end
| uu____8231 -> begin
false
end))


let uu___is_No : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____8235 -> begin
false
end))


let uu___is_Maybe : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____8239 -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in (match ((Prims.op_Equality l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
Yes
end
| uu____8247 -> begin
(match ((FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur1 = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l1 -> (match (((c), (l1))) with
| ([], uu____8273) -> begin
Maybe
end
| (uu____8280, []) -> begin
No
end
| ((hd1)::tl1, (hd')::tl') when (Prims.op_Equality hd1.FStar_Ident.idText hd'.FStar_Ident.idText) -> begin
(aux tl1 tl')
end
| uu____8299 -> begin
No
end))
in (aux cur1 lns))))
end
| uu____8308 -> begin
No
end)
end)))


type qninfo =
(((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option)) FStar_Util.either * FStar_Range.range) FStar_Pervasives_Native.option


let lookup_qname : env  ->  FStar_Ident.lident  ->  qninfo = (fun env lid -> (

let cur_mod = (in_cur_mod env lid)
in (

let cache = (fun t -> ((FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t);
FStar_Pervasives_Native.Some (t);
))
in (

let found = (match ((Prims.op_disEquality cur_mod No)) with
| true -> begin
(

let uu____8384 = (FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)
in (match (uu____8384) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.find_map env.gamma (fun uu___76_8429 -> (match (uu___76_8429) with
| Binding_lid (l, t) -> begin
(match ((FStar_Ident.lid_equals lid l)) with
| true -> begin
(

let uu____8472 = (

let uu____8491 = (

let uu____8506 = (inst_tscheme t)
in FStar_Util.Inl (uu____8506))
in ((uu____8491), ((FStar_Ident.range_of_lid l))))
in FStar_Pervasives_Native.Some (uu____8472))
end
| uu____8553 -> begin
FStar_Pervasives_Native.None
end)
end
| Binding_sig (uu____8572, {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (ses, uu____8574); FStar_Syntax_Syntax.sigrng = uu____8575; FStar_Syntax_Syntax.sigquals = uu____8576; FStar_Syntax_Syntax.sigmeta = uu____8577; FStar_Syntax_Syntax.sigattrs = uu____8578}) -> begin
(FStar_Util.find_map ses (fun se -> (

let uu____8598 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____8598) with
| true -> begin
(cache ((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| uu____8629 -> begin
FStar_Pervasives_Native.None
end))))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____8644) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____8651 -> begin
(cache t)
end))
in (

let uu____8652 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____8652) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (l) -> begin
(maybe_cache ((FStar_Util.Inr (((s), (FStar_Pervasives_Native.None)))), ((FStar_Ident.range_of_lid l))))
end)))
end
| Binding_sig_inst (lids, s, us) -> begin
(

let uu____8727 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____8727) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (l) -> begin
FStar_Pervasives_Native.Some (((FStar_Util.Inr (((s), (FStar_Pervasives_Native.Some (us))))), ((FStar_Ident.range_of_lid l))))
end))
end
| uu____8813 -> begin
FStar_Pervasives_Native.None
end)))
end
| se -> begin
se
end))
end
| uu____8835 -> begin
FStar_Pervasives_Native.None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| uu____8872 -> begin
(

let uu____8873 = (find_in_sigtab env lid)
in (match (uu____8873) with
| FStar_Pervasives_Native.Some (se) -> begin
FStar_Pervasives_Native.Some (((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end)))))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____8952) -> begin
(add_sigelts env ses)
end
| uu____8961 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids);
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| uu____8975 -> begin
()
end);
))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) FStar_Pervasives_Native.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun uu___77_9002 -> (match (uu___77_9002) with
| Binding_var (id1) when (FStar_Syntax_Syntax.bv_eq id1 bv) -> begin
FStar_Pervasives_Native.Some (((id1.FStar_Syntax_Syntax.sort), (id1.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
end
| uu____9020 -> begin
FStar_Pervasives_Native.None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) * FStar_Range.range) FStar_Pervasives_Native.option = (fun us_opt se lid -> (

let inst_tscheme1 = (fun ts -> (match (us_opt) with
| FStar_Pervasives_Native.None -> begin
(inst_tscheme ts)
end
| FStar_Pervasives_Native.Some (us) -> begin
(inst_tscheme_with ts us)
end))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____9073, (lb)::[]), uu____9075) -> begin
(

let uu____9088 = (

let uu____9097 = (inst_tscheme1 ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____9106 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in ((uu____9097), (uu____9106))))
in FStar_Pervasives_Native.Some (uu____9088))
end
| FStar_Syntax_Syntax.Sig_let ((uu____9119, lbs), uu____9121) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____9157) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
(

let uu____9169 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____9169) with
| true -> begin
(

let uu____9180 = (

let uu____9189 = (inst_tscheme1 ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____9198 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____9189), (uu____9198))))
in FStar_Pervasives_Native.Some (uu____9180))
end
| uu____9211 -> begin
FStar_Pervasives_Native.None
end))
end)))
end
| uu____9220 -> begin
FStar_Pervasives_Native.None
end)))


let effect_signature : FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.sigelt  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) * FStar_Range.range) FStar_Pervasives_Native.option = (fun us_opt se -> (

let inst_tscheme1 = (fun ts -> (match (us_opt) with
| FStar_Pervasives_Native.None -> begin
(inst_tscheme ts)
end
| FStar_Pervasives_Native.Some (us) -> begin
(inst_tscheme_with ts us)
end))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____9273 = (

let uu____9282 = (

let uu____9287 = (

let uu____9288 = (

let uu____9291 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders uu____9291))
in ((ne.FStar_Syntax_Syntax.univs), (uu____9288)))
in (inst_tscheme1 uu____9287))
in ((uu____9282), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____9273))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, uu____9311, uu____9312) -> begin
(

let uu____9317 = (

let uu____9326 = (

let uu____9331 = (

let uu____9332 = (

let uu____9335 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders uu____9335))
in ((us), (uu____9332)))
in (inst_tscheme1 uu____9331))
in ((uu____9326), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____9317))
end
| uu____9352 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_lid_aux : FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option  ->  env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) * FStar_Range.range) FStar_Pervasives_Native.option = (fun us_opt env lid -> (

let inst_tscheme1 = (fun ts -> (match (us_opt) with
| FStar_Pervasives_Native.None -> begin
(inst_tscheme ts)
end
| FStar_Pervasives_Native.Some (us) -> begin
(inst_tscheme_with ts us)
end))
in (

let mapper = (fun uu____9430 -> (match (uu____9430) with
| (lr, rng) -> begin
(match (lr) with
| FStar_Util.Inl (t) -> begin
FStar_Pervasives_Native.Some (((t), (rng)))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____9526, uvs, t, uu____9529, uu____9530, uu____9531); FStar_Syntax_Syntax.sigrng = uu____9532; FStar_Syntax_Syntax.sigquals = uu____9533; FStar_Syntax_Syntax.sigmeta = uu____9534; FStar_Syntax_Syntax.sigattrs = uu____9535}, FStar_Pervasives_Native.None) -> begin
(

let uu____9556 = (

let uu____9565 = (inst_tscheme1 ((uvs), (t)))
in ((uu____9565), (rng)))
in FStar_Pervasives_Native.Some (uu____9556))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t); FStar_Syntax_Syntax.sigrng = uu____9585; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____9587; FStar_Syntax_Syntax.sigattrs = uu____9588}, FStar_Pervasives_Native.None) -> begin
(

let uu____9605 = (

let uu____9606 = (in_cur_mod env l)
in (Prims.op_Equality uu____9606 Yes))
in (match (uu____9605) with
| true -> begin
(

let uu____9617 = ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface)
in (match (uu____9617) with
| true -> begin
(

let uu____9630 = (

let uu____9639 = (inst_tscheme1 ((uvs), (t)))
in ((uu____9639), (rng)))
in FStar_Pervasives_Native.Some (uu____9630))
end
| uu____9656 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____9665 -> begin
(

let uu____9666 = (

let uu____9675 = (inst_tscheme1 ((uvs), (t)))
in ((uu____9675), (rng)))
in FStar_Pervasives_Native.Some (uu____9666))
end))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____9696, uu____9697); FStar_Syntax_Syntax.sigrng = uu____9698; FStar_Syntax_Syntax.sigquals = uu____9699; FStar_Syntax_Syntax.sigmeta = uu____9700; FStar_Syntax_Syntax.sigattrs = uu____9701}, FStar_Pervasives_Native.None) -> begin
(match (tps) with
| [] -> begin
(

let uu____9740 = (

let uu____9749 = (inst_tscheme1 ((uvs), (k)))
in ((uu____9749), (rng)))
in FStar_Pervasives_Native.Some (uu____9740))
end
| uu____9766 -> begin
(

let uu____9767 = (

let uu____9776 = (

let uu____9781 = (

let uu____9782 = (

let uu____9785 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____9785))
in ((uvs), (uu____9782)))
in (inst_tscheme1 uu____9781))
in ((uu____9776), (rng)))
in FStar_Pervasives_Native.Some (uu____9767))
end)
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____9806, uu____9807); FStar_Syntax_Syntax.sigrng = uu____9808; FStar_Syntax_Syntax.sigquals = uu____9809; FStar_Syntax_Syntax.sigmeta = uu____9810; FStar_Syntax_Syntax.sigattrs = uu____9811}, FStar_Pervasives_Native.Some (us)) -> begin
(match (tps) with
| [] -> begin
(

let uu____9851 = (

let uu____9860 = (inst_tscheme_with ((uvs), (k)) us)
in ((uu____9860), (rng)))
in FStar_Pervasives_Native.Some (uu____9851))
end
| uu____9877 -> begin
(

let uu____9878 = (

let uu____9887 = (

let uu____9892 = (

let uu____9893 = (

let uu____9896 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____9896))
in ((uvs), (uu____9893)))
in (inst_tscheme_with uu____9892 us))
in ((uu____9887), (rng)))
in FStar_Pervasives_Native.Some (uu____9878))
end)
end
| FStar_Util.Inr (se) -> begin
(

let uu____9930 = (match (se) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____9951); FStar_Syntax_Syntax.sigrng = uu____9952; FStar_Syntax_Syntax.sigquals = uu____9953; FStar_Syntax_Syntax.sigmeta = uu____9954; FStar_Syntax_Syntax.sigattrs = uu____9955}, FStar_Pervasives_Native.None) -> begin
(lookup_type_of_let us_opt (FStar_Pervasives_Native.fst se) lid)
end
| uu____9970 -> begin
(effect_signature us_opt (FStar_Pervasives_Native.fst se))
end)
in (FStar_All.pipe_right uu____9930 (FStar_Util.map_option (fun uu____10018 -> (match (uu____10018) with
| (us_t, rng1) -> begin
((us_t), (rng1))
end)))))
end)
end))
in (

let uu____10049 = (

let uu____10060 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____10060 mapper))
in (match (uu____10049) with
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
FStar_Pervasives_Native.Some (((((us), ((

let uu___98_10153 = t
in {FStar_Syntax_Syntax.n = uu___98_10153.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = uu___98_10153.FStar_Syntax_Syntax.vars})))), (r)))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____10178 = (lookup_qname env l)
in (match (uu____10178) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____10197) -> begin
true
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) = (fun env bv -> (

let bvr = (FStar_Syntax_Syntax.range_of_bv bv)
in (

let uu____10245 = (try_lookup_bv env bv)
in (match (uu____10245) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10260 = (variable_not_found bv)
in (FStar_Errors.raise_error uu____10260 bvr))
end
| FStar_Pervasives_Native.Some (t, r) -> begin
(

let uu____10275 = (FStar_Syntax_Subst.set_use_range bvr t)
in (

let uu____10276 = (

let uu____10277 = (FStar_Range.use_range bvr)
in (FStar_Range.set_use_range r uu____10277))
in ((uu____10275), (uu____10276))))
end))))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) FStar_Pervasives_Native.option = (fun env l -> (

let uu____10294 = (try_lookup_lid_aux FStar_Pervasives_Native.None env l)
in (match (uu____10294) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
(

let use_range1 = (FStar_Ident.range_of_lid l)
in (

let r1 = (

let uu____10360 = (FStar_Range.use_range use_range1)
in (FStar_Range.set_use_range r uu____10360))
in (

let uu____10361 = (

let uu____10370 = (

let uu____10375 = (FStar_Syntax_Subst.set_use_range use_range1 t)
in ((us), (uu____10375)))
in ((uu____10370), (r1)))
in FStar_Pervasives_Native.Some (uu____10361))))
end)))


let try_lookup_and_inst_lid : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) FStar_Pervasives_Native.option = (fun env us l -> (

let uu____10403 = (try_lookup_lid_aux (FStar_Pervasives_Native.Some (us)) env l)
in (match (uu____10403) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((uu____10436, t), r) -> begin
(

let use_range1 = (FStar_Ident.range_of_lid l)
in (

let r1 = (

let uu____10461 = (FStar_Range.use_range use_range1)
in (FStar_Range.set_use_range r uu____10461))
in (

let uu____10462 = (

let uu____10467 = (FStar_Syntax_Subst.set_use_range use_range1 t)
in ((uu____10467), (r1)))
in FStar_Pervasives_Native.Some (uu____10462))))
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) = (fun env l -> (

let uu____10486 = (try_lookup_lid env l)
in (match (uu____10486) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10513 = (name_not_found l)
in (FStar_Errors.raise_error uu____10513 (FStar_Ident.range_of_lid l)))
end
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end)))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun uu___78_10553 -> (match (uu___78_10553) with
| Binding_univ (y) -> begin
(Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)
end
| uu____10555 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env lid -> (

let uu____10570 = (lookup_qname env lid)
in (match (uu____10570) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____10579, uvs, t); FStar_Syntax_Syntax.sigrng = uu____10582; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____10584; FStar_Syntax_Syntax.sigattrs = uu____10585}, FStar_Pervasives_Native.None), uu____10586) -> begin
(

let uu____10635 = (

let uu____10646 = (

let uu____10651 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (uu____10651)))
in ((uu____10646), (q)))
in FStar_Pervasives_Native.Some (uu____10635))
end
| uu____10668 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____10685 = (lookup_qname env lid)
in (match (uu____10685) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____10690, uvs, t); FStar_Syntax_Syntax.sigrng = uu____10693; FStar_Syntax_Syntax.sigquals = uu____10694; FStar_Syntax_Syntax.sigmeta = uu____10695; FStar_Syntax_Syntax.sigattrs = uu____10696}, FStar_Pervasives_Native.None), uu____10697) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____10746 -> begin
(

let uu____10747 = (name_not_found lid)
in (FStar_Errors.raise_error uu____10747 (FStar_Ident.range_of_lid lid)))
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____10766 = (lookup_qname env lid)
in (match (uu____10766) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____10771, uvs, t, uu____10774, uu____10775, uu____10776); FStar_Syntax_Syntax.sigrng = uu____10777; FStar_Syntax_Syntax.sigquals = uu____10778; FStar_Syntax_Syntax.sigmeta = uu____10779; FStar_Syntax_Syntax.sigattrs = uu____10780}, FStar_Pervasives_Native.None), uu____10781) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____10834 -> begin
(

let uu____10835 = (name_not_found lid)
in (FStar_Errors.raise_error uu____10835 (FStar_Ident.range_of_lid lid)))
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  (Prims.bool * FStar_Ident.lident Prims.list) = (fun env lid -> (

let uu____10856 = (lookup_qname env lid)
in (match (uu____10856) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____10863, uu____10864, uu____10865, uu____10866, uu____10867, dcs); FStar_Syntax_Syntax.sigrng = uu____10869; FStar_Syntax_Syntax.sigquals = uu____10870; FStar_Syntax_Syntax.sigmeta = uu____10871; FStar_Syntax_Syntax.sigattrs = uu____10872}, uu____10873), uu____10874) -> begin
((true), (dcs))
end
| uu____10935 -> begin
((false), ([]))
end)))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____10944 = (lookup_qname env lid)
in (match (uu____10944) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____10945, uu____10946, uu____10947, l, uu____10949, uu____10950); FStar_Syntax_Syntax.sigrng = uu____10951; FStar_Syntax_Syntax.sigquals = uu____10952; FStar_Syntax_Syntax.sigmeta = uu____10953; FStar_Syntax_Syntax.sigattrs = uu____10954}, uu____10955), uu____10956) -> begin
l
end
| uu____11011 -> begin
(

let uu____11012 = (

let uu____11013 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" uu____11013))
in (failwith uu____11012))
end)))


let lookup_definition_qninfo : delta_level Prims.list  ->  FStar_Ident.lident  ->  qninfo  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun delta_levels lid qninfo -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____11054) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____11105, lbs), uu____11107) when (visible se.FStar_Syntax_Syntax.sigquals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____11135 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____11135) with
| true -> begin
FStar_Pervasives_Native.Some (((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbdef)))
end
| uu____11158 -> begin
FStar_Pervasives_Native.None
end)))))
end
| uu____11167 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____11172 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun delta_levels env lid -> (

let uu____11196 = (lookup_qname env lid)
in (FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid) uu____11196)))


let attrs_of_qninfo : qninfo  ->  FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option = (fun qninfo -> (match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, uu____11219), uu____11220) -> begin
FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
end
| uu____11269 -> begin
FStar_Pervasives_Native.None
end))


let lookup_attrs_of_lid : env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option = (fun env lid -> (

let uu____11286 = (lookup_qname env lid)
in (FStar_All.pipe_left attrs_of_qninfo uu____11286)))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env ftv -> (

let uu____11301 = (lookup_qname env ftv)
in (match (uu____11301) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____11305) -> begin
(

let uu____11350 = (effect_signature FStar_Pervasives_Native.None se)
in (match (uu____11350) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((uu____11371, t), r) -> begin
(

let uu____11386 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t)
in FStar_Pervasives_Native.Some (uu____11386))
end))
end
| uu____11387 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (

let uu____11394 = (try_lookup_effect_lid env ftv)
in (match (uu____11394) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11397 = (name_not_found ftv)
in (FStar_Errors.raise_error uu____11397 (FStar_Ident.range_of_lid ftv)))
end
| FStar_Pervasives_Native.Some (k) -> begin
k
end)))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun env univ_insts lid0 -> (

let uu____11418 = (lookup_qname env lid0)
in (match (uu____11418) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs1, binders, c, uu____11429); FStar_Syntax_Syntax.sigrng = uu____11430; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____11432; FStar_Syntax_Syntax.sigattrs = uu____11433}, FStar_Pervasives_Native.None), uu____11434) -> begin
(

let lid1 = (

let uu____11488 = (

let uu____11489 = (FStar_Range.use_range (FStar_Ident.range_of_lid lid0))
in (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) uu____11489))
in (FStar_Ident.set_lid_range lid uu____11488))
in (

let uu____11490 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___79_11494 -> (match (uu___79_11494) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____11495 -> begin
false
end))))
in (match (uu____11490) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____11506 -> begin
(

let insts = (match ((Prims.op_Equality (FStar_List.length univ_insts) (FStar_List.length univs1))) with
| true -> begin
univ_insts
end
| uu____11508 -> begin
(

let uu____11509 = (

let uu____11510 = (

let uu____11511 = (get_range env)
in (FStar_Range.string_of_range uu____11511))
in (

let uu____11512 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____11513 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format3 "(%s) Unexpected instantiation of effect %s with %s universes" uu____11510 uu____11512 uu____11513))))
in (failwith uu____11509))
end)
in (match (((binders), (univs1))) with
| ([], uu____11520) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (uu____11537, (uu____11538)::(uu____11539)::uu____11540) -> begin
(

let uu____11545 = (

let uu____11546 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____11547 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" uu____11546 uu____11547)))
in (failwith uu____11545))
end
| uu____11554 -> begin
(

let uu____11559 = (

let uu____11564 = (

let uu____11565 = (FStar_Syntax_Util.arrow binders c)
in ((univs1), (uu____11565)))
in (inst_tscheme_with uu____11564 insts))
in (match (uu____11559) with
| (uu____11576, t) -> begin
(

let t1 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid1) t)
in (

let uu____11579 = (

let uu____11580 = (FStar_Syntax_Subst.compress t1)
in uu____11580.FStar_Syntax_Syntax.n)
in (match (uu____11579) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
FStar_Pervasives_Native.Some (((binders1), (c1)))
end
| uu____11627 -> begin
(failwith "Impossible")
end)))
end))
end))
end)))
end
| uu____11634 -> begin
FStar_Pervasives_Native.None
end)))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find1 = (fun l1 -> (

let uu____11654 = (lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l1)
in (match (uu____11654) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____11667, c) -> begin
(

let l2 = (FStar_Syntax_Util.comp_effect_name c)
in (

let uu____11674 = (find1 l2)
in (match (uu____11674) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (l2)
end
| FStar_Pervasives_Native.Some (l') -> begin
FStar_Pervasives_Native.Some (l')
end)))
end)))
in (

let res = (

let uu____11681 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____11681) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____11685 = (find1 l)
in (match (uu____11685) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (m) -> begin
((FStar_Util.smap_add cache l.FStar_Ident.str m);
m;
)
end))
end))
in (FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l))))))


let lookup_effect_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env l -> (

let l1 = (norm_eff_name env l)
in (

let uu____11699 = (lookup_qname env l1)
in (match (uu____11699) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (uu____11702); FStar_Syntax_Syntax.sigrng = uu____11703; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____11705; FStar_Syntax_Syntax.sigattrs = uu____11706}, uu____11707), uu____11708) -> begin
q
end
| uu____11759 -> begin
[]
end))))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail1 = (fun uu____11772 -> (

let uu____11773 = (

let uu____11774 = (FStar_Util.string_of_int i)
in (

let uu____11775 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" uu____11774 uu____11775)))
in (failwith uu____11773)))
in (

let uu____11776 = (lookup_datacon env lid)
in (match (uu____11776) with
| (uu____11781, t) -> begin
(

let uu____11783 = (

let uu____11784 = (FStar_Syntax_Subst.compress t)
in uu____11784.FStar_Syntax_Syntax.n)
in (match (uu____11783) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____11788) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail1 ())
end
| uu____11809 -> begin
(

let b = (FStar_List.nth binders i)
in (

let uu____11819 = (FStar_Syntax_Util.mk_field_projector_name lid (FStar_Pervasives_Native.fst b) i)
in (FStar_All.pipe_right uu____11819 FStar_Pervasives_Native.fst)))
end)
end
| uu____11828 -> begin
(fail1 ())
end))
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____11835 = (lookup_qname env l)
in (match (uu____11835) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____11836, uu____11837, uu____11838); FStar_Syntax_Syntax.sigrng = uu____11839; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____11841; FStar_Syntax_Syntax.sigattrs = uu____11842}, uu____11843), uu____11844) -> begin
(FStar_Util.for_some (fun uu___80_11897 -> (match (uu___80_11897) with
| FStar_Syntax_Syntax.Projector (uu____11898) -> begin
true
end
| uu____11903 -> begin
false
end)) quals)
end
| uu____11904 -> begin
false
end)))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____11911 = (lookup_qname env lid)
in (match (uu____11911) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____11912, uu____11913, uu____11914, uu____11915, uu____11916, uu____11917); FStar_Syntax_Syntax.sigrng = uu____11918; FStar_Syntax_Syntax.sigquals = uu____11919; FStar_Syntax_Syntax.sigmeta = uu____11920; FStar_Syntax_Syntax.sigattrs = uu____11921}, uu____11922), uu____11923) -> begin
true
end
| uu____11978 -> begin
false
end)))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____11985 = (lookup_qname env lid)
in (match (uu____11985) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____11986, uu____11987, uu____11988, uu____11989, uu____11990, uu____11991); FStar_Syntax_Syntax.sigrng = uu____11992; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____11994; FStar_Syntax_Syntax.sigattrs = uu____11995}, uu____11996), uu____11997) -> begin
(FStar_Util.for_some (fun uu___81_12058 -> (match (uu___81_12058) with
| FStar_Syntax_Syntax.RecordType (uu____12059) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____12068) -> begin
true
end
| uu____12077 -> begin
false
end)) quals)
end
| uu____12078 -> begin
false
end)))


let qninfo_is_action : qninfo  ->  Prims.bool = (fun qninfo -> (match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____12082, uu____12083); FStar_Syntax_Syntax.sigrng = uu____12084; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____12086; FStar_Syntax_Syntax.sigattrs = uu____12087}, uu____12088), uu____12089) -> begin
(FStar_Util.for_some (fun uu___82_12146 -> (match (uu___82_12146) with
| FStar_Syntax_Syntax.Action (uu____12147) -> begin
true
end
| uu____12148 -> begin
false
end)) quals)
end
| uu____12149 -> begin
false
end))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____12156 = (lookup_qname env lid)
in (FStar_All.pipe_left qninfo_is_action uu____12156)))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (fun env head1 -> (

let uu____12166 = (

let uu____12167 = (FStar_Syntax_Util.un_uinst head1)
in uu____12167.FStar_Syntax_Syntax.n)
in (match (uu____12166) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(Prims.op_Equality fv.FStar_Syntax_Syntax.fv_delta FStar_Syntax_Syntax.Delta_equational)
end
| uu____12171 -> begin
false
end))))


let is_irreducible : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____12178 = (lookup_qname env l)
in (match (uu____12178) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, uu____12180), uu____12181) -> begin
(FStar_Util.for_some (fun uu___83_12229 -> (match (uu___83_12229) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____12230 -> begin
false
end)) se.FStar_Syntax_Syntax.sigquals)
end
| uu____12231 -> begin
false
end)))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun x -> (match ((FStar_Pervasives_Native.fst x)) with
| FStar_Util.Inl (uu____12296) -> begin
FStar_Pervasives_Native.Some (false)
end
| FStar_Util.Inr (se, uu____12312) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____12329) -> begin
FStar_Pervasives_Native.Some ((FStar_List.contains FStar_Syntax_Syntax.New se.FStar_Syntax_Syntax.sigquals))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____12336) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____12353 -> begin
FStar_Pervasives_Native.Some (false)
end)
end))
in (

let uu____12354 = (

let uu____12357 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____12357 mapper))
in (match (uu____12354) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
false
end))))


let num_inductive_ty_params : env  ->  FStar_Ident.lident  ->  Prims.int = (fun env lid -> (

let uu____12403 = (lookup_qname env lid)
in (match (uu____12403) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____12404, uu____12405, tps, uu____12407, uu____12408, uu____12409); FStar_Syntax_Syntax.sigrng = uu____12410; FStar_Syntax_Syntax.sigquals = uu____12411; FStar_Syntax_Syntax.sigmeta = uu____12412; FStar_Syntax_Syntax.sigattrs = uu____12413}, uu____12414), uu____12415) -> begin
(FStar_List.length tps)
end
| uu____12478 -> begin
(

let uu____12479 = (name_not_found lid)
in (FStar_Errors.raise_error uu____12479 (FStar_Ident.range_of_lid lid)))
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun uu____12523 -> (match (uu____12523) with
| (d, uu____12531) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)
end)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (

let uu____12542 = (effect_decl_opt env l)
in (match (uu____12542) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12557 = (name_not_found l)
in (FStar_Errors.raise_error uu____12557 (FStar_Ident.range_of_lid l)))
end
| FStar_Pervasives_Native.Some (md) -> begin
(FStar_Pervasives_Native.fst md)
end)))


let identity_mlift : mlift = {mlift_wp = (fun uu____12583 t wp -> wp); mlift_term = FStar_Pervasives_Native.Some ((fun uu____12598 t wp e -> (FStar_Util.return_all e)))}


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> (match ((FStar_Ident.lid_equals l1 l2)) with
| true -> begin
((l1), (identity_mlift), (identity_mlift))
end
| uu____12623 -> begin
(match ((((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid)))) with
| true -> begin
((FStar_Parser_Const.effect_GTot_lid), (identity_mlift), (identity_mlift))
end
| uu____12630 -> begin
(

let uu____12631 = (FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun uu____12684 -> (match (uu____12684) with
| (m1, m2, uu____12697, uu____12698, uu____12699) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))
in (match (uu____12631) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12716 = (

let uu____12721 = (

let uu____12722 = (FStar_Syntax_Print.lid_to_string l1)
in (

let uu____12723 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" uu____12722 uu____12723)))
in ((FStar_Errors.Fatal_EffectsCannotBeComposed), (uu____12721)))
in (FStar_Errors.raise_error uu____12716 env.range))
end
| FStar_Pervasives_Native.Some (uu____12730, uu____12731, m3, j1, j2) -> begin
((m3), (j1), (j2))
end))
end)
end))


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge FStar_Pervasives_Native.option = (fun env l1 l2 -> (match (((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)))) with
| true -> begin
FStar_Pervasives_Native.Some ({msource = l1; mtarget = l2; mlift = identity_mlift})
end
| uu____12758 -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end))


let wp_sig_aux : 'Auu____12768 . (FStar_Syntax_Syntax.eff_decl * 'Auu____12768) Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun decls m -> (

let uu____12795 = (FStar_All.pipe_right decls (FStar_Util.find_opt (fun uu____12821 -> (match (uu____12821) with
| (d, uu____12827) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)
end))))
in (match (uu____12795) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12838 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith uu____12838))
end
| FStar_Pervasives_Native.Some (md, _q) -> begin
(

let uu____12851 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (uu____12851) with
| (uu____12862, s) -> begin
(

let s1 = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s1.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, uu____12872))::((wp, uu____12874))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____12910 -> begin
(failwith "Impossible")
end))
end))
end)))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let null_wp_for_eff : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env eff_name res_u res_t -> (match ((FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' res_t (FStar_Pervasives_Native.Some (res_u)))
end
| uu____12945 -> begin
(match ((FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal' res_t (FStar_Pervasives_Native.Some (res_u)))
end
| uu____12946 -> begin
(

let eff_name1 = (norm_eff_name env eff_name)
in (

let ed = (get_effect_decl env eff_name1)
in (

let null_wp = (inst_effect_fun_with ((res_u)::[]) env ed ed.FStar_Syntax_Syntax.null_wp)
in (

let null_wp_res = (

let uu____12953 = (get_range env)
in (

let uu____12954 = (

let uu____12957 = (

let uu____12958 = (

let uu____12973 = (

let uu____12976 = (FStar_Syntax_Syntax.as_arg res_t)
in (uu____12976)::[])
in ((null_wp), (uu____12973)))
in FStar_Syntax_Syntax.Tm_app (uu____12958))
in (FStar_Syntax_Syntax.mk uu____12957))
in (uu____12954 FStar_Pervasives_Native.None uu____12953)))
in (

let uu____12982 = (

let uu____12983 = (

let uu____12992 = (FStar_Syntax_Syntax.as_arg null_wp_res)
in (uu____12992)::[])
in {FStar_Syntax_Syntax.comp_univs = (res_u)::[]; FStar_Syntax_Syntax.effect_name = eff_name1; FStar_Syntax_Syntax.result_typ = res_t; FStar_Syntax_Syntax.effect_args = uu____12983; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp uu____12982))))))
end)
end))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let effects = (

let uu___99_13001 = env.effects
in {decls = (((ne), (se.FStar_Syntax_Syntax.sigquals)))::env.effects.decls; order = uu___99_13001.order; joins = uu___99_13001.joins})
in (

let uu___100_13010 = env
in {solver = uu___100_13010.solver; range = uu___100_13010.range; curmodule = uu___100_13010.curmodule; gamma = uu___100_13010.gamma; gamma_cache = uu___100_13010.gamma_cache; modules = uu___100_13010.modules; expected_typ = uu___100_13010.expected_typ; sigtab = uu___100_13010.sigtab; is_pattern = uu___100_13010.is_pattern; instantiate_imp = uu___100_13010.instantiate_imp; effects = effects; generalize = uu___100_13010.generalize; letrecs = uu___100_13010.letrecs; top_level = uu___100_13010.top_level; check_uvars = uu___100_13010.check_uvars; use_eq = uu___100_13010.use_eq; is_iface = uu___100_13010.is_iface; admit = uu___100_13010.admit; lax = uu___100_13010.lax; lax_universes = uu___100_13010.lax_universes; failhard = uu___100_13010.failhard; nosynth = uu___100_13010.nosynth; tc_term = uu___100_13010.tc_term; type_of = uu___100_13010.type_of; universe_of = uu___100_13010.universe_of; check_type_of = uu___100_13010.check_type_of; use_bv_sorts = uu___100_13010.use_bv_sorts; qtbl_name_and_index = uu___100_13010.qtbl_name_and_index; proof_ns = uu___100_13010.proof_ns; synth_hook = uu___100_13010.synth_hook; splice = uu___100_13010.splice; is_native_tactic = uu___100_13010.is_native_tactic; identifier_info = uu___100_13010.identifier_info; tc_hooks = uu___100_13010.tc_hooks; dsenv = uu___100_13010.dsenv; dep_graph = uu___100_13010.dep_graph}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let compose_edges = (fun e1 e2 -> (

let composed_lift = (

let mlift_wp = (fun u r wp1 -> (

let uu____13030 = (e1.mlift.mlift_wp u r wp1)
in (e2.mlift.mlift_wp u r uu____13030)))
in (

let mlift_term = (match (((e1.mlift.mlift_term), (e2.mlift.mlift_term))) with
| (FStar_Pervasives_Native.Some (l1), FStar_Pervasives_Native.Some (l2)) -> begin
FStar_Pervasives_Native.Some ((fun u t wp e -> (

let uu____13144 = (e1.mlift.mlift_wp u t wp)
in (

let uu____13145 = (l1 u t wp e)
in (l2 u t uu____13144 uu____13145)))))
end
| uu____13146 -> begin
FStar_Pervasives_Native.None
end)
in {mlift_wp = mlift_wp; mlift_term = mlift_term}))
in {msource = e1.msource; mtarget = e2.mtarget; mlift = composed_lift}))
in (

let mk_mlift_wp = (fun lift_t u r wp1 -> (

let uu____13194 = (inst_tscheme_with lift_t ((u)::[]))
in (match (uu____13194) with
| (uu____13201, lift_t1) -> begin
(

let uu____13203 = (

let uu____13206 = (

let uu____13207 = (

let uu____13222 = (

let uu____13225 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____13226 = (

let uu____13229 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____13229)::[])
in (uu____13225)::uu____13226))
in ((lift_t1), (uu____13222)))
in FStar_Syntax_Syntax.Tm_app (uu____13207))
in (FStar_Syntax_Syntax.mk uu____13206))
in (uu____13203 FStar_Pervasives_Native.None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let sub_mlift_wp = (match (sub1.FStar_Syntax_Syntax.lift_wp) with
| FStar_Pervasives_Native.Some (sub_lift_wp) -> begin
(mk_mlift_wp sub_lift_wp)
end
| FStar_Pervasives_Native.None -> begin
(failwith "sub effect should\'ve been elaborated at this stage")
end)
in (

let mk_mlift_term = (fun lift_t u r wp1 e -> (

let uu____13279 = (inst_tscheme_with lift_t ((u)::[]))
in (match (uu____13279) with
| (uu____13286, lift_t1) -> begin
(

let uu____13288 = (

let uu____13291 = (

let uu____13292 = (

let uu____13307 = (

let uu____13310 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____13311 = (

let uu____13314 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____13315 = (

let uu____13318 = (FStar_Syntax_Syntax.as_arg e)
in (uu____13318)::[])
in (uu____13314)::uu____13315))
in (uu____13310)::uu____13311))
in ((lift_t1), (uu____13307)))
in FStar_Syntax_Syntax.Tm_app (uu____13292))
in (FStar_Syntax_Syntax.mk uu____13291))
in (uu____13288 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end)))
in (

let sub_mlift_term = (FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term)
in (

let edge = {msource = sub1.FStar_Syntax_Syntax.source; mtarget = sub1.FStar_Syntax_Syntax.target; mlift = {mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term}}
in (

let id_edge = (fun l -> {msource = sub1.FStar_Syntax_Syntax.source; mtarget = sub1.FStar_Syntax_Syntax.target; mlift = identity_mlift})
in (

let print_mlift = (fun l -> (

let bogus_term = (fun s -> (

let uu____13360 = (

let uu____13361 = (FStar_Ident.lid_of_path ((s)::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____13361 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.fv_to_tm uu____13360)))
in (

let arg = (bogus_term "ARG")
in (

let wp = (bogus_term "WP")
in (

let e = (bogus_term "COMP")
in (

let uu____13365 = (

let uu____13366 = (l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp)
in (FStar_Syntax_Print.term_to_string uu____13366))
in (

let uu____13367 = (

let uu____13368 = (FStar_Util.map_opt l.mlift_term (fun l1 -> (

let uu____13390 = (l1 FStar_Syntax_Syntax.U_zero arg wp e)
in (FStar_Syntax_Print.term_to_string uu____13390))))
in (FStar_Util.dflt "none" uu____13368))
in (FStar_Util.format2 "{ wp : %s ; term : %s }" uu____13365 uu____13367))))))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun uu____13416 -> (match (uu____13416) with
| (e, uu____13424) -> begin
e.FStar_Syntax_Syntax.mname
end))))
in (

let find_edge = (fun order1 uu____13443 -> (match (uu____13443) with
| (i, j) -> begin
(match ((FStar_Ident.lid_equals i j)) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _0_40 -> FStar_Pervasives_Native.Some (_0_40)))
end
| uu____13458 -> begin
(FStar_All.pipe_right order1 (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end)
end))
in (

let order1 = (

let fold_fun = (fun order1 k -> (

let uu____13481 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (match ((FStar_Ident.lid_equals i k)) with
| true -> begin
[]
end
| uu____13492 -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (match ((FStar_Ident.lid_equals j k)) with
| true -> begin
[]
end
| uu____13501 -> begin
(

let uu____13502 = (

let uu____13511 = (find_edge order1 ((i), (k)))
in (

let uu____13514 = (find_edge order1 ((k), (j)))
in ((uu____13511), (uu____13514))))
in (match (uu____13502) with
| (FStar_Pervasives_Native.Some (e1), FStar_Pervasives_Native.Some (e2)) -> begin
(

let uu____13529 = (compose_edges e1 e2)
in (uu____13529)::[])
end
| uu____13530 -> begin
[]
end))
end))))
end))))
in (FStar_List.append order1 uu____13481)))
in (FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)))
in (

let order2 = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order1)
in ((FStar_All.pipe_right order2 (FStar_List.iter (fun edge1 -> (

let uu____13560 = ((FStar_Ident.lid_equals edge1.msource FStar_Parser_Const.effect_DIV_lid) && (

let uu____13562 = (lookup_effect_quals env edge1.mtarget)
in (FStar_All.pipe_right uu____13562 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))))
in (match (uu____13560) with
| true -> begin
(

let uu____13567 = (

let uu____13572 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge1.mtarget.FStar_Ident.str)
in ((FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal), (uu____13572)))
in (

let uu____13573 = (get_range env)
in (FStar_Errors.raise_error uu____13567 uu____13573)))
end
| uu____13574 -> begin
()
end)))));
(

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (match ((FStar_Ident.lid_equals i j)) with
| true -> begin
FStar_Pervasives_Native.Some (((i), ((id_edge i)), ((id_edge i))))
end
| uu____13664 -> begin
(FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (

let uu____13698 = (

let uu____13707 = (find_edge order2 ((i), (k)))
in (

let uu____13710 = (find_edge order2 ((j), (k)))
in ((uu____13707), (uu____13710))))
in (match (uu____13698) with
| (FStar_Pervasives_Native.Some (ik), FStar_Pervasives_Native.Some (jk)) -> begin
(match (bopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((k), (ik), (jk)))
end
| FStar_Pervasives_Native.Some (ub, uu____13752, uu____13753) -> begin
(

let uu____13760 = (

let uu____13765 = (

let uu____13766 = (find_edge order2 ((k), (ub)))
in (FStar_Util.is_some uu____13766))
in (

let uu____13769 = (

let uu____13770 = (find_edge order2 ((ub), (k)))
in (FStar_Util.is_some uu____13770))
in ((uu____13765), (uu____13769))))
in (match (uu____13760) with
| (true, true) -> begin
(match ((FStar_Ident.lid_equals k ub)) with
| true -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Warning_UpperBoundCandidateAlreadyVisited), ("Looking multiple times at the same upper bound candidate")));
bopt;
)
end
| uu____13790 -> begin
(failwith "Found a cycle in the lattice")
end)
end
| (false, false) -> begin
bopt
end
| (true, false) -> begin
FStar_Pervasives_Native.Some (((k), (ik), (jk)))
end
| (false, true) -> begin
bopt
end))
end)
end
| uu____13805 -> begin
bopt
end))) FStar_Pervasives_Native.None))
end)
in (match (join_opt) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (k, e1, e2) -> begin
(((i), (j), (k), (e1.mlift), (e2.mlift)))::[]
end))))))))
in (

let effects = (

let uu___101_13878 = env.effects
in {decls = uu___101_13878.decls; order = order2; joins = joins})
in (

let uu___102_13879 = env
in {solver = uu___102_13879.solver; range = uu___102_13879.range; curmodule = uu___102_13879.curmodule; gamma = uu___102_13879.gamma; gamma_cache = uu___102_13879.gamma_cache; modules = uu___102_13879.modules; expected_typ = uu___102_13879.expected_typ; sigtab = uu___102_13879.sigtab; is_pattern = uu___102_13879.is_pattern; instantiate_imp = uu___102_13879.instantiate_imp; effects = effects; generalize = uu___102_13879.generalize; letrecs = uu___102_13879.letrecs; top_level = uu___102_13879.top_level; check_uvars = uu___102_13879.check_uvars; use_eq = uu___102_13879.use_eq; is_iface = uu___102_13879.is_iface; admit = uu___102_13879.admit; lax = uu___102_13879.lax; lax_universes = uu___102_13879.lax_universes; failhard = uu___102_13879.failhard; nosynth = uu___102_13879.nosynth; tc_term = uu___102_13879.tc_term; type_of = uu___102_13879.type_of; universe_of = uu___102_13879.universe_of; check_type_of = uu___102_13879.check_type_of; use_bv_sorts = uu___102_13879.use_bv_sorts; qtbl_name_and_index = uu___102_13879.qtbl_name_and_index; proof_ns = uu___102_13879.proof_ns; synth_hook = uu___102_13879.synth_hook; splice = uu___102_13879.splice; is_native_tactic = uu___102_13879.is_native_tactic; identifier_info = uu___102_13879.identifier_info; tc_hooks = uu___102_13879.tc_hooks; dsenv = uu___102_13879.dsenv; dep_graph = uu___102_13879.dep_graph})));
))))))))))))))
end
| uu____13880 -> begin
env
end))


let comp_to_comp_typ : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env c -> (

let c1 = (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.None) -> begin
(

let u = (env.universe_of env t)
in (FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some (u))))
end
| FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.None) -> begin
(

let u = (env.universe_of env t)
in (FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some (u))))
end
| uu____13904 -> begin
c
end)
in (FStar_Syntax_Util.comp_to_comp_typ c1)))


let rec unfold_effect_abbrev : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (comp_to_comp_typ env comp)
in (

let uu____13912 = (lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name)
in (match (uu____13912) with
| FStar_Pervasives_Native.None -> begin
c
end
| FStar_Pervasives_Native.Some (binders, cdef) -> begin
(

let uu____13929 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (uu____13929) with
| (binders1, cdef1) -> begin
((match ((Prims.op_disEquality (FStar_List.length binders1) ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))) with
| true -> begin
(

let uu____13947 = (

let uu____13952 = (

let uu____13953 = (FStar_Util.string_of_int (FStar_List.length binders1))
in (

let uu____13958 = (FStar_Util.string_of_int ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))
in (

let uu____13965 = (

let uu____13966 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Print.comp_to_string uu____13966))
in (FStar_Util.format3 "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s" uu____13953 uu____13958 uu____13965))))
in ((FStar_Errors.Fatal_ConstructorArgLengthMismatch), (uu____13952)))
in (FStar_Errors.raise_error uu____13947 comp.FStar_Syntax_Syntax.pos))
end
| uu____13967 -> begin
()
end);
(

let inst1 = (

let uu____13971 = (

let uu____13980 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (uu____13980)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun uu____13997 uu____13998 -> (match (((uu____13997), (uu____13998))) with
| ((x, uu____14020), (t, uu____14022)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders1 uu____13971))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst1 cdef1)
in (

let c2 = (

let uu____14041 = (

let uu___103_14042 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = uu___103_14042.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___103_14042.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___103_14042.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___103_14042.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right uu____14041 FStar_Syntax_Syntax.mk_Comp))
in (unfold_effect_abbrev env c2))));
)
end))
end))))


let effect_repr_aux : Prims.bool  ->  env  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun only_reifiable env c u_c -> (

let effect_name = (norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (

let uu____14064 = (effect_decl_opt env effect_name)
in (match (uu____14064) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____14097 = (only_reifiable && (

let uu____14099 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____14099))))
in (match (uu____14097) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____14108 -> begin
(match (ed.FStar_Syntax_Syntax.repr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| uu____14115 -> begin
(

let c1 = (unfold_effect_abbrev env c)
in (

let res_typ = c1.FStar_Syntax_Syntax.result_typ
in (

let wp = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (hd1)::uu____14134 -> begin
hd1
end
| [] -> begin
(

let name = (FStar_Ident.string_of_lid effect_name)
in (

let message = (

let uu____14163 = (FStar_Util.format1 "Not enough arguments for effect %s. " name)
in (Prims.strcat uu____14163 (Prims.strcat "This usually happens when you use a partially applied DM4F effect, " "like [TAC int] instead of [Tac int].")))
in (

let uu____14164 = (get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NotEnoughArgumentsForEffect), (message)) uu____14164))))
end)
in (

let repr = (inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____14174 = (

let uu____14177 = (get_range env)
in (

let uu____14178 = (

let uu____14181 = (

let uu____14182 = (

let uu____14197 = (

let uu____14200 = (FStar_Syntax_Syntax.as_arg res_typ)
in (uu____14200)::(wp)::[])
in ((repr), (uu____14197)))
in FStar_Syntax_Syntax.Tm_app (uu____14182))
in (FStar_Syntax_Syntax.mk uu____14181))
in (uu____14178 FStar_Pervasives_Native.None uu____14177)))
in FStar_Pervasives_Native.Some (uu____14174))))))
end)
end))
end))))


let effect_repr : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (

let uu____14246 = (

let uu____14251 = (

let uu____14252 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format1 "Effect %s cannot be reified" uu____14252))
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____14251)))
in (

let uu____14253 = (get_range env)
in (FStar_Errors.raise_error uu____14246 uu____14253))))
in (

let uu____14254 = (effect_repr_aux true env c u_c)
in (match (uu____14254) with
| FStar_Pervasives_Native.None -> begin
(no_reify (FStar_Syntax_Util.comp_effect_name c))
end
| FStar_Pervasives_Native.Some (tm) -> begin
tm
end))))


let is_reifiable_effect : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env effect_lid -> (

let quals = (lookup_effect_quals env effect_lid)
in (FStar_List.contains FStar_Syntax_Syntax.Reifiable quals)))


let is_reifiable : env  ->  FStar_Syntax_Syntax.residual_comp  ->  Prims.bool = (fun env c -> (is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect))


let is_reifiable_comp : env  ->  FStar_Syntax_Syntax.comp  ->  Prims.bool = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name)
end
| uu____14288 -> begin
false
end))


let is_reifiable_function : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____14295 = (

let uu____14296 = (FStar_Syntax_Subst.compress t)
in uu____14296.FStar_Syntax_Syntax.n)
in (match (uu____14295) with
| FStar_Syntax_Syntax.Tm_arrow (uu____14299, c) -> begin
(is_reifiable_comp env c)
end
| uu____14317 -> begin
false
end)))


let push_in_gamma : env  ->  binding  ->  env = (fun env s -> (

let rec push1 = (fun x rest -> (match (rest) with
| (Binding_sig (uu____14339))::uu____14340 -> begin
(x)::rest
end
| (Binding_sig_inst (uu____14349))::uu____14350 -> begin
(x)::rest
end
| [] -> begin
(x)::[]
end
| (local)::rest1 -> begin
(

let uu____14365 = (push1 x rest1)
in (local)::uu____14365)
end))
in ((env.tc_hooks.tc_push_in_gamma_hook env s);
(

let uu___104_14369 = env
in (

let uu____14370 = (push1 s env.gamma)
in {solver = uu___104_14369.solver; range = uu___104_14369.range; curmodule = uu___104_14369.curmodule; gamma = uu____14370; gamma_cache = uu___104_14369.gamma_cache; modules = uu___104_14369.modules; expected_typ = uu___104_14369.expected_typ; sigtab = uu___104_14369.sigtab; is_pattern = uu___104_14369.is_pattern; instantiate_imp = uu___104_14369.instantiate_imp; effects = uu___104_14369.effects; generalize = uu___104_14369.generalize; letrecs = uu___104_14369.letrecs; top_level = uu___104_14369.top_level; check_uvars = uu___104_14369.check_uvars; use_eq = uu___104_14369.use_eq; is_iface = uu___104_14369.is_iface; admit = uu___104_14369.admit; lax = uu___104_14369.lax; lax_universes = uu___104_14369.lax_universes; failhard = uu___104_14369.failhard; nosynth = uu___104_14369.nosynth; tc_term = uu___104_14369.tc_term; type_of = uu___104_14369.type_of; universe_of = uu___104_14369.universe_of; check_type_of = uu___104_14369.check_type_of; use_bv_sorts = uu___104_14369.use_bv_sorts; qtbl_name_and_index = uu___104_14369.qtbl_name_and_index; proof_ns = uu___104_14369.proof_ns; synth_hook = uu___104_14369.synth_hook; splice = uu___104_14369.splice; is_native_tactic = uu___104_14369.is_native_tactic; identifier_info = uu___104_14369.identifier_info; tc_hooks = uu___104_14369.tc_hooks; dsenv = uu___104_14369.dsenv; dep_graph = uu___104_14369.dep_graph}));
)))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env1 = (push_in_gamma env (Binding_sig ((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))))
in (build_lattice env1 s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env1 = (push_in_gamma env (Binding_sig_inst ((((FStar_Syntax_Util.lids_of_sigelt s)), (s), (us)))))
in (build_lattice env1 s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let uu___105_14400 = env
in {solver = uu___105_14400.solver; range = uu___105_14400.range; curmodule = uu___105_14400.curmodule; gamma = (b)::env.gamma; gamma_cache = uu___105_14400.gamma_cache; modules = uu___105_14400.modules; expected_typ = uu___105_14400.expected_typ; sigtab = uu___105_14400.sigtab; is_pattern = uu___105_14400.is_pattern; instantiate_imp = uu___105_14400.instantiate_imp; effects = uu___105_14400.effects; generalize = uu___105_14400.generalize; letrecs = uu___105_14400.letrecs; top_level = uu___105_14400.top_level; check_uvars = uu___105_14400.check_uvars; use_eq = uu___105_14400.use_eq; is_iface = uu___105_14400.is_iface; admit = uu___105_14400.admit; lax = uu___105_14400.lax; lax_universes = uu___105_14400.lax_universes; failhard = uu___105_14400.failhard; nosynth = uu___105_14400.nosynth; tc_term = uu___105_14400.tc_term; type_of = uu___105_14400.type_of; universe_of = uu___105_14400.universe_of; check_type_of = uu___105_14400.check_type_of; use_bv_sorts = uu___105_14400.use_bv_sorts; qtbl_name_and_index = uu___105_14400.qtbl_name_and_index; proof_ns = uu___105_14400.proof_ns; synth_hook = uu___105_14400.synth_hook; splice = uu___105_14400.splice; is_native_tactic = uu___105_14400.is_native_tactic; identifier_info = uu___105_14400.identifier_info; tc_hooks = uu___105_14400.tc_hooks; dsenv = uu___105_14400.dsenv; dep_graph = uu___105_14400.dep_graph}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let pop_bv : env  ->  (FStar_Syntax_Syntax.bv * env) FStar_Pervasives_Native.option = (fun env -> (match (env.gamma) with
| (Binding_var (x))::rest -> begin
FStar_Pervasives_Native.Some (((x), ((

let uu___106_14431 = env
in {solver = uu___106_14431.solver; range = uu___106_14431.range; curmodule = uu___106_14431.curmodule; gamma = rest; gamma_cache = uu___106_14431.gamma_cache; modules = uu___106_14431.modules; expected_typ = uu___106_14431.expected_typ; sigtab = uu___106_14431.sigtab; is_pattern = uu___106_14431.is_pattern; instantiate_imp = uu___106_14431.instantiate_imp; effects = uu___106_14431.effects; generalize = uu___106_14431.generalize; letrecs = uu___106_14431.letrecs; top_level = uu___106_14431.top_level; check_uvars = uu___106_14431.check_uvars; use_eq = uu___106_14431.use_eq; is_iface = uu___106_14431.is_iface; admit = uu___106_14431.admit; lax = uu___106_14431.lax; lax_universes = uu___106_14431.lax_universes; failhard = uu___106_14431.failhard; nosynth = uu___106_14431.nosynth; tc_term = uu___106_14431.tc_term; type_of = uu___106_14431.type_of; universe_of = uu___106_14431.universe_of; check_type_of = uu___106_14431.check_type_of; use_bv_sorts = uu___106_14431.use_bv_sorts; qtbl_name_and_index = uu___106_14431.qtbl_name_and_index; proof_ns = uu___106_14431.proof_ns; synth_hook = uu___106_14431.synth_hook; splice = uu___106_14431.splice; is_native_tactic = uu___106_14431.is_native_tactic; identifier_info = uu___106_14431.identifier_info; tc_hooks = uu___106_14431.tc_hooks; dsenv = uu___106_14431.dsenv; dep_graph = uu___106_14431.dep_graph}))))
end
| uu____14432 -> begin
FStar_Pervasives_Native.None
end))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env1 uu____14454 -> (match (uu____14454) with
| (x, uu____14460) -> begin
(push_bv env1 x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x1) -> begin
(

let x2 = (

let uu___107_14494 = x1
in {FStar_Syntax_Syntax.ppname = uu___107_14494.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___107_14494.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)})
in Binding_var (x2))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> ((add_sigelts env m.FStar_Syntax_Syntax.exports);
(

let uu___108_14524 = env
in {solver = uu___108_14524.solver; range = uu___108_14524.range; curmodule = uu___108_14524.curmodule; gamma = []; gamma_cache = uu___108_14524.gamma_cache; modules = (m)::env.modules; expected_typ = FStar_Pervasives_Native.None; sigtab = uu___108_14524.sigtab; is_pattern = uu___108_14524.is_pattern; instantiate_imp = uu___108_14524.instantiate_imp; effects = uu___108_14524.effects; generalize = uu___108_14524.generalize; letrecs = uu___108_14524.letrecs; top_level = uu___108_14524.top_level; check_uvars = uu___108_14524.check_uvars; use_eq = uu___108_14524.use_eq; is_iface = uu___108_14524.is_iface; admit = uu___108_14524.admit; lax = uu___108_14524.lax; lax_universes = uu___108_14524.lax_universes; failhard = uu___108_14524.failhard; nosynth = uu___108_14524.nosynth; tc_term = uu___108_14524.tc_term; type_of = uu___108_14524.type_of; universe_of = uu___108_14524.universe_of; check_type_of = uu___108_14524.check_type_of; use_bv_sorts = uu___108_14524.use_bv_sorts; qtbl_name_and_index = uu___108_14524.qtbl_name_and_index; proof_ns = uu___108_14524.proof_ns; synth_hook = uu___108_14524.synth_hook; splice = uu___108_14524.splice; is_native_tactic = uu___108_14524.is_native_tactic; identifier_info = uu___108_14524.identifier_info; tc_hooks = uu___108_14524.tc_hooks; dsenv = uu___108_14524.dsenv; dep_graph = uu___108_14524.dep_graph});
))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env1 x -> (push_local_binding env1 (Binding_univ (x)))) env xs))


let open_universes_in : env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term Prims.list  ->  (env * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term Prims.list) = (fun env uvs terms -> (

let uu____14556 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____14556) with
| (univ_subst, univ_vars) -> begin
(

let env' = (push_univ_vars env univ_vars)
in (

let uu____14584 = (FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms)
in ((env'), (univ_vars), (uu____14584))))
end)))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let uu___109_14597 = env
in {solver = uu___109_14597.solver; range = uu___109_14597.range; curmodule = uu___109_14597.curmodule; gamma = uu___109_14597.gamma; gamma_cache = uu___109_14597.gamma_cache; modules = uu___109_14597.modules; expected_typ = FStar_Pervasives_Native.Some (t); sigtab = uu___109_14597.sigtab; is_pattern = uu___109_14597.is_pattern; instantiate_imp = uu___109_14597.instantiate_imp; effects = uu___109_14597.effects; generalize = uu___109_14597.generalize; letrecs = uu___109_14597.letrecs; top_level = uu___109_14597.top_level; check_uvars = uu___109_14597.check_uvars; use_eq = false; is_iface = uu___109_14597.is_iface; admit = uu___109_14597.admit; lax = uu___109_14597.lax; lax_universes = uu___109_14597.lax_universes; failhard = uu___109_14597.failhard; nosynth = uu___109_14597.nosynth; tc_term = uu___109_14597.tc_term; type_of = uu___109_14597.type_of; universe_of = uu___109_14597.universe_of; check_type_of = uu___109_14597.check_type_of; use_bv_sorts = uu___109_14597.use_bv_sorts; qtbl_name_and_index = uu___109_14597.qtbl_name_and_index; proof_ns = uu___109_14597.proof_ns; synth_hook = uu___109_14597.synth_hook; splice = uu___109_14597.splice; is_native_tactic = uu___109_14597.is_native_tactic; identifier_info = uu___109_14597.identifier_info; tc_hooks = uu___109_14597.tc_hooks; dsenv = uu___109_14597.dsenv; dep_graph = uu___109_14597.dep_graph}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun env -> (match (env.expected_typ) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) = (fun env_ -> (

let uu____14621 = (expected_typ env_)
in (((

let uu___110_14627 = env_
in {solver = uu___110_14627.solver; range = uu___110_14627.range; curmodule = uu___110_14627.curmodule; gamma = uu___110_14627.gamma; gamma_cache = uu___110_14627.gamma_cache; modules = uu___110_14627.modules; expected_typ = FStar_Pervasives_Native.None; sigtab = uu___110_14627.sigtab; is_pattern = uu___110_14627.is_pattern; instantiate_imp = uu___110_14627.instantiate_imp; effects = uu___110_14627.effects; generalize = uu___110_14627.generalize; letrecs = uu___110_14627.letrecs; top_level = uu___110_14627.top_level; check_uvars = uu___110_14627.check_uvars; use_eq = false; is_iface = uu___110_14627.is_iface; admit = uu___110_14627.admit; lax = uu___110_14627.lax; lax_universes = uu___110_14627.lax_universes; failhard = uu___110_14627.failhard; nosynth = uu___110_14627.nosynth; tc_term = uu___110_14627.tc_term; type_of = uu___110_14627.type_of; universe_of = uu___110_14627.universe_of; check_type_of = uu___110_14627.check_type_of; use_bv_sorts = uu___110_14627.use_bv_sorts; qtbl_name_and_index = uu___110_14627.qtbl_name_and_index; proof_ns = uu___110_14627.proof_ns; synth_hook = uu___110_14627.synth_hook; splice = uu___110_14627.splice; is_native_tactic = uu___110_14627.is_native_tactic; identifier_info = uu___110_14627.identifier_info; tc_hooks = uu___110_14627.tc_hooks; dsenv = uu___110_14627.dsenv; dep_graph = uu___110_14627.dep_graph})), (uu____14621))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = (match ((FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Parser_Const.prims_lid)) with
| true -> begin
(

let uu____14640 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun uu___84_14650 -> (match (uu___84_14650) with
| Binding_sig (uu____14653, se) -> begin
(se)::[]
end
| uu____14659 -> begin
[]
end))))
in (FStar_All.pipe_right uu____14640 FStar_List.rev))
end
| uu____14664 -> begin
m.FStar_Syntax_Syntax.exports
end)
in ((add_sigelts env sigs);
(

let uu___111_14666 = env
in {solver = uu___111_14666.solver; range = uu___111_14666.range; curmodule = empty_lid; gamma = []; gamma_cache = uu___111_14666.gamma_cache; modules = (m)::env.modules; expected_typ = uu___111_14666.expected_typ; sigtab = uu___111_14666.sigtab; is_pattern = uu___111_14666.is_pattern; instantiate_imp = uu___111_14666.instantiate_imp; effects = uu___111_14666.effects; generalize = uu___111_14666.generalize; letrecs = uu___111_14666.letrecs; top_level = uu___111_14666.top_level; check_uvars = uu___111_14666.check_uvars; use_eq = uu___111_14666.use_eq; is_iface = uu___111_14666.is_iface; admit = uu___111_14666.admit; lax = uu___111_14666.lax; lax_universes = uu___111_14666.lax_universes; failhard = uu___111_14666.failhard; nosynth = uu___111_14666.nosynth; tc_term = uu___111_14666.tc_term; type_of = uu___111_14666.type_of; universe_of = uu___111_14666.universe_of; check_type_of = uu___111_14666.check_type_of; use_bv_sorts = uu___111_14666.use_bv_sorts; qtbl_name_and_index = uu___111_14666.qtbl_name_and_index; proof_ns = uu___111_14666.proof_ns; synth_hook = uu___111_14666.synth_hook; splice = uu___111_14666.splice; is_native_tactic = uu___111_14666.is_native_tactic; identifier_info = uu___111_14666.identifier_info; tc_hooks = uu___111_14666.tc_hooks; dsenv = uu___111_14666.dsenv; dep_graph = uu___111_14666.dep_graph});
))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Free.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (uu____14747))::tl1 -> begin
(aux out tl1)
end
| (Binding_lid (uu____14751, (uu____14752, t)))::tl1 -> begin
(

let uu____14767 = (

let uu____14774 = (FStar_Syntax_Free.uvars t)
in (ext out uu____14774))
in (aux uu____14767 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____14781; FStar_Syntax_Syntax.index = uu____14782; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____14789 = (

let uu____14796 = (FStar_Syntax_Free.uvars t)
in (ext out uu____14796))
in (aux uu____14789 tl1))
end
| (Binding_sig (uu____14803))::uu____14804 -> begin
out
end
| (Binding_sig_inst (uu____14813))::uu____14814 -> begin
out
end))
in (aux no_uvs env.gamma)))))


let univ_vars : env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun env -> (

let no_univs = (FStar_Syntax_Free.new_universe_uvar_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (uu____14869))::tl1 -> begin
(aux out tl1)
end
| (Binding_univ (uu____14881))::tl1 -> begin
(aux out tl1)
end
| (Binding_lid (uu____14885, (uu____14886, t)))::tl1 -> begin
(

let uu____14901 = (

let uu____14904 = (FStar_Syntax_Free.univs t)
in (ext out uu____14904))
in (aux uu____14901 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____14907; FStar_Syntax_Syntax.index = uu____14908; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____14915 = (

let uu____14918 = (FStar_Syntax_Free.univs t)
in (ext out uu____14918))
in (aux uu____14915 tl1))
end
| (Binding_sig (uu____14921))::uu____14922 -> begin
out
end))
in (aux no_univs env.gamma)))))


let univnames : env  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun env -> (

let no_univ_names = FStar_Syntax_Syntax.no_universe_names
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (uu____14975))::tl1 -> begin
(aux out tl1)
end
| (Binding_univ (uname))::tl1 -> begin
(

let uu____14991 = (FStar_Util.set_add uname out)
in (aux uu____14991 tl1))
end
| (Binding_lid (uu____14994, (uu____14995, t)))::tl1 -> begin
(

let uu____15010 = (

let uu____15013 = (FStar_Syntax_Free.univnames t)
in (ext out uu____15013))
in (aux uu____15010 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____15016; FStar_Syntax_Syntax.index = uu____15017; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____15024 = (

let uu____15027 = (FStar_Syntax_Free.univnames t)
in (ext out uu____15027))
in (aux uu____15024 tl1))
end
| (Binding_sig (uu____15030))::uu____15031 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu___85_15055 -> (match (uu___85_15055) with
| Binding_var (x) -> begin
(x)::[]
end
| Binding_lid (uu____15059) -> begin
[]
end
| Binding_sig (uu____15064) -> begin
[]
end
| Binding_univ (uu____15071) -> begin
[]
end
| Binding_sig_inst (uu____15072) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____15088 = (

let uu____15091 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right uu____15091 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right uu____15088 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let print_gamma : env  ->  Prims.unit = (fun env -> (

let uu____15113 = (

let uu____15114 = (FStar_All.pipe_right env.gamma (FStar_List.map (fun uu___86_15124 -> (match (uu___86_15124) with
| Binding_var (x) -> begin
(

let uu____15126 = (FStar_Syntax_Print.bv_to_string x)
in (Prims.strcat "Binding_var " uu____15126))
end
| Binding_univ (u) -> begin
(Prims.strcat "Binding_univ " u.FStar_Ident.idText)
end
| Binding_lid (l, uu____15129) -> begin
(

let uu____15130 = (FStar_Ident.string_of_lid l)
in (Prims.strcat "Binding_lid " uu____15130))
end
| Binding_sig (ls, uu____15132) -> begin
(

let uu____15137 = (

let uu____15138 = (FStar_All.pipe_right ls (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____15138 (FStar_String.concat ", ")))
in (Prims.strcat "Binding_sig " uu____15137))
end
| Binding_sig_inst (ls, uu____15148, uu____15149) -> begin
(

let uu____15154 = (

let uu____15155 = (FStar_All.pipe_right ls (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____15155 (FStar_String.concat ", ")))
in (Prims.strcat "Binding_sig_inst " uu____15154))
end))))
in (FStar_All.pipe_right uu____15114 (FStar_String.concat "::\n")))
in (FStar_All.pipe_right uu____15113 (FStar_Util.print1 "%s\n"))))


let eq_gamma : env  ->  env  ->  Prims.bool = (fun env env' -> (

let uu____15172 = (FStar_Util.physical_equality env.gamma env'.gamma)
in (match (uu____15172) with
| true -> begin
true
end
| uu____15175 -> begin
(

let g = (all_binders env)
in (

let g' = (all_binders env')
in ((Prims.op_Equality (FStar_List.length g) (FStar_List.length g')) && (FStar_List.forall2 (fun uu____15200 uu____15201 -> (match (((uu____15200), (uu____15201))) with
| ((b1, uu____15219), (b2, uu____15221)) -> begin
(FStar_Syntax_Syntax.bv_eq b1 b2)
end)) g g'))))
end)))


let fold_env : 'a . env  ->  ('a  ->  binding  ->  'a)  ->  'a  ->  'a = (fun env f a -> (FStar_List.fold_right (fun e a1 -> (f a1 e)) env.gamma a))


let string_of_delta_level : delta_level  ->  Prims.string = (fun uu___87_15263 -> (match (uu___87_15263) with
| NoDelta -> begin
"NoDelta"
end
| Inlining -> begin
"Inlining"
end
| Eager_unfolding_only -> begin
"Eager_unfolding_only"
end
| Unfold (uu____15264) -> begin
"Unfold _"
end
| UnfoldTac -> begin
"UnfoldTac"
end))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys uu___88_15282 -> (match (uu___88_15282) with
| Binding_sig (lids, uu____15288) -> begin
(FStar_List.append lids keys)
end
| uu____15293 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun uu____15299 v1 keys1 -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)) keys)))


let should_enc_path : env  ->  Prims.string Prims.list  ->  Prims.bool = (fun env path -> (

let rec list_prefix = (fun xs ys -> (match (((xs), (ys))) with
| ([], uu____15333) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((Prims.op_Equality x y) && (list_prefix xs1 ys1))
end
| (uu____15352, uu____15353) -> begin
false
end))
in (

let uu____15362 = (FStar_List.tryFind (fun uu____15380 -> (match (uu____15380) with
| (p, uu____15388) -> begin
(list_prefix p path)
end)) env.proof_ns)
in (match (uu____15362) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____15399, b) -> begin
b
end))))


let should_enc_lid : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____15417 = (FStar_Ident.path_of_lid lid)
in (should_enc_path env uu____15417)))


let cons_proof_ns : Prims.bool  ->  env  ->  name_prefix  ->  env = (fun b e path -> (

let uu___112_15429 = e
in {solver = uu___112_15429.solver; range = uu___112_15429.range; curmodule = uu___112_15429.curmodule; gamma = uu___112_15429.gamma; gamma_cache = uu___112_15429.gamma_cache; modules = uu___112_15429.modules; expected_typ = uu___112_15429.expected_typ; sigtab = uu___112_15429.sigtab; is_pattern = uu___112_15429.is_pattern; instantiate_imp = uu___112_15429.instantiate_imp; effects = uu___112_15429.effects; generalize = uu___112_15429.generalize; letrecs = uu___112_15429.letrecs; top_level = uu___112_15429.top_level; check_uvars = uu___112_15429.check_uvars; use_eq = uu___112_15429.use_eq; is_iface = uu___112_15429.is_iface; admit = uu___112_15429.admit; lax = uu___112_15429.lax; lax_universes = uu___112_15429.lax_universes; failhard = uu___112_15429.failhard; nosynth = uu___112_15429.nosynth; tc_term = uu___112_15429.tc_term; type_of = uu___112_15429.type_of; universe_of = uu___112_15429.universe_of; check_type_of = uu___112_15429.check_type_of; use_bv_sorts = uu___112_15429.use_bv_sorts; qtbl_name_and_index = uu___112_15429.qtbl_name_and_index; proof_ns = (((path), (b)))::e.proof_ns; synth_hook = uu___112_15429.synth_hook; splice = uu___112_15429.splice; is_native_tactic = uu___112_15429.is_native_tactic; identifier_info = uu___112_15429.identifier_info; tc_hooks = uu___112_15429.tc_hooks; dsenv = uu___112_15429.dsenv; dep_graph = uu___112_15429.dep_graph}))


let add_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns true e path))


let rem_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns false e path))


let get_proof_ns : env  ->  proof_namespace = (fun e -> e.proof_ns)


let set_proof_ns : proof_namespace  ->  env  ->  env = (fun ns e -> (

let uu___113_15455 = e
in {solver = uu___113_15455.solver; range = uu___113_15455.range; curmodule = uu___113_15455.curmodule; gamma = uu___113_15455.gamma; gamma_cache = uu___113_15455.gamma_cache; modules = uu___113_15455.modules; expected_typ = uu___113_15455.expected_typ; sigtab = uu___113_15455.sigtab; is_pattern = uu___113_15455.is_pattern; instantiate_imp = uu___113_15455.instantiate_imp; effects = uu___113_15455.effects; generalize = uu___113_15455.generalize; letrecs = uu___113_15455.letrecs; top_level = uu___113_15455.top_level; check_uvars = uu___113_15455.check_uvars; use_eq = uu___113_15455.use_eq; is_iface = uu___113_15455.is_iface; admit = uu___113_15455.admit; lax = uu___113_15455.lax; lax_universes = uu___113_15455.lax_universes; failhard = uu___113_15455.failhard; nosynth = uu___113_15455.nosynth; tc_term = uu___113_15455.tc_term; type_of = uu___113_15455.type_of; universe_of = uu___113_15455.universe_of; check_type_of = uu___113_15455.check_type_of; use_bv_sorts = uu___113_15455.use_bv_sorts; qtbl_name_and_index = uu___113_15455.qtbl_name_and_index; proof_ns = ns; synth_hook = uu___113_15455.synth_hook; splice = uu___113_15455.splice; is_native_tactic = uu___113_15455.is_native_tactic; identifier_info = uu___113_15455.identifier_info; tc_hooks = uu___113_15455.tc_hooks; dsenv = uu___113_15455.dsenv; dep_graph = uu___113_15455.dep_graph}))


let unbound_vars : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun e t -> (

let uu____15466 = (FStar_Syntax_Free.names t)
in (

let uu____15469 = (bound_vars e)
in (FStar_List.fold_left (fun s bv -> (FStar_Util.set_remove bv s)) uu____15466 uu____15469))))


let closed : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e t -> (

let uu____15486 = (unbound_vars e t)
in (FStar_Util.set_is_empty uu____15486)))


let closed' : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____15492 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_is_empty uu____15492)))


let string_of_proof_ns : env  ->  Prims.string = (fun env -> (

let aux = (fun uu____15507 -> (match (uu____15507) with
| (p, b) -> begin
(match (((Prims.op_Equality p []) && b)) with
| true -> begin
"*"
end
| uu____15522 -> begin
(

let uu____15523 = (FStar_Ident.text_of_path p)
in (Prims.strcat (match (b) with
| true -> begin
"+"
end
| uu____15524 -> begin
"-"
end) uu____15523))
end)
end))
in (

let uu____15525 = (

let uu____15528 = (FStar_List.map aux env.proof_ns)
in (FStar_All.pipe_right uu____15528 FStar_List.rev))
in (FStar_All.pipe_right uu____15525 (FStar_String.concat " ")))))


let dummy_solver : solver_t = {init = (fun uu____15545 -> ()); push = (fun uu____15547 -> ()); pop = (fun uu____15549 -> ()); encode_modul = (fun uu____15552 uu____15553 -> ()); encode_sig = (fun uu____15556 uu____15557 -> ()); preprocess = (fun e g -> (

let uu____15563 = (

let uu____15570 = (FStar_Options.peek ())
in ((e), (g), (uu____15570)))
in (uu____15563)::[])); solve = (fun uu____15586 uu____15587 uu____15588 -> ()); finish = (fun uu____15594 -> ()); refresh = (fun uu____15596 -> ())}


let mk_copy : env  ->  env = (fun en -> (

let uu___114_15600 = en
in (

let uu____15601 = (FStar_Util.smap_copy en.gamma_cache)
in (

let uu____15604 = (FStar_Util.smap_copy en.sigtab)
in (

let uu____15607 = (FStar_Syntax_DsEnv.mk_copy en.dsenv)
in {solver = uu___114_15600.solver; range = uu___114_15600.range; curmodule = uu___114_15600.curmodule; gamma = uu___114_15600.gamma; gamma_cache = uu____15601; modules = uu___114_15600.modules; expected_typ = uu___114_15600.expected_typ; sigtab = uu____15604; is_pattern = uu___114_15600.is_pattern; instantiate_imp = uu___114_15600.instantiate_imp; effects = uu___114_15600.effects; generalize = uu___114_15600.generalize; letrecs = uu___114_15600.letrecs; top_level = uu___114_15600.top_level; check_uvars = uu___114_15600.check_uvars; use_eq = uu___114_15600.use_eq; is_iface = uu___114_15600.is_iface; admit = uu___114_15600.admit; lax = uu___114_15600.lax; lax_universes = uu___114_15600.lax_universes; failhard = uu___114_15600.failhard; nosynth = uu___114_15600.nosynth; tc_term = uu___114_15600.tc_term; type_of = uu___114_15600.type_of; universe_of = uu___114_15600.universe_of; check_type_of = uu___114_15600.check_type_of; use_bv_sorts = uu___114_15600.use_bv_sorts; qtbl_name_and_index = uu___114_15600.qtbl_name_and_index; proof_ns = uu___114_15600.proof_ns; synth_hook = uu___114_15600.synth_hook; splice = uu___114_15600.splice; is_native_tactic = uu___114_15600.is_native_tactic; identifier_info = uu___114_15600.identifier_info; tc_hooks = uu___114_15600.tc_hooks; dsenv = uu____15607; dep_graph = uu___114_15600.dep_graph})))))





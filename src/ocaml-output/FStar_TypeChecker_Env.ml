
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
| uu____44 -> begin
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
| uu____62 -> begin
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
| uu____94 -> begin
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
| uu____126 -> begin
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
| uu____148 -> begin
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
| uu____189 -> begin
false
end))


let uu___is_Inlining : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____194 -> begin
false
end))


let uu___is_Eager_unfolding_only : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding_only -> begin
true
end
| uu____199 -> begin
false
end))


let uu___is_Unfold : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unfold (_0) -> begin
true
end
| uu____205 -> begin
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
| uu____218 -> begin
false
end))

type mlift =
{mlift_wp : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ; mlift_term : (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option}


let __proj__Mkmlift__item__mlift_wp : mlift  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| {mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term} -> begin
__fname__mlift_wp
end))


let __proj__Mkmlift__item__mlift_term : mlift  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
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


type flat_proof_namespace =
(name_prefix * Prims.bool) Prims.list


type proof_namespace =
flat_proof_namespace Prims.list


type cached_elt =
(((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option)) FStar_Util.either * FStar_Range.range)


type goal =
FStar_Syntax_Syntax.term

type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; lax : Prims.bool; lax_universes : Prims.bool; failhard : Prims.bool; nosynth : Prims.bool; tc_term : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t); type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool; qname_and_index : (FStar_Ident.lident * Prims.int) FStar_Pervasives_Native.option; proof_ns : proof_namespace; synth : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term; is_native_tactic : FStar_Ident.lid  ->  Prims.bool; identifier_info : FStar_TypeChecker_Common.id_info_table FStar_ST.ref; tc_hooks : tcenv_hooks; dsenv : FStar_ToSyntax_Env.env} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; preprocess : env  ->  goal  ->  (env * goal * FStar_Options.optionstate) Prims.list; solve : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : (FStar_Syntax_Syntax.universe Prims.list * FStar_TypeChecker_Common.univ_ineq Prims.list); implicits : (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list} 
 and tcenv_hooks =
{tc_push_in_gamma_hook : env  ->  binding  ->  Prims.unit}


let __proj__Mkenv__item__solver : env  ->  solver_t = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__solver
end))


let __proj__Mkenv__item__range : env  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__range
end))


let __proj__Mkenv__item__curmodule : env  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__curmodule
end))


let __proj__Mkenv__item__gamma : env  ->  binding Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__gamma
end))


let __proj__Mkenv__item__gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__gamma_cache
end))


let __proj__Mkenv__item__modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__modules
end))


let __proj__Mkenv__item__expected_typ : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__expected_typ
end))


let __proj__Mkenv__item__sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__sigtab
end))


let __proj__Mkenv__item__is_pattern : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__is_pattern
end))


let __proj__Mkenv__item__instantiate_imp : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__instantiate_imp
end))


let __proj__Mkenv__item__effects : env  ->  effects = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__effects
end))


let __proj__Mkenv__item__generalize : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__generalize
end))


let __proj__Mkenv__item__letrecs : env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__letrecs
end))


let __proj__Mkenv__item__top_level : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__top_level
end))


let __proj__Mkenv__item__check_uvars : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__check_uvars
end))


let __proj__Mkenv__item__use_eq : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__use_eq
end))


let __proj__Mkenv__item__is_iface : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__is_iface
end))


let __proj__Mkenv__item__admit : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__admit
end))


let __proj__Mkenv__item__lax : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__lax
end))


let __proj__Mkenv__item__lax_universes : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__lax_universes
end))


let __proj__Mkenv__item__failhard : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__failhard
end))


let __proj__Mkenv__item__nosynth : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__nosynth
end))


let __proj__Mkenv__item__tc_term : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t) = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__tc_term
end))


let __proj__Mkenv__item__type_of : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t) = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__type_of
end))


let __proj__Mkenv__item__universe_of : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__universe_of
end))


let __proj__Mkenv__item__use_bv_sorts : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__use_bv_sorts
end))


let __proj__Mkenv__item__qname_and_index : env  ->  (FStar_Ident.lident * Prims.int) FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__qname_and_index
end))


let __proj__Mkenv__item__proof_ns : env  ->  proof_namespace = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__proof_ns
end))


let __proj__Mkenv__item__synth : env  ->  env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__synth
end))


let __proj__Mkenv__item__is_native_tactic : env  ->  FStar_Ident.lid  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__is_native_tactic
end))


let __proj__Mkenv__item__identifier_info : env  ->  FStar_TypeChecker_Common.id_info_table FStar_ST.ref = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__identifier_info
end))


let __proj__Mkenv__item__tc_hooks : env  ->  tcenv_hooks = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__tc_hooks
end))


let __proj__Mkenv__item__dsenv : env  ->  FStar_ToSyntax_Env.env = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__dsenv
end))


let __proj__Mksolver_t__item__init : solver_t  ->  env  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__init
end))


let __proj__Mksolver_t__item__push : solver_t  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__push
end))


let __proj__Mksolver_t__item__pop : solver_t  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__pop
end))


let __proj__Mksolver_t__item__encode_modul : solver_t  ->  env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__encode_modul
end))


let __proj__Mksolver_t__item__encode_sig : solver_t  ->  env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__encode_sig
end))


let __proj__Mksolver_t__item__preprocess : solver_t  ->  env  ->  goal  ->  (env * goal * FStar_Options.optionstate) Prims.list = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__preprocess
end))


let __proj__Mksolver_t__item__solve : solver_t  ->  (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__solve
end))


let __proj__Mksolver_t__item__is_trivial : solver_t  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__is_trivial
end))


let __proj__Mksolver_t__item__finish : solver_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__finish
end))


let __proj__Mksolver_t__item__refresh : solver_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
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


let default_tc_hooks : tcenv_hooks = {tc_push_in_gamma_hook = (fun uu____5036 uu____5037 -> ())}


let tc_hooks : env  ->  tcenv_hooks = (fun env -> env.tc_hooks)


let set_tc_hooks : env  ->  tcenv_hooks  ->  env = (fun env hooks -> (

let uu___144_5050 = env
in {solver = uu___144_5050.solver; range = uu___144_5050.range; curmodule = uu___144_5050.curmodule; gamma = uu___144_5050.gamma; gamma_cache = uu___144_5050.gamma_cache; modules = uu___144_5050.modules; expected_typ = uu___144_5050.expected_typ; sigtab = uu___144_5050.sigtab; is_pattern = uu___144_5050.is_pattern; instantiate_imp = uu___144_5050.instantiate_imp; effects = uu___144_5050.effects; generalize = uu___144_5050.generalize; letrecs = uu___144_5050.letrecs; top_level = uu___144_5050.top_level; check_uvars = uu___144_5050.check_uvars; use_eq = uu___144_5050.use_eq; is_iface = uu___144_5050.is_iface; admit = uu___144_5050.admit; lax = uu___144_5050.lax; lax_universes = uu___144_5050.lax_universes; failhard = uu___144_5050.failhard; nosynth = uu___144_5050.nosynth; tc_term = uu___144_5050.tc_term; type_of = uu___144_5050.type_of; universe_of = uu___144_5050.universe_of; use_bv_sorts = uu___144_5050.use_bv_sorts; qname_and_index = uu___144_5050.qname_and_index; proof_ns = uu___144_5050.proof_ns; synth = uu___144_5050.synth; is_native_tactic = uu___144_5050.is_native_tactic; identifier_info = uu___144_5050.identifier_info; tc_hooks = hooks; dsenv = uu___144_5050.dsenv}))


type env_t =
env


type sigtable =
FStar_Syntax_Syntax.sigelt FStar_Util.smap


let should_verify : env  ->  Prims.bool = (fun env -> (((not (env.lax)) && (not (env.admit))) && (FStar_Options.should_verify env.curmodule.FStar_Ident.str)))


let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match (((d), (q))) with
| (NoDelta, uu____5065) -> begin
true
end
| (Eager_unfolding_only, FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____5066), FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____5067), FStar_Syntax_Syntax.Visible_default) -> begin
true
end
| (Inlining, FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| uu____5068 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab : 'Auu____5077 . Prims.unit  ->  'Auu____5077 FStar_Util.smap = (fun uu____5083 -> (FStar_Util.smap_create default_table_size))


let new_gamma_cache : 'Auu____5088 . Prims.unit  ->  'Auu____5088 FStar_Util.smap = (fun uu____5094 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc_term type_of universe_of solver module_lid -> (

let uu____5169 = (new_gamma_cache ())
in (

let uu____5172 = (new_sigtab ())
in (

let uu____5175 = (

let uu____5176 = (FStar_Options.using_facts_from ())
in (match (uu____5176) with
| FStar_Pervasives_Native.Some (ns) -> begin
(

let uu____5186 = (

let uu____5195 = (FStar_List.map (fun s -> (((FStar_Ident.path_of_text s)), (true))) ns)
in (FStar_List.append uu____5195 (((([]), (false)))::[])))
in (uu____5186)::[])
end
| FStar_Pervasives_Native.None -> begin
([])::[]
end))
in (

let uu____5268 = (FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty)
in (

let uu____5271 = (FStar_ToSyntax_Env.empty_env ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = uu____5169; modules = []; expected_typ = FStar_Pervasives_Native.None; sigtab = uu____5172; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; failhard = false; nosynth = false; tc_term = tc_term; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = FStar_Pervasives_Native.None; proof_ns = uu____5175; synth = (fun e g tau -> (failwith "no synthesizer available")); is_native_tactic = (fun uu____5303 -> false); identifier_info = uu____5268; tc_hooks = default_tc_hooks; dsenv = uu____5271}))))))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


let query_indices : (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let push_query_indices : Prims.unit  ->  Prims.unit = (fun uu____5374 -> (

let uu____5375 = (FStar_ST.op_Bang query_indices)
in (match (uu____5375) with
| [] -> begin
(failwith "Empty query indices!")
end
| uu____5452 -> begin
(

let uu____5461 = (

let uu____5470 = (

let uu____5477 = (FStar_ST.op_Bang query_indices)
in (FStar_List.hd uu____5477))
in (

let uu____5554 = (FStar_ST.op_Bang query_indices)
in (uu____5470)::uu____5554))
in (FStar_ST.op_Colon_Equals query_indices uu____5461))
end)))


let pop_query_indices : Prims.unit  ->  Prims.unit = (fun uu____5696 -> (

let uu____5697 = (FStar_ST.op_Bang query_indices)
in (match (uu____5697) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals query_indices tl1)
end)))


let add_query_index : (FStar_Ident.lident * Prims.int)  ->  Prims.unit = (fun uu____5865 -> (match (uu____5865) with
| (l, n1) -> begin
(

let uu____5872 = (FStar_ST.op_Bang query_indices)
in (match (uu____5872) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals query_indices (((((l), (n1)))::hd1)::tl1))
end
| uu____6037 -> begin
(failwith "Empty query indices")
end))
end))


let peek_query_indices : Prims.unit  ->  (FStar_Ident.lident * Prims.int) Prims.list = (fun uu____6055 -> (

let uu____6056 = (FStar_ST.op_Bang query_indices)
in (FStar_List.hd uu____6056)))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push_stack : env  ->  env = (fun env -> ((

let uu____6151 = (

let uu____6154 = (FStar_ST.op_Bang stack)
in (env)::uu____6154)
in (FStar_ST.op_Colon_Equals stack uu____6151));
(

let uu___145_6257 = env
in (

let uu____6258 = (FStar_Util.smap_copy (gamma_cache env))
in (

let uu____6261 = (FStar_Util.smap_copy (sigtab env))
in (

let uu____6264 = (

let uu____6267 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_Util.mk_ref uu____6267))
in {solver = uu___145_6257.solver; range = uu___145_6257.range; curmodule = uu___145_6257.curmodule; gamma = uu___145_6257.gamma; gamma_cache = uu____6258; modules = uu___145_6257.modules; expected_typ = uu___145_6257.expected_typ; sigtab = uu____6261; is_pattern = uu___145_6257.is_pattern; instantiate_imp = uu___145_6257.instantiate_imp; effects = uu___145_6257.effects; generalize = uu___145_6257.generalize; letrecs = uu___145_6257.letrecs; top_level = uu___145_6257.top_level; check_uvars = uu___145_6257.check_uvars; use_eq = uu___145_6257.use_eq; is_iface = uu___145_6257.is_iface; admit = uu___145_6257.admit; lax = uu___145_6257.lax; lax_universes = uu___145_6257.lax_universes; failhard = uu___145_6257.failhard; nosynth = uu___145_6257.nosynth; tc_term = uu___145_6257.tc_term; type_of = uu___145_6257.type_of; universe_of = uu___145_6257.universe_of; use_bv_sorts = uu___145_6257.use_bv_sorts; qname_and_index = uu___145_6257.qname_and_index; proof_ns = uu___145_6257.proof_ns; synth = uu___145_6257.synth; is_native_tactic = uu___145_6257.is_native_tactic; identifier_info = uu____6264; tc_hooks = uu___145_6257.tc_hooks; dsenv = uu___145_6257.dsenv}))));
))


let pop_stack : Prims.unit  ->  env = (fun uu____6331 -> (

let uu____6332 = (FStar_ST.op_Bang stack)
in (match (uu____6332) with
| (env)::tl1 -> begin
((FStar_ST.op_Colon_Equals stack tl1);
env;
)
end
| uu____6440 -> begin
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
in (match (env.qname_and_index) with
| FStar_Pervasives_Native.None -> begin
env
end
| FStar_Pervasives_Native.Some (l, n1) -> begin
(

let uu____6484 = (FStar_All.pipe_right qix (FStar_List.tryFind (fun uu____6510 -> (match (uu____6510) with
| (m, uu____6516) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____6484) with
| FStar_Pervasives_Native.None -> begin
(

let next = (n1 + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___146_6523 = env
in {solver = uu___146_6523.solver; range = uu___146_6523.range; curmodule = uu___146_6523.curmodule; gamma = uu___146_6523.gamma; gamma_cache = uu___146_6523.gamma_cache; modules = uu___146_6523.modules; expected_typ = uu___146_6523.expected_typ; sigtab = uu___146_6523.sigtab; is_pattern = uu___146_6523.is_pattern; instantiate_imp = uu___146_6523.instantiate_imp; effects = uu___146_6523.effects; generalize = uu___146_6523.generalize; letrecs = uu___146_6523.letrecs; top_level = uu___146_6523.top_level; check_uvars = uu___146_6523.check_uvars; use_eq = uu___146_6523.use_eq; is_iface = uu___146_6523.is_iface; admit = uu___146_6523.admit; lax = uu___146_6523.lax; lax_universes = uu___146_6523.lax_universes; failhard = uu___146_6523.failhard; nosynth = uu___146_6523.nosynth; tc_term = uu___146_6523.tc_term; type_of = uu___146_6523.type_of; universe_of = uu___146_6523.universe_of; use_bv_sorts = uu___146_6523.use_bv_sorts; qname_and_index = FStar_Pervasives_Native.Some (((l), (next))); proof_ns = uu___146_6523.proof_ns; synth = uu___146_6523.synth; is_native_tactic = uu___146_6523.is_native_tactic; identifier_info = uu___146_6523.identifier_info; tc_hooks = uu___146_6523.tc_hooks; dsenv = uu___146_6523.dsenv});
))
end
| FStar_Pervasives_Native.Some (uu____6528, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___147_6536 = env
in {solver = uu___147_6536.solver; range = uu___147_6536.range; curmodule = uu___147_6536.curmodule; gamma = uu___147_6536.gamma; gamma_cache = uu___147_6536.gamma_cache; modules = uu___147_6536.modules; expected_typ = uu___147_6536.expected_typ; sigtab = uu___147_6536.sigtab; is_pattern = uu___147_6536.is_pattern; instantiate_imp = uu___147_6536.instantiate_imp; effects = uu___147_6536.effects; generalize = uu___147_6536.generalize; letrecs = uu___147_6536.letrecs; top_level = uu___147_6536.top_level; check_uvars = uu___147_6536.check_uvars; use_eq = uu___147_6536.use_eq; is_iface = uu___147_6536.is_iface; admit = uu___147_6536.admit; lax = uu___147_6536.lax; lax_universes = uu___147_6536.lax_universes; failhard = uu___147_6536.failhard; nosynth = uu___147_6536.nosynth; tc_term = uu___147_6536.tc_term; type_of = uu___147_6536.type_of; universe_of = uu___147_6536.universe_of; use_bv_sorts = uu___147_6536.use_bv_sorts; qname_and_index = FStar_Pervasives_Native.Some (((l), (next))); proof_ns = uu___147_6536.proof_ns; synth = uu___147_6536.synth; is_native_tactic = uu___147_6536.is_native_tactic; identifier_info = uu___147_6536.identifier_info; tc_hooks = uu___147_6536.tc_hooks; dsenv = uu___147_6536.dsenv});
))
end))
end)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> (match ((Prims.op_Equality r FStar_Range.dummyRange)) with
| true -> begin
e
end
| uu____6557 -> begin
(

let uu___148_6558 = e
in {solver = uu___148_6558.solver; range = r; curmodule = uu___148_6558.curmodule; gamma = uu___148_6558.gamma; gamma_cache = uu___148_6558.gamma_cache; modules = uu___148_6558.modules; expected_typ = uu___148_6558.expected_typ; sigtab = uu___148_6558.sigtab; is_pattern = uu___148_6558.is_pattern; instantiate_imp = uu___148_6558.instantiate_imp; effects = uu___148_6558.effects; generalize = uu___148_6558.generalize; letrecs = uu___148_6558.letrecs; top_level = uu___148_6558.top_level; check_uvars = uu___148_6558.check_uvars; use_eq = uu___148_6558.use_eq; is_iface = uu___148_6558.is_iface; admit = uu___148_6558.admit; lax = uu___148_6558.lax; lax_universes = uu___148_6558.lax_universes; failhard = uu___148_6558.failhard; nosynth = uu___148_6558.nosynth; tc_term = uu___148_6558.tc_term; type_of = uu___148_6558.type_of; universe_of = uu___148_6558.universe_of; use_bv_sorts = uu___148_6558.use_bv_sorts; qname_and_index = uu___148_6558.qname_and_index; proof_ns = uu___148_6558.proof_ns; synth = uu___148_6558.synth; is_native_tactic = uu___148_6558.is_native_tactic; identifier_info = uu___148_6558.identifier_info; tc_hooks = uu___148_6558.tc_hooks; dsenv = uu___148_6558.dsenv})
end))


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let toggle_id_info : env  ->  Prims.bool  ->  Prims.unit = (fun env enabled -> (

let uu____6571 = (

let uu____6572 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_toggle uu____6572 enabled))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____6571)))


let insert_bv_info : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env bv ty -> (

let uu____6677 = (

let uu____6678 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_insert_bv uu____6678 bv ty))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____6677)))


let insert_fv_info : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env fv ty -> (

let uu____6783 = (

let uu____6784 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_insert_fv uu____6784 fv ty))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____6783)))


let promote_id_info : env  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  Prims.unit = (fun env ty_map -> (

let uu____6890 = (

let uu____6891 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_promote uu____6891 ty_map))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____6890)))


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let uu___149_7002 = env
in {solver = uu___149_7002.solver; range = uu___149_7002.range; curmodule = lid; gamma = uu___149_7002.gamma; gamma_cache = uu___149_7002.gamma_cache; modules = uu___149_7002.modules; expected_typ = uu___149_7002.expected_typ; sigtab = uu___149_7002.sigtab; is_pattern = uu___149_7002.is_pattern; instantiate_imp = uu___149_7002.instantiate_imp; effects = uu___149_7002.effects; generalize = uu___149_7002.generalize; letrecs = uu___149_7002.letrecs; top_level = uu___149_7002.top_level; check_uvars = uu___149_7002.check_uvars; use_eq = uu___149_7002.use_eq; is_iface = uu___149_7002.is_iface; admit = uu___149_7002.admit; lax = uu___149_7002.lax; lax_universes = uu___149_7002.lax_universes; failhard = uu___149_7002.failhard; nosynth = uu___149_7002.nosynth; tc_term = uu___149_7002.tc_term; type_of = uu___149_7002.type_of; universe_of = uu___149_7002.universe_of; use_bv_sorts = uu___149_7002.use_bv_sorts; qname_and_index = uu___149_7002.qname_and_index; proof_ns = uu___149_7002.proof_ns; synth = uu___149_7002.synth; is_native_tactic = uu___149_7002.is_native_tactic; identifier_info = uu___149_7002.identifier_info; tc_hooks = uu___149_7002.tc_hooks; dsenv = uu___149_7002.dsenv}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v1 -> (

let uu____7033 = (FStar_Syntax_Print.bv_to_string v1)
in (FStar_Util.format1 "Variable \"%s\" not found" uu____7033)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun uu____7037 -> (

let uu____7038 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____7038)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), uu____7078) -> begin
(

let n1 = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n1 - i)), (u))))))
in (

let uu____7102 = (FStar_Syntax_Subst.subst vs t)
in ((us), (uu____7102)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun uu___131_7116 -> (match (uu___131_7116) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun uu____7140 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let uu____7155 = (inst_tscheme t)
in (match (uu____7155) with
| (us, t1) -> begin
(

let uu____7166 = (FStar_Syntax_Subst.set_use_range r t1)
in ((us), (uu____7166)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed uu____7182 -> (match (uu____7182) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs1 = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in ((match ((Prims.op_disEquality (FStar_List.length insts) (FStar_List.length univs1))) with
| true -> begin
(

let uu____7197 = (

let uu____7198 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (

let uu____7199 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (

let uu____7200 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____7201 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" uu____7198 uu____7199 uu____7200 uu____7201)))))
in (failwith uu____7197))
end
| uu____7202 -> begin
()
end);
(

let uu____7203 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (FStar_Pervasives_Native.snd uu____7203));
))
end
| uu____7210 -> begin
(

let uu____7211 = (

let uu____7212 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" uu____7212))
in (failwith uu____7211))
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
| uu____7217 -> begin
false
end))


let uu___is_No : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____7222 -> begin
false
end))


let uu___is_Maybe : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____7227 -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in (match ((Prims.op_Equality l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
Yes
end
| uu____7237 -> begin
(match ((FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur1 = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l1 -> (match (((c), (l1))) with
| ([], uu____7263) -> begin
Maybe
end
| (uu____7270, []) -> begin
No
end
| ((hd1)::tl1, (hd')::tl') when (Prims.op_Equality hd1.FStar_Ident.idText hd'.FStar_Ident.idText) -> begin
(aux tl1 tl')
end
| uu____7289 -> begin
No
end))
in (aux cur1 lns))))
end
| uu____7298 -> begin
No
end)
end)))


let lookup_qname : env  ->  FStar_Ident.lident  ->  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option)) FStar_Util.either * FStar_Range.range) FStar_Pervasives_Native.option = (fun env lid -> (

let cur_mod = (in_cur_mod env lid)
in (

let cache = (fun t -> ((FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t);
FStar_Pervasives_Native.Some (t);
))
in (

let found = (match ((Prims.op_disEquality cur_mod No)) with
| true -> begin
(

let uu____7396 = (FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)
in (match (uu____7396) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.find_map env.gamma (fun uu___132_7441 -> (match (uu___132_7441) with
| Binding_lid (l, t) -> begin
(match ((FStar_Ident.lid_equals lid l)) with
| true -> begin
(

let uu____7484 = (

let uu____7503 = (

let uu____7518 = (inst_tscheme t)
in FStar_Util.Inl (uu____7518))
in ((uu____7503), ((FStar_Ident.range_of_lid l))))
in FStar_Pervasives_Native.Some (uu____7484))
end
| uu____7565 -> begin
FStar_Pervasives_Native.None
end)
end
| Binding_sig (uu____7584, {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (ses, uu____7586); FStar_Syntax_Syntax.sigrng = uu____7587; FStar_Syntax_Syntax.sigquals = uu____7588; FStar_Syntax_Syntax.sigmeta = uu____7589; FStar_Syntax_Syntax.sigattrs = uu____7590}) -> begin
(FStar_Util.find_map ses (fun se -> (

let uu____7610 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____7610) with
| true -> begin
(cache ((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| uu____7641 -> begin
FStar_Pervasives_Native.None
end))))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____7656) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____7663 -> begin
(cache t)
end))
in (

let uu____7664 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____7664) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (l) -> begin
(maybe_cache ((FStar_Util.Inr (((s), (FStar_Pervasives_Native.None)))), ((FStar_Ident.range_of_lid l))))
end)))
end
| Binding_sig_inst (lids, s, us) -> begin
(

let uu____7739 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____7739) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (l) -> begin
FStar_Pervasives_Native.Some (((FStar_Util.Inr (((s), (FStar_Pervasives_Native.Some (us))))), ((FStar_Ident.range_of_lid l))))
end))
end
| uu____7825 -> begin
FStar_Pervasives_Native.None
end)))
end
| se -> begin
se
end))
end
| uu____7847 -> begin
FStar_Pervasives_Native.None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| uu____7904 -> begin
(

let uu____7905 = (find_in_sigtab env lid)
in (match (uu____7905) with
| FStar_Pervasives_Native.Some (se) -> begin
FStar_Pervasives_Native.Some (((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end)))))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____8004) -> begin
(add_sigelts env ses)
end
| uu____8013 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids);
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| uu____8027 -> begin
()
end);
))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) FStar_Pervasives_Native.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun uu___133_8056 -> (match (uu___133_8056) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
FStar_Pervasives_Native.Some (((id.FStar_Syntax_Syntax.sort), (id.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
end
| uu____8074 -> begin
FStar_Pervasives_Native.None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) * FStar_Range.range) FStar_Pervasives_Native.option = (fun se lid -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____8109, (lb)::[]), uu____8111) -> begin
(

let uu____8124 = (

let uu____8133 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____8142 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in ((uu____8133), (uu____8142))))
in FStar_Pervasives_Native.Some (uu____8124))
end
| FStar_Syntax_Syntax.Sig_let ((uu____8155, lbs), uu____8157) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____8193) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
(

let uu____8205 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____8205) with
| true -> begin
(

let uu____8216 = (

let uu____8225 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____8234 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____8225), (uu____8234))))
in FStar_Pervasives_Native.Some (uu____8216))
end
| uu____8247 -> begin
FStar_Pervasives_Native.None
end))
end)))
end
| uu____8256 -> begin
FStar_Pervasives_Native.None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) * FStar_Range.range) FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____8290 = (

let uu____8299 = (

let uu____8304 = (

let uu____8305 = (

let uu____8308 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders uu____8308))
in ((ne.FStar_Syntax_Syntax.univs), (uu____8305)))
in (inst_tscheme uu____8304))
in ((uu____8299), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____8290))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, uu____8328, uu____8329) -> begin
(

let uu____8334 = (

let uu____8343 = (

let uu____8348 = (

let uu____8349 = (

let uu____8352 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders uu____8352))
in ((us), (uu____8349)))
in (inst_tscheme uu____8348))
in ((uu____8343), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____8334))
end
| uu____8369 -> begin
FStar_Pervasives_Native.None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) * FStar_Range.range) FStar_Pervasives_Native.option = (fun env lid -> (

let mapper = (fun uu____8429 -> (match (uu____8429) with
| (lr, rng) -> begin
(match (lr) with
| FStar_Util.Inl (t) -> begin
FStar_Pervasives_Native.Some (((t), (rng)))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____8525, uvs, t, uu____8528, uu____8529, uu____8530); FStar_Syntax_Syntax.sigrng = uu____8531; FStar_Syntax_Syntax.sigquals = uu____8532; FStar_Syntax_Syntax.sigmeta = uu____8533; FStar_Syntax_Syntax.sigattrs = uu____8534}, FStar_Pervasives_Native.None) -> begin
(

let uu____8555 = (

let uu____8564 = (inst_tscheme ((uvs), (t)))
in ((uu____8564), (rng)))
in FStar_Pervasives_Native.Some (uu____8555))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t); FStar_Syntax_Syntax.sigrng = uu____8584; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____8586; FStar_Syntax_Syntax.sigattrs = uu____8587}, FStar_Pervasives_Native.None) -> begin
(

let uu____8604 = (

let uu____8605 = (in_cur_mod env l)
in (Prims.op_Equality uu____8605 Yes))
in (match (uu____8604) with
| true -> begin
(

let uu____8616 = ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface)
in (match (uu____8616) with
| true -> begin
(

let uu____8629 = (

let uu____8638 = (inst_tscheme ((uvs), (t)))
in ((uu____8638), (rng)))
in FStar_Pervasives_Native.Some (uu____8629))
end
| uu____8655 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____8664 -> begin
(

let uu____8665 = (

let uu____8674 = (inst_tscheme ((uvs), (t)))
in ((uu____8674), (rng)))
in FStar_Pervasives_Native.Some (uu____8665))
end))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____8695, uu____8696); FStar_Syntax_Syntax.sigrng = uu____8697; FStar_Syntax_Syntax.sigquals = uu____8698; FStar_Syntax_Syntax.sigmeta = uu____8699; FStar_Syntax_Syntax.sigattrs = uu____8700}, FStar_Pervasives_Native.None) -> begin
(match (tps) with
| [] -> begin
(

let uu____8739 = (

let uu____8748 = (inst_tscheme ((uvs), (k)))
in ((uu____8748), (rng)))
in FStar_Pervasives_Native.Some (uu____8739))
end
| uu____8765 -> begin
(

let uu____8766 = (

let uu____8775 = (

let uu____8780 = (

let uu____8781 = (

let uu____8784 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____8784))
in ((uvs), (uu____8781)))
in (inst_tscheme uu____8780))
in ((uu____8775), (rng)))
in FStar_Pervasives_Native.Some (uu____8766))
end)
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____8805, uu____8806); FStar_Syntax_Syntax.sigrng = uu____8807; FStar_Syntax_Syntax.sigquals = uu____8808; FStar_Syntax_Syntax.sigmeta = uu____8809; FStar_Syntax_Syntax.sigattrs = uu____8810}, FStar_Pervasives_Native.Some (us)) -> begin
(match (tps) with
| [] -> begin
(

let uu____8850 = (

let uu____8859 = (inst_tscheme_with ((uvs), (k)) us)
in ((uu____8859), (rng)))
in FStar_Pervasives_Native.Some (uu____8850))
end
| uu____8876 -> begin
(

let uu____8877 = (

let uu____8886 = (

let uu____8891 = (

let uu____8892 = (

let uu____8895 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____8895))
in ((uvs), (uu____8892)))
in (inst_tscheme_with uu____8891 us))
in ((uu____8886), (rng)))
in FStar_Pervasives_Native.Some (uu____8877))
end)
end
| FStar_Util.Inr (se) -> begin
(

let uu____8929 = (match (se) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____8950); FStar_Syntax_Syntax.sigrng = uu____8951; FStar_Syntax_Syntax.sigquals = uu____8952; FStar_Syntax_Syntax.sigmeta = uu____8953; FStar_Syntax_Syntax.sigattrs = uu____8954}, FStar_Pervasives_Native.None) -> begin
(lookup_type_of_let (FStar_Pervasives_Native.fst se) lid)
end
| uu____8969 -> begin
(effect_signature (FStar_Pervasives_Native.fst se))
end)
in (FStar_All.pipe_right uu____8929 (FStar_Util.map_option (fun uu____9017 -> (match (uu____9017) with
| (us_t, rng1) -> begin
((us_t), (rng1))
end)))))
end)
end))
in (

let uu____9048 = (

let uu____9059 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____9059 mapper))
in (match (uu____9048) with
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
FStar_Pervasives_Native.Some (((((us), ((

let uu___150_9152 = t
in {FStar_Syntax_Syntax.n = uu___150_9152.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = uu___150_9152.FStar_Syntax_Syntax.vars})))), (r)))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____9179 = (lookup_qname env l)
in (match (uu____9179) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____9218) -> begin
true
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) = (fun env bv -> (

let bvr = (FStar_Syntax_Syntax.range_of_bv bv)
in (

let uu____9268 = (try_lookup_bv env bv)
in (match (uu____9268) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9283 = (

let uu____9284 = (

let uu____9289 = (variable_not_found bv)
in ((uu____9289), (bvr)))
in FStar_Errors.Error (uu____9284))
in (FStar_Exn.raise uu____9283))
end
| FStar_Pervasives_Native.Some (t, r) -> begin
(

let uu____9300 = (FStar_Syntax_Subst.set_use_range bvr t)
in (

let uu____9301 = (FStar_Range.set_use_range r bvr)
in ((uu____9300), (uu____9301))))
end))))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) FStar_Pervasives_Native.option = (fun env l -> (

let uu____9320 = (try_lookup_lid_aux env l)
in (match (uu____9320) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
(

let use_range = (FStar_Ident.range_of_lid l)
in (

let r1 = (FStar_Range.set_use_range r use_range)
in (

let uu____9386 = (

let uu____9395 = (

let uu____9400 = (FStar_Syntax_Subst.set_use_range use_range t)
in ((us), (uu____9400)))
in ((uu____9395), (r1)))
in FStar_Pervasives_Native.Some (uu____9386))))
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) = (fun env l -> (

let uu____9429 = (try_lookup_lid env l)
in (match (uu____9429) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9456 = (

let uu____9457 = (

let uu____9462 = (name_not_found l)
in ((uu____9462), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____9457))
in (FStar_Exn.raise uu____9456))
end
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end)))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun uu___134_9500 -> (match (uu___134_9500) with
| Binding_univ (y) -> begin
(Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)
end
| uu____9502 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env lid -> (

let uu____9519 = (lookup_qname env lid)
in (match (uu____9519) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____9548, uvs, t); FStar_Syntax_Syntax.sigrng = uu____9551; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____9553; FStar_Syntax_Syntax.sigattrs = uu____9554}, FStar_Pervasives_Native.None), uu____9555) -> begin
(

let uu____9604 = (

let uu____9615 = (

let uu____9620 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (uu____9620)))
in ((uu____9615), (q)))
in FStar_Pervasives_Native.Some (uu____9604))
end
| uu____9637 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____9676 = (lookup_qname env lid)
in (match (uu____9676) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____9701, uvs, t); FStar_Syntax_Syntax.sigrng = uu____9704; FStar_Syntax_Syntax.sigquals = uu____9705; FStar_Syntax_Syntax.sigmeta = uu____9706; FStar_Syntax_Syntax.sigattrs = uu____9707}, FStar_Pervasives_Native.None), uu____9708) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____9757 -> begin
(

let uu____9778 = (

let uu____9779 = (

let uu____9784 = (name_not_found lid)
in ((uu____9784), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____9779))
in (FStar_Exn.raise uu____9778))
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____9801 = (lookup_qname env lid)
in (match (uu____9801) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____9826, uvs, t, uu____9829, uu____9830, uu____9831); FStar_Syntax_Syntax.sigrng = uu____9832; FStar_Syntax_Syntax.sigquals = uu____9833; FStar_Syntax_Syntax.sigmeta = uu____9834; FStar_Syntax_Syntax.sigattrs = uu____9835}, FStar_Pervasives_Native.None), uu____9836) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____9889 -> begin
(

let uu____9910 = (

let uu____9911 = (

let uu____9916 = (name_not_found lid)
in ((uu____9916), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____9911))
in (FStar_Exn.raise uu____9910))
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  (Prims.bool * FStar_Ident.lident Prims.list) = (fun env lid -> (

let uu____9935 = (lookup_qname env lid)
in (match (uu____9935) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____9962, uu____9963, uu____9964, uu____9965, uu____9966, dcs); FStar_Syntax_Syntax.sigrng = uu____9968; FStar_Syntax_Syntax.sigquals = uu____9969; FStar_Syntax_Syntax.sigmeta = uu____9970; FStar_Syntax_Syntax.sigattrs = uu____9971}, uu____9972), uu____9973) -> begin
((true), (dcs))
end
| uu____10034 -> begin
((false), ([]))
end)))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____10065 = (lookup_qname env lid)
in (match (uu____10065) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____10086, uu____10087, uu____10088, l, uu____10090, uu____10091); FStar_Syntax_Syntax.sigrng = uu____10092; FStar_Syntax_Syntax.sigquals = uu____10093; FStar_Syntax_Syntax.sigmeta = uu____10094; FStar_Syntax_Syntax.sigattrs = uu____10095}, uu____10096), uu____10097) -> begin
l
end
| uu____10152 -> begin
(

let uu____10173 = (

let uu____10174 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" uu____10174))
in (failwith uu____10173))
end)))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (

let uu____10211 = (lookup_qname env lid)
in (match (uu____10211) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____10239) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____10290, lbs), uu____10292) when (visible se.FStar_Syntax_Syntax.sigquals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____10320 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____10320) with
| true -> begin
FStar_Pervasives_Native.Some (((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbdef)))
end
| uu____10343 -> begin
FStar_Pervasives_Native.None
end)))))
end
| uu____10352 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____10357 -> begin
FStar_Pervasives_Native.None
end))))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env ftv -> (

let uu____10394 = (lookup_qname env ftv)
in (match (uu____10394) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____10418) -> begin
(

let uu____10463 = (effect_signature se)
in (match (uu____10463) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((uu____10484, t), r) -> begin
(

let uu____10499 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t)
in FStar_Pervasives_Native.Some (uu____10499))
end))
end
| uu____10500 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (

let uu____10529 = (try_lookup_effect_lid env ftv)
in (match (uu____10529) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10532 = (

let uu____10533 = (

let uu____10538 = (name_not_found ftv)
in ((uu____10538), ((FStar_Ident.range_of_lid ftv))))
in FStar_Errors.Error (uu____10533))
in (FStar_Exn.raise uu____10532))
end
| FStar_Pervasives_Native.Some (k) -> begin
k
end)))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun env univ_insts lid0 -> (

let uu____10558 = (lookup_qname env lid0)
in (match (uu____10558) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs1, binders, c, uu____10589); FStar_Syntax_Syntax.sigrng = uu____10590; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____10592; FStar_Syntax_Syntax.sigattrs = uu____10593}, FStar_Pervasives_Native.None), uu____10594) -> begin
(

let lid1 = (

let uu____10648 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) (FStar_Ident.range_of_lid lid0))
in (FStar_Ident.set_lid_range lid uu____10648))
in (

let uu____10649 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___135_10653 -> (match (uu___135_10653) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____10654 -> begin
false
end))))
in (match (uu____10649) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____10665 -> begin
(

let insts = (match ((Prims.op_Equality (FStar_List.length univ_insts) (FStar_List.length univs1))) with
| true -> begin
univ_insts
end
| uu____10667 -> begin
(

let uu____10668 = (

let uu____10669 = (

let uu____10670 = (get_range env)
in (FStar_Range.string_of_range uu____10670))
in (

let uu____10671 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____10672 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format3 "(%s) Unexpected instantiation of effect %s with %s universes" uu____10669 uu____10671 uu____10672))))
in (failwith uu____10668))
end)
in (match (((binders), (univs1))) with
| ([], uu____10679) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (uu____10696, (uu____10697)::(uu____10698)::uu____10699) -> begin
(

let uu____10704 = (

let uu____10705 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____10706 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" uu____10705 uu____10706)))
in (failwith uu____10704))
end
| uu____10713 -> begin
(

let uu____10718 = (

let uu____10723 = (

let uu____10724 = (FStar_Syntax_Util.arrow binders c)
in ((univs1), (uu____10724)))
in (inst_tscheme_with uu____10723 insts))
in (match (uu____10718) with
| (uu____10735, t) -> begin
(

let t1 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid1) t)
in (

let uu____10738 = (

let uu____10739 = (FStar_Syntax_Subst.compress t1)
in uu____10739.FStar_Syntax_Syntax.n)
in (match (uu____10738) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
FStar_Pervasives_Native.Some (((binders1), (c1)))
end
| uu____10786 -> begin
(failwith "Impossible")
end)))
end))
end))
end)))
end
| uu____10793 -> begin
FStar_Pervasives_Native.None
end)))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find1 = (fun l1 -> (

let uu____10835 = (lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l1)
in (match (uu____10835) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____10848, c) -> begin
(

let l2 = (FStar_Syntax_Util.comp_effect_name c)
in (

let uu____10855 = (find1 l2)
in (match (uu____10855) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (l2)
end
| FStar_Pervasives_Native.Some (l') -> begin
FStar_Pervasives_Native.Some (l')
end)))
end)))
in (

let res = (

let uu____10862 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____10862) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____10866 = (find1 l)
in (match (uu____10866) with
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

let uu____10882 = (lookup_qname env l1)
in (match (uu____10882) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (uu____10905); FStar_Syntax_Syntax.sigrng = uu____10906; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____10908; FStar_Syntax_Syntax.sigattrs = uu____10909}, uu____10910), uu____10911) -> begin
q
end
| uu____10962 -> begin
[]
end))))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun uu____10998 -> (

let uu____10999 = (

let uu____11000 = (FStar_Util.string_of_int i)
in (

let uu____11001 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" uu____11000 uu____11001)))
in (failwith uu____10999)))
in (

let uu____11002 = (lookup_datacon env lid)
in (match (uu____11002) with
| (uu____11007, t) -> begin
(

let uu____11009 = (

let uu____11010 = (FStar_Syntax_Subst.compress t)
in uu____11010.FStar_Syntax_Syntax.n)
in (match (uu____11009) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____11014) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____11035 -> begin
(

let b = (FStar_List.nth binders i)
in (

let uu____11045 = (FStar_Syntax_Util.mk_field_projector_name lid (FStar_Pervasives_Native.fst b) i)
in (FStar_All.pipe_right uu____11045 FStar_Pervasives_Native.fst)))
end)
end
| uu____11054 -> begin
(fail ())
end))
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____11063 = (lookup_qname env l)
in (match (uu____11063) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____11084, uu____11085, uu____11086); FStar_Syntax_Syntax.sigrng = uu____11087; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____11089; FStar_Syntax_Syntax.sigattrs = uu____11090}, uu____11091), uu____11092) -> begin
(FStar_Util.for_some (fun uu___136_11145 -> (match (uu___136_11145) with
| FStar_Syntax_Syntax.Projector (uu____11146) -> begin
true
end
| uu____11151 -> begin
false
end)) quals)
end
| uu____11152 -> begin
false
end)))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____11181 = (lookup_qname env lid)
in (match (uu____11181) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____11202, uu____11203, uu____11204, uu____11205, uu____11206, uu____11207); FStar_Syntax_Syntax.sigrng = uu____11208; FStar_Syntax_Syntax.sigquals = uu____11209; FStar_Syntax_Syntax.sigmeta = uu____11210; FStar_Syntax_Syntax.sigattrs = uu____11211}, uu____11212), uu____11213) -> begin
true
end
| uu____11268 -> begin
false
end)))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____11297 = (lookup_qname env lid)
in (match (uu____11297) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____11318, uu____11319, uu____11320, uu____11321, uu____11322, uu____11323); FStar_Syntax_Syntax.sigrng = uu____11324; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____11326; FStar_Syntax_Syntax.sigattrs = uu____11327}, uu____11328), uu____11329) -> begin
(FStar_Util.for_some (fun uu___137_11390 -> (match (uu___137_11390) with
| FStar_Syntax_Syntax.RecordType (uu____11391) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____11400) -> begin
true
end
| uu____11409 -> begin
false
end)) quals)
end
| uu____11410 -> begin
false
end)))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____11439 = (lookup_qname env lid)
in (match (uu____11439) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____11460, uu____11461); FStar_Syntax_Syntax.sigrng = uu____11462; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____11464; FStar_Syntax_Syntax.sigattrs = uu____11465}, uu____11466), uu____11467) -> begin
(FStar_Util.for_some (fun uu___138_11524 -> (match (uu___138_11524) with
| FStar_Syntax_Syntax.Action (uu____11525) -> begin
true
end
| uu____11526 -> begin
false
end)) quals)
end
| uu____11527 -> begin
false
end)))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (fun env head1 -> (

let uu____11559 = (

let uu____11560 = (FStar_Syntax_Util.un_uinst head1)
in uu____11560.FStar_Syntax_Syntax.n)
in (match (uu____11559) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(Prims.op_Equality fv.FStar_Syntax_Syntax.fv_delta FStar_Syntax_Syntax.Delta_equational)
end
| uu____11564 -> begin
false
end))))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun x -> (match ((FStar_Pervasives_Native.fst x)) with
| FStar_Util.Inl (uu____11631) -> begin
FStar_Pervasives_Native.Some (false)
end
| FStar_Util.Inr (se, uu____11647) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____11664) -> begin
FStar_Pervasives_Native.Some ((FStar_List.contains FStar_Syntax_Syntax.New se.FStar_Syntax_Syntax.sigquals))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____11671) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____11688 -> begin
FStar_Pervasives_Native.Some (false)
end)
end))
in (

let uu____11689 = (

let uu____11692 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____11692 mapper))
in (match (uu____11689) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
false
end))))


let num_inductive_ty_params : env  ->  FStar_Ident.lident  ->  Prims.int = (fun env lid -> (

let uu____11740 = (lookup_qname env lid)
in (match (uu____11740) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____11761, uu____11762, tps, uu____11764, uu____11765, uu____11766); FStar_Syntax_Syntax.sigrng = uu____11767; FStar_Syntax_Syntax.sigquals = uu____11768; FStar_Syntax_Syntax.sigmeta = uu____11769; FStar_Syntax_Syntax.sigattrs = uu____11770}, uu____11771), uu____11772) -> begin
(FStar_List.length tps)
end
| uu____11835 -> begin
(

let uu____11856 = (

let uu____11857 = (

let uu____11862 = (name_not_found lid)
in ((uu____11862), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____11857))
in (FStar_Exn.raise uu____11856))
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun uu____11904 -> (match (uu____11904) with
| (d, uu____11912) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)
end)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (

let uu____11925 = (effect_decl_opt env l)
in (match (uu____11925) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11940 = (

let uu____11941 = (

let uu____11946 = (name_not_found l)
in ((uu____11946), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____11941))
in (FStar_Exn.raise uu____11940))
end
| FStar_Pervasives_Native.Some (md) -> begin
(FStar_Pervasives_Native.fst md)
end)))


let identity_mlift : mlift = {mlift_wp = (fun t wp -> wp); mlift_term = FStar_Pervasives_Native.Some ((fun t wp e -> (FStar_Util.return_all e)))}


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> (match ((FStar_Ident.lid_equals l1 l2)) with
| true -> begin
((l1), (identity_mlift), (identity_mlift))
end
| uu____12004 -> begin
(match ((((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid)))) with
| true -> begin
((FStar_Parser_Const.effect_GTot_lid), (identity_mlift), (identity_mlift))
end
| uu____12011 -> begin
(

let uu____12012 = (FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun uu____12065 -> (match (uu____12065) with
| (m1, m2, uu____12078, uu____12079, uu____12080) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))
in (match (uu____12012) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12097 = (

let uu____12098 = (

let uu____12103 = (

let uu____12104 = (FStar_Syntax_Print.lid_to_string l1)
in (

let uu____12105 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" uu____12104 uu____12105)))
in ((uu____12103), (env.range)))
in FStar_Errors.Error (uu____12098))
in (FStar_Exn.raise uu____12097))
end
| FStar_Pervasives_Native.Some (uu____12112, uu____12113, m3, j1, j2) -> begin
((m3), (j1), (j2))
end))
end)
end))


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge FStar_Pervasives_Native.option = (fun env l1 l2 -> (match (((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)))) with
| true -> begin
FStar_Pervasives_Native.Some ({msource = l1; mtarget = l2; mlift = identity_mlift})
end
| uu____12143 -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end))


let wp_sig_aux : 'Auu____12156 . (FStar_Syntax_Syntax.eff_decl * 'Auu____12156) Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun decls m -> (

let uu____12183 = (FStar_All.pipe_right decls (FStar_Util.find_opt (fun uu____12209 -> (match (uu____12209) with
| (d, uu____12215) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)
end))))
in (match (uu____12183) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12226 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith uu____12226))
end
| FStar_Pervasives_Native.Some (md, _q) -> begin
(

let uu____12239 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (uu____12239) with
| (uu____12250, s) -> begin
(

let s1 = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s1.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, uu____12260))::((wp, uu____12262))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____12298 -> begin
(failwith "Impossible")
end))
end))
end)))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let null_wp_for_eff : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env eff_name res_u res_t -> (match ((FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' res_t (FStar_Pervasives_Native.Some (res_u)))
end
| uu____12339 -> begin
(match ((FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal' res_t (FStar_Pervasives_Native.Some (res_u)))
end
| uu____12340 -> begin
(

let eff_name1 = (norm_eff_name env eff_name)
in (

let ed = (get_effect_decl env eff_name1)
in (

let null_wp = (inst_effect_fun_with ((res_u)::[]) env ed ed.FStar_Syntax_Syntax.null_wp)
in (

let null_wp_res = (

let uu____12347 = (get_range env)
in (

let uu____12348 = (

let uu____12351 = (

let uu____12352 = (

let uu____12367 = (

let uu____12370 = (FStar_Syntax_Syntax.as_arg res_t)
in (uu____12370)::[])
in ((null_wp), (uu____12367)))
in FStar_Syntax_Syntax.Tm_app (uu____12352))
in (FStar_Syntax_Syntax.mk uu____12351))
in (uu____12348 FStar_Pervasives_Native.None uu____12347)))
in (

let uu____12376 = (

let uu____12377 = (

let uu____12386 = (FStar_Syntax_Syntax.as_arg null_wp_res)
in (uu____12386)::[])
in {FStar_Syntax_Syntax.comp_univs = (res_u)::[]; FStar_Syntax_Syntax.effect_name = eff_name1; FStar_Syntax_Syntax.result_typ = res_t; FStar_Syntax_Syntax.effect_args = uu____12377; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp uu____12376))))))
end)
end))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let effects = (

let uu___151_12397 = env.effects
in {decls = (((ne), (se.FStar_Syntax_Syntax.sigquals)))::env.effects.decls; order = uu___151_12397.order; joins = uu___151_12397.joins})
in (

let uu___152_12406 = env
in {solver = uu___152_12406.solver; range = uu___152_12406.range; curmodule = uu___152_12406.curmodule; gamma = uu___152_12406.gamma; gamma_cache = uu___152_12406.gamma_cache; modules = uu___152_12406.modules; expected_typ = uu___152_12406.expected_typ; sigtab = uu___152_12406.sigtab; is_pattern = uu___152_12406.is_pattern; instantiate_imp = uu___152_12406.instantiate_imp; effects = effects; generalize = uu___152_12406.generalize; letrecs = uu___152_12406.letrecs; top_level = uu___152_12406.top_level; check_uvars = uu___152_12406.check_uvars; use_eq = uu___152_12406.use_eq; is_iface = uu___152_12406.is_iface; admit = uu___152_12406.admit; lax = uu___152_12406.lax; lax_universes = uu___152_12406.lax_universes; failhard = uu___152_12406.failhard; nosynth = uu___152_12406.nosynth; tc_term = uu___152_12406.tc_term; type_of = uu___152_12406.type_of; universe_of = uu___152_12406.universe_of; use_bv_sorts = uu___152_12406.use_bv_sorts; qname_and_index = uu___152_12406.qname_and_index; proof_ns = uu___152_12406.proof_ns; synth = uu___152_12406.synth; is_native_tactic = uu___152_12406.is_native_tactic; identifier_info = uu___152_12406.identifier_info; tc_hooks = uu___152_12406.tc_hooks; dsenv = uu___152_12406.dsenv}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let compose_edges = (fun e1 e2 -> (

let composed_lift = (

let mlift_wp = (fun r wp1 -> (

let uu____12423 = (e1.mlift.mlift_wp r wp1)
in (e2.mlift.mlift_wp r uu____12423)))
in (

let mlift_term = (match (((e1.mlift.mlift_term), (e2.mlift.mlift_term))) with
| (FStar_Pervasives_Native.Some (l1), FStar_Pervasives_Native.Some (l2)) -> begin
FStar_Pervasives_Native.Some ((fun t wp e -> (

let uu____12513 = (e1.mlift.mlift_wp t wp)
in (

let uu____12514 = (l1 t wp e)
in (l2 t uu____12513 uu____12514)))))
end
| uu____12515 -> begin
FStar_Pervasives_Native.None
end)
in {mlift_wp = mlift_wp; mlift_term = mlift_term}))
in {msource = e1.msource; mtarget = e2.mtarget; mlift = composed_lift}))
in (

let mk_mlift_wp = (fun lift_t r wp1 -> (

let uu____12554 = (inst_tscheme lift_t)
in (match (uu____12554) with
| (uu____12561, lift_t1) -> begin
(

let uu____12563 = (

let uu____12566 = (

let uu____12567 = (

let uu____12582 = (

let uu____12585 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____12586 = (

let uu____12589 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____12589)::[])
in (uu____12585)::uu____12586))
in ((lift_t1), (uu____12582)))
in FStar_Syntax_Syntax.Tm_app (uu____12567))
in (FStar_Syntax_Syntax.mk uu____12566))
in (uu____12563 FStar_Pervasives_Native.None wp1.FStar_Syntax_Syntax.pos))
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

let mk_mlift_term = (fun lift_t r wp1 e -> (

let uu____12630 = (inst_tscheme lift_t)
in (match (uu____12630) with
| (uu____12637, lift_t1) -> begin
(

let uu____12639 = (

let uu____12642 = (

let uu____12643 = (

let uu____12658 = (

let uu____12661 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____12662 = (

let uu____12665 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____12666 = (

let uu____12669 = (FStar_Syntax_Syntax.as_arg e)
in (uu____12669)::[])
in (uu____12665)::uu____12666))
in (uu____12661)::uu____12662))
in ((lift_t1), (uu____12658)))
in FStar_Syntax_Syntax.Tm_app (uu____12643))
in (FStar_Syntax_Syntax.mk uu____12642))
in (uu____12639 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
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

let uu____12707 = (

let uu____12708 = (FStar_Ident.lid_of_path ((s)::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____12708 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.fv_to_tm uu____12707)))
in (

let arg = (bogus_term "ARG")
in (

let wp = (bogus_term "WP")
in (

let e = (bogus_term "COMP")
in (

let uu____12712 = (

let uu____12713 = (l.mlift_wp arg wp)
in (FStar_Syntax_Print.term_to_string uu____12713))
in (

let uu____12714 = (

let uu____12715 = (FStar_Util.map_opt l.mlift_term (fun l1 -> (

let uu____12733 = (l1 arg wp e)
in (FStar_Syntax_Print.term_to_string uu____12733))))
in (FStar_Util.dflt "none" uu____12715))
in (FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12712 uu____12714))))))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun uu____12759 -> (match (uu____12759) with
| (e, uu____12767) -> begin
e.FStar_Syntax_Syntax.mname
end))))
in (

let find_edge = (fun order1 uu____12786 -> (match (uu____12786) with
| (i, j) -> begin
(match ((FStar_Ident.lid_equals i j)) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)))
end
| uu____12801 -> begin
(FStar_All.pipe_right order1 (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end)
end))
in (

let order1 = (

let fold_fun = (fun order1 k -> (

let uu____12824 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (match ((FStar_Ident.lid_equals i k)) with
| true -> begin
[]
end
| uu____12835 -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (match ((FStar_Ident.lid_equals j k)) with
| true -> begin
[]
end
| uu____12844 -> begin
(

let uu____12845 = (

let uu____12854 = (find_edge order1 ((i), (k)))
in (

let uu____12857 = (find_edge order1 ((k), (j)))
in ((uu____12854), (uu____12857))))
in (match (uu____12845) with
| (FStar_Pervasives_Native.Some (e1), FStar_Pervasives_Native.Some (e2)) -> begin
(

let uu____12872 = (compose_edges e1 e2)
in (uu____12872)::[])
end
| uu____12873 -> begin
[]
end))
end))))
end))))
in (FStar_List.append order1 uu____12824)))
in (FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)))
in (

let order2 = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order1)
in ((FStar_All.pipe_right order2 (FStar_List.iter (fun edge1 -> (

let uu____12902 = ((FStar_Ident.lid_equals edge1.msource FStar_Parser_Const.effect_DIV_lid) && (

let uu____12904 = (lookup_effect_quals env edge1.mtarget)
in (FStar_All.pipe_right uu____12904 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))))
in (match (uu____12902) with
| true -> begin
(

let uu____12909 = (

let uu____12910 = (

let uu____12915 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge1.mtarget.FStar_Ident.str)
in (

let uu____12916 = (get_range env)
in ((uu____12915), (uu____12916))))
in FStar_Errors.Error (uu____12910))
in (FStar_Exn.raise uu____12909))
end
| uu____12917 -> begin
()
end)))));
(

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (match ((FStar_Ident.lid_equals i j)) with
| true -> begin
FStar_Pervasives_Native.Some (((i), ((id_edge i)), ((id_edge i))))
end
| uu____13007 -> begin
(FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (

let uu____13041 = (

let uu____13050 = (find_edge order2 ((i), (k)))
in (

let uu____13053 = (find_edge order2 ((j), (k)))
in ((uu____13050), (uu____13053))))
in (match (uu____13041) with
| (FStar_Pervasives_Native.Some (ik), FStar_Pervasives_Native.Some (jk)) -> begin
(match (bopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((k), (ik), (jk)))
end
| FStar_Pervasives_Native.Some (ub, uu____13095, uu____13096) -> begin
(

let uu____13103 = (

let uu____13108 = (

let uu____13109 = (find_edge order2 ((k), (ub)))
in (FStar_Util.is_some uu____13109))
in (

let uu____13112 = (

let uu____13113 = (find_edge order2 ((ub), (k)))
in (FStar_Util.is_some uu____13113))
in ((uu____13108), (uu____13112))))
in (match (uu____13103) with
| (true, true) -> begin
(match ((FStar_Ident.lid_equals k ub)) with
| true -> begin
((FStar_Util.print_warning "Looking multiple times at the same upper bound candidate");
bopt;
)
end
| uu____13133 -> begin
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
| uu____13148 -> begin
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

let uu___153_13221 = env.effects
in {decls = uu___153_13221.decls; order = order2; joins = joins})
in (

let uu___154_13222 = env
in {solver = uu___154_13222.solver; range = uu___154_13222.range; curmodule = uu___154_13222.curmodule; gamma = uu___154_13222.gamma; gamma_cache = uu___154_13222.gamma_cache; modules = uu___154_13222.modules; expected_typ = uu___154_13222.expected_typ; sigtab = uu___154_13222.sigtab; is_pattern = uu___154_13222.is_pattern; instantiate_imp = uu___154_13222.instantiate_imp; effects = effects; generalize = uu___154_13222.generalize; letrecs = uu___154_13222.letrecs; top_level = uu___154_13222.top_level; check_uvars = uu___154_13222.check_uvars; use_eq = uu___154_13222.use_eq; is_iface = uu___154_13222.is_iface; admit = uu___154_13222.admit; lax = uu___154_13222.lax; lax_universes = uu___154_13222.lax_universes; failhard = uu___154_13222.failhard; nosynth = uu___154_13222.nosynth; tc_term = uu___154_13222.tc_term; type_of = uu___154_13222.type_of; universe_of = uu___154_13222.universe_of; use_bv_sorts = uu___154_13222.use_bv_sorts; qname_and_index = uu___154_13222.qname_and_index; proof_ns = uu___154_13222.proof_ns; synth = uu___154_13222.synth; is_native_tactic = uu___154_13222.is_native_tactic; identifier_info = uu___154_13222.identifier_info; tc_hooks = uu___154_13222.tc_hooks; dsenv = uu___154_13222.dsenv})));
))))))))))))))
end
| uu____13223 -> begin
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
| uu____13249 -> begin
c
end)
in (FStar_Syntax_Util.comp_to_comp_typ c1)))


let rec unfold_effect_abbrev : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (comp_to_comp_typ env comp)
in (

let uu____13259 = (lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name)
in (match (uu____13259) with
| FStar_Pervasives_Native.None -> begin
c
end
| FStar_Pervasives_Native.Some (binders, cdef) -> begin
(

let uu____13276 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (uu____13276) with
| (binders1, cdef1) -> begin
((match ((Prims.op_disEquality (FStar_List.length binders1) ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))) with
| true -> begin
(

let uu____13294 = (

let uu____13295 = (

let uu____13300 = (

let uu____13301 = (FStar_Util.string_of_int (FStar_List.length binders1))
in (

let uu____13306 = (FStar_Util.string_of_int ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))
in (

let uu____13313 = (

let uu____13314 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Print.comp_to_string uu____13314))
in (FStar_Util.format3 "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s" uu____13301 uu____13306 uu____13313))))
in ((uu____13300), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____13295))
in (FStar_Exn.raise uu____13294))
end
| uu____13315 -> begin
()
end);
(

let inst1 = (

let uu____13319 = (

let uu____13328 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (uu____13328)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun uu____13345 uu____13346 -> (match (((uu____13345), (uu____13346))) with
| ((x, uu____13368), (t, uu____13370)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders1 uu____13319))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst1 cdef1)
in (

let c2 = (

let uu____13389 = (

let uu___155_13390 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = uu___155_13390.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___155_13390.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___155_13390.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___155_13390.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right uu____13389 FStar_Syntax_Syntax.mk_Comp))
in (unfold_effect_abbrev env c2))));
)
end))
end))))


let effect_repr_aux : Prims.bool  ->  env  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun only_reifiable env c u_c -> (

let effect_name = (norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (

let uu____13416 = (effect_decl_opt env effect_name)
in (match (uu____13416) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____13449 = (only_reifiable && (

let uu____13451 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____13451))))
in (match (uu____13449) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13460 -> begin
(match (ed.FStar_Syntax_Syntax.repr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| uu____13467 -> begin
(

let c1 = (unfold_effect_abbrev env c)
in (

let res_typ = c1.FStar_Syntax_Syntax.result_typ
in (

let wp = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (hd1)::uu____13486 -> begin
hd1
end
| [] -> begin
(

let name = (FStar_Ident.string_of_lid effect_name)
in (

let message = (

let uu____13515 = (FStar_Util.format1 "Not enough arguments for effect %s. " name)
in (Prims.strcat uu____13515 (Prims.strcat "This usually happens when you use a partially applied DM4F effect, " "like [TAC int] instead of [Tac int].")))
in (

let uu____13516 = (

let uu____13517 = (

let uu____13522 = (get_range env)
in ((message), (uu____13522)))
in FStar_Errors.Error (uu____13517))
in (FStar_Exn.raise uu____13516))))
end)
in (

let repr = (inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____13532 = (

let uu____13535 = (get_range env)
in (

let uu____13536 = (

let uu____13539 = (

let uu____13540 = (

let uu____13555 = (

let uu____13558 = (FStar_Syntax_Syntax.as_arg res_typ)
in (uu____13558)::(wp)::[])
in ((repr), (uu____13555)))
in FStar_Syntax_Syntax.Tm_app (uu____13540))
in (FStar_Syntax_Syntax.mk uu____13539))
in (uu____13536 FStar_Pervasives_Native.None uu____13535)))
in FStar_Pervasives_Native.Some (uu____13532))))))
end)
end))
end))))


let effect_repr : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (

let uu____13610 = (

let uu____13611 = (

let uu____13616 = (

let uu____13617 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format1 "Effect %s cannot be reified" uu____13617))
in (

let uu____13618 = (get_range env)
in ((uu____13616), (uu____13618))))
in FStar_Errors.Error (uu____13611))
in (FStar_Exn.raise uu____13610)))
in (

let uu____13619 = (effect_repr_aux true env c u_c)
in (match (uu____13619) with
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
| uu____13659 -> begin
false
end))


let is_reifiable_function : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____13668 = (

let uu____13669 = (FStar_Syntax_Subst.compress t)
in uu____13669.FStar_Syntax_Syntax.n)
in (match (uu____13668) with
| FStar_Syntax_Syntax.Tm_arrow (uu____13672, c) -> begin
(is_reifiable_comp env c)
end
| uu____13690 -> begin
false
end)))


let push_in_gamma : env  ->  binding  ->  env = (fun env s -> (

let rec push1 = (fun x rest -> (match (rest) with
| (Binding_sig (uu____13714))::uu____13715 -> begin
(x)::rest
end
| (Binding_sig_inst (uu____13724))::uu____13725 -> begin
(x)::rest
end
| [] -> begin
(x)::[]
end
| (local)::rest1 -> begin
(

let uu____13740 = (push1 x rest1)
in (local)::uu____13740)
end))
in ((env.tc_hooks.tc_push_in_gamma_hook env s);
(

let uu___156_13744 = env
in (

let uu____13745 = (push1 s env.gamma)
in {solver = uu___156_13744.solver; range = uu___156_13744.range; curmodule = uu___156_13744.curmodule; gamma = uu____13745; gamma_cache = uu___156_13744.gamma_cache; modules = uu___156_13744.modules; expected_typ = uu___156_13744.expected_typ; sigtab = uu___156_13744.sigtab; is_pattern = uu___156_13744.is_pattern; instantiate_imp = uu___156_13744.instantiate_imp; effects = uu___156_13744.effects; generalize = uu___156_13744.generalize; letrecs = uu___156_13744.letrecs; top_level = uu___156_13744.top_level; check_uvars = uu___156_13744.check_uvars; use_eq = uu___156_13744.use_eq; is_iface = uu___156_13744.is_iface; admit = uu___156_13744.admit; lax = uu___156_13744.lax; lax_universes = uu___156_13744.lax_universes; failhard = uu___156_13744.failhard; nosynth = uu___156_13744.nosynth; tc_term = uu___156_13744.tc_term; type_of = uu___156_13744.type_of; universe_of = uu___156_13744.universe_of; use_bv_sorts = uu___156_13744.use_bv_sorts; qname_and_index = uu___156_13744.qname_and_index; proof_ns = uu___156_13744.proof_ns; synth = uu___156_13744.synth; is_native_tactic = uu___156_13744.is_native_tactic; identifier_info = uu___156_13744.identifier_info; tc_hooks = uu___156_13744.tc_hooks; dsenv = uu___156_13744.dsenv}));
)))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env1 = (push_in_gamma env (Binding_sig ((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))))
in (build_lattice env1 s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env1 = (push_in_gamma env (Binding_sig_inst ((((FStar_Syntax_Util.lids_of_sigelt s)), (s), (us)))))
in (build_lattice env1 s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let uu___157_13782 = env
in {solver = uu___157_13782.solver; range = uu___157_13782.range; curmodule = uu___157_13782.curmodule; gamma = (b)::env.gamma; gamma_cache = uu___157_13782.gamma_cache; modules = uu___157_13782.modules; expected_typ = uu___157_13782.expected_typ; sigtab = uu___157_13782.sigtab; is_pattern = uu___157_13782.is_pattern; instantiate_imp = uu___157_13782.instantiate_imp; effects = uu___157_13782.effects; generalize = uu___157_13782.generalize; letrecs = uu___157_13782.letrecs; top_level = uu___157_13782.top_level; check_uvars = uu___157_13782.check_uvars; use_eq = uu___157_13782.use_eq; is_iface = uu___157_13782.is_iface; admit = uu___157_13782.admit; lax = uu___157_13782.lax; lax_universes = uu___157_13782.lax_universes; failhard = uu___157_13782.failhard; nosynth = uu___157_13782.nosynth; tc_term = uu___157_13782.tc_term; type_of = uu___157_13782.type_of; universe_of = uu___157_13782.universe_of; use_bv_sorts = uu___157_13782.use_bv_sorts; qname_and_index = uu___157_13782.qname_and_index; proof_ns = uu___157_13782.proof_ns; synth = uu___157_13782.synth; is_native_tactic = uu___157_13782.is_native_tactic; identifier_info = uu___157_13782.identifier_info; tc_hooks = uu___157_13782.tc_hooks; dsenv = uu___157_13782.dsenv}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let pop_bv : env  ->  (FStar_Syntax_Syntax.bv * env) FStar_Pervasives_Native.option = (fun env -> (match (env.gamma) with
| (Binding_var (x))::rest -> begin
FStar_Pervasives_Native.Some (((x), ((

let uu___158_13816 = env
in {solver = uu___158_13816.solver; range = uu___158_13816.range; curmodule = uu___158_13816.curmodule; gamma = rest; gamma_cache = uu___158_13816.gamma_cache; modules = uu___158_13816.modules; expected_typ = uu___158_13816.expected_typ; sigtab = uu___158_13816.sigtab; is_pattern = uu___158_13816.is_pattern; instantiate_imp = uu___158_13816.instantiate_imp; effects = uu___158_13816.effects; generalize = uu___158_13816.generalize; letrecs = uu___158_13816.letrecs; top_level = uu___158_13816.top_level; check_uvars = uu___158_13816.check_uvars; use_eq = uu___158_13816.use_eq; is_iface = uu___158_13816.is_iface; admit = uu___158_13816.admit; lax = uu___158_13816.lax; lax_universes = uu___158_13816.lax_universes; failhard = uu___158_13816.failhard; nosynth = uu___158_13816.nosynth; tc_term = uu___158_13816.tc_term; type_of = uu___158_13816.type_of; universe_of = uu___158_13816.universe_of; use_bv_sorts = uu___158_13816.use_bv_sorts; qname_and_index = uu___158_13816.qname_and_index; proof_ns = uu___158_13816.proof_ns; synth = uu___158_13816.synth; is_native_tactic = uu___158_13816.is_native_tactic; identifier_info = uu___158_13816.identifier_info; tc_hooks = uu___158_13816.tc_hooks; dsenv = uu___158_13816.dsenv}))))
end
| uu____13817 -> begin
FStar_Pervasives_Native.None
end))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env1 uu____13841 -> (match (uu____13841) with
| (x, uu____13847) -> begin
(push_bv env1 x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x1) -> begin
(

let x2 = (

let uu___159_13877 = x1
in {FStar_Syntax_Syntax.ppname = uu___159_13877.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___159_13877.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)})
in Binding_var (x2))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> ((add_sigelts env m.FStar_Syntax_Syntax.exports);
(

let uu___160_13912 = env
in {solver = uu___160_13912.solver; range = uu___160_13912.range; curmodule = uu___160_13912.curmodule; gamma = []; gamma_cache = uu___160_13912.gamma_cache; modules = (m)::env.modules; expected_typ = FStar_Pervasives_Native.None; sigtab = uu___160_13912.sigtab; is_pattern = uu___160_13912.is_pattern; instantiate_imp = uu___160_13912.instantiate_imp; effects = uu___160_13912.effects; generalize = uu___160_13912.generalize; letrecs = uu___160_13912.letrecs; top_level = uu___160_13912.top_level; check_uvars = uu___160_13912.check_uvars; use_eq = uu___160_13912.use_eq; is_iface = uu___160_13912.is_iface; admit = uu___160_13912.admit; lax = uu___160_13912.lax; lax_universes = uu___160_13912.lax_universes; failhard = uu___160_13912.failhard; nosynth = uu___160_13912.nosynth; tc_term = uu___160_13912.tc_term; type_of = uu___160_13912.type_of; universe_of = uu___160_13912.universe_of; use_bv_sorts = uu___160_13912.use_bv_sorts; qname_and_index = uu___160_13912.qname_and_index; proof_ns = uu___160_13912.proof_ns; synth = uu___160_13912.synth; is_native_tactic = uu___160_13912.is_native_tactic; identifier_info = uu___160_13912.identifier_info; tc_hooks = uu___160_13912.tc_hooks; dsenv = uu___160_13912.dsenv});
))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env1 x -> (push_local_binding env1 (Binding_univ (x)))) env xs))


let open_universes_in : env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term Prims.list  ->  (env * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term Prims.list) = (fun env uvs terms -> (

let uu____13949 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____13949) with
| (univ_subst, univ_vars) -> begin
(

let env' = (push_univ_vars env univ_vars)
in (

let uu____13977 = (FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms)
in ((env'), (univ_vars), (uu____13977))))
end)))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let uu___161_13992 = env
in {solver = uu___161_13992.solver; range = uu___161_13992.range; curmodule = uu___161_13992.curmodule; gamma = uu___161_13992.gamma; gamma_cache = uu___161_13992.gamma_cache; modules = uu___161_13992.modules; expected_typ = FStar_Pervasives_Native.Some (t); sigtab = uu___161_13992.sigtab; is_pattern = uu___161_13992.is_pattern; instantiate_imp = uu___161_13992.instantiate_imp; effects = uu___161_13992.effects; generalize = uu___161_13992.generalize; letrecs = uu___161_13992.letrecs; top_level = uu___161_13992.top_level; check_uvars = uu___161_13992.check_uvars; use_eq = false; is_iface = uu___161_13992.is_iface; admit = uu___161_13992.admit; lax = uu___161_13992.lax; lax_universes = uu___161_13992.lax_universes; failhard = uu___161_13992.failhard; nosynth = uu___161_13992.nosynth; tc_term = uu___161_13992.tc_term; type_of = uu___161_13992.type_of; universe_of = uu___161_13992.universe_of; use_bv_sorts = uu___161_13992.use_bv_sorts; qname_and_index = uu___161_13992.qname_and_index; proof_ns = uu___161_13992.proof_ns; synth = uu___161_13992.synth; is_native_tactic = uu___161_13992.is_native_tactic; identifier_info = uu___161_13992.identifier_info; tc_hooks = uu___161_13992.tc_hooks; dsenv = uu___161_13992.dsenv}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun env -> (match (env.expected_typ) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) = (fun env_ -> (

let uu____14018 = (expected_typ env_)
in (((

let uu___162_14024 = env_
in {solver = uu___162_14024.solver; range = uu___162_14024.range; curmodule = uu___162_14024.curmodule; gamma = uu___162_14024.gamma; gamma_cache = uu___162_14024.gamma_cache; modules = uu___162_14024.modules; expected_typ = FStar_Pervasives_Native.None; sigtab = uu___162_14024.sigtab; is_pattern = uu___162_14024.is_pattern; instantiate_imp = uu___162_14024.instantiate_imp; effects = uu___162_14024.effects; generalize = uu___162_14024.generalize; letrecs = uu___162_14024.letrecs; top_level = uu___162_14024.top_level; check_uvars = uu___162_14024.check_uvars; use_eq = false; is_iface = uu___162_14024.is_iface; admit = uu___162_14024.admit; lax = uu___162_14024.lax; lax_universes = uu___162_14024.lax_universes; failhard = uu___162_14024.failhard; nosynth = uu___162_14024.nosynth; tc_term = uu___162_14024.tc_term; type_of = uu___162_14024.type_of; universe_of = uu___162_14024.universe_of; use_bv_sorts = uu___162_14024.use_bv_sorts; qname_and_index = uu___162_14024.qname_and_index; proof_ns = uu___162_14024.proof_ns; synth = uu___162_14024.synth; is_native_tactic = uu___162_14024.is_native_tactic; identifier_info = uu___162_14024.identifier_info; tc_hooks = uu___162_14024.tc_hooks; dsenv = uu___162_14024.dsenv})), (uu____14018))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = (match ((FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Parser_Const.prims_lid)) with
| true -> begin
(

let uu____14039 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun uu___139_14049 -> (match (uu___139_14049) with
| Binding_sig (uu____14052, se) -> begin
(se)::[]
end
| uu____14058 -> begin
[]
end))))
in (FStar_All.pipe_right uu____14039 FStar_List.rev))
end
| uu____14063 -> begin
m.FStar_Syntax_Syntax.exports
end)
in ((add_sigelts env sigs);
(

let uu___163_14065 = env
in {solver = uu___163_14065.solver; range = uu___163_14065.range; curmodule = empty_lid; gamma = []; gamma_cache = uu___163_14065.gamma_cache; modules = (m)::env.modules; expected_typ = uu___163_14065.expected_typ; sigtab = uu___163_14065.sigtab; is_pattern = uu___163_14065.is_pattern; instantiate_imp = uu___163_14065.instantiate_imp; effects = uu___163_14065.effects; generalize = uu___163_14065.generalize; letrecs = uu___163_14065.letrecs; top_level = uu___163_14065.top_level; check_uvars = uu___163_14065.check_uvars; use_eq = uu___163_14065.use_eq; is_iface = uu___163_14065.is_iface; admit = uu___163_14065.admit; lax = uu___163_14065.lax; lax_universes = uu___163_14065.lax_universes; failhard = uu___163_14065.failhard; nosynth = uu___163_14065.nosynth; tc_term = uu___163_14065.tc_term; type_of = uu___163_14065.type_of; universe_of = uu___163_14065.universe_of; use_bv_sorts = uu___163_14065.use_bv_sorts; qname_and_index = uu___163_14065.qname_and_index; proof_ns = uu___163_14065.proof_ns; synth = uu___163_14065.synth; is_native_tactic = uu___163_14065.is_native_tactic; identifier_info = uu___163_14065.identifier_info; tc_hooks = uu___163_14065.tc_hooks; dsenv = uu___163_14065.dsenv});
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
| (Binding_univ (uu____14147))::tl1 -> begin
(aux out tl1)
end
| (Binding_lid (uu____14151, (uu____14152, t)))::tl1 -> begin
(

let uu____14167 = (

let uu____14174 = (FStar_Syntax_Free.uvars t)
in (ext out uu____14174))
in (aux uu____14167 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____14181; FStar_Syntax_Syntax.index = uu____14182; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____14189 = (

let uu____14196 = (FStar_Syntax_Free.uvars t)
in (ext out uu____14196))
in (aux uu____14189 tl1))
end
| (Binding_sig (uu____14203))::uu____14204 -> begin
out
end
| (Binding_sig_inst (uu____14213))::uu____14214 -> begin
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
| (Binding_sig_inst (uu____14270))::tl1 -> begin
(aux out tl1)
end
| (Binding_univ (uu____14282))::tl1 -> begin
(aux out tl1)
end
| (Binding_lid (uu____14286, (uu____14287, t)))::tl1 -> begin
(

let uu____14302 = (

let uu____14305 = (FStar_Syntax_Free.univs t)
in (ext out uu____14305))
in (aux uu____14302 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____14308; FStar_Syntax_Syntax.index = uu____14309; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____14316 = (

let uu____14319 = (FStar_Syntax_Free.univs t)
in (ext out uu____14319))
in (aux uu____14316 tl1))
end
| (Binding_sig (uu____14322))::uu____14323 -> begin
out
end))
in (aux no_univs env.gamma)))))


let univnames : env  ->  FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set = (fun env -> (

let no_univ_names = FStar_Syntax_Syntax.no_universe_names
in (

let ext = (fun out uvs -> (FStar_Util.fifo_set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (uu____14377))::tl1 -> begin
(aux out tl1)
end
| (Binding_univ (uname))::tl1 -> begin
(

let uu____14393 = (FStar_Util.fifo_set_add uname out)
in (aux uu____14393 tl1))
end
| (Binding_lid (uu____14396, (uu____14397, t)))::tl1 -> begin
(

let uu____14412 = (

let uu____14415 = (FStar_Syntax_Free.univnames t)
in (ext out uu____14415))
in (aux uu____14412 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____14418; FStar_Syntax_Syntax.index = uu____14419; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____14426 = (

let uu____14429 = (FStar_Syntax_Free.univnames t)
in (ext out uu____14429))
in (aux uu____14426 tl1))
end
| (Binding_sig (uu____14432))::uu____14433 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu___140_14458 -> (match (uu___140_14458) with
| Binding_var (x) -> begin
(x)::[]
end
| Binding_lid (uu____14462) -> begin
[]
end
| Binding_sig (uu____14467) -> begin
[]
end
| Binding_univ (uu____14474) -> begin
[]
end
| Binding_sig_inst (uu____14475) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____14492 = (

let uu____14495 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right uu____14495 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right uu____14492 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let print_gamma : env  ->  Prims.unit = (fun env -> (

let uu____14520 = (

let uu____14521 = (FStar_All.pipe_right env.gamma (FStar_List.map (fun uu___141_14531 -> (match (uu___141_14531) with
| Binding_var (x) -> begin
(

let uu____14533 = (FStar_Syntax_Print.bv_to_string x)
in (Prims.strcat "Binding_var " uu____14533))
end
| Binding_univ (u) -> begin
(Prims.strcat "Binding_univ " u.FStar_Ident.idText)
end
| Binding_lid (l, uu____14536) -> begin
(

let uu____14537 = (FStar_Ident.string_of_lid l)
in (Prims.strcat "Binding_lid " uu____14537))
end
| Binding_sig (ls, uu____14539) -> begin
(

let uu____14544 = (

let uu____14545 = (FStar_All.pipe_right ls (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____14545 (FStar_String.concat ", ")))
in (Prims.strcat "Binding_sig " uu____14544))
end
| Binding_sig_inst (ls, uu____14555, uu____14556) -> begin
(

let uu____14561 = (

let uu____14562 = (FStar_All.pipe_right ls (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____14562 (FStar_String.concat ", ")))
in (Prims.strcat "Binding_sig_inst " uu____14561))
end))))
in (FStar_All.pipe_right uu____14521 (FStar_String.concat "::\n")))
in (FStar_All.pipe_right uu____14520 (FStar_Util.print1 "%s\n"))))


let eq_gamma : env  ->  env  ->  Prims.bool = (fun env env' -> (

let uu____14581 = (FStar_Util.physical_equality env.gamma env'.gamma)
in (match (uu____14581) with
| true -> begin
true
end
| uu____14584 -> begin
(

let g = (all_binders env)
in (

let g' = (all_binders env')
in ((Prims.op_Equality (FStar_List.length g) (FStar_List.length g')) && (FStar_List.forall2 (fun uu____14609 uu____14610 -> (match (((uu____14609), (uu____14610))) with
| ((b1, uu____14628), (b2, uu____14630)) -> begin
(FStar_Syntax_Syntax.bv_eq b1 b2)
end)) g g'))))
end)))


let fold_env : 'a . env  ->  ('a  ->  binding  ->  'a)  ->  'a  ->  'a = (fun env f a -> (FStar_List.fold_right (fun e a1 -> (f a1 e)) env.gamma a))


let string_of_delta_level : delta_level  ->  Prims.string = (fun uu___142_14677 -> (match (uu___142_14677) with
| NoDelta -> begin
"NoDelta"
end
| Inlining -> begin
"Inlining"
end
| Eager_unfolding_only -> begin
"Eager_unfolding_only"
end
| Unfold (uu____14678) -> begin
"Unfold _"
end
| UnfoldTac -> begin
"UnfoldTac"
end))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys uu___143_14697 -> (match (uu___143_14697) with
| Binding_sig (lids, uu____14703) -> begin
(FStar_List.append lids keys)
end
| uu____14708 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun uu____14714 v1 keys1 -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)) keys)))


let should_enc_path : env  ->  Prims.string Prims.list  ->  Prims.bool = (fun env path -> (

let rec list_prefix = (fun xs ys -> (match (((xs), (ys))) with
| ([], uu____14750) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((Prims.op_Equality x y) && (list_prefix xs1 ys1))
end
| (uu____14769, uu____14770) -> begin
false
end))
in (

let rec should_enc_path' = (fun pns path1 -> (match (pns) with
| [] -> begin
true
end
| ((p, b))::pns1 -> begin
(

let uu____14807 = (list_prefix p path1)
in (match (uu____14807) with
| true -> begin
b
end
| uu____14808 -> begin
(should_enc_path' pns1 path1)
end))
end))
in (should_enc_path' (FStar_List.flatten env.proof_ns) path))))


let should_enc_lid : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____14821 = (FStar_Ident.path_of_lid lid)
in (should_enc_path env uu____14821)))


let cons_proof_ns : Prims.bool  ->  env  ->  name_prefix  ->  env = (fun b e path -> (match (e.proof_ns) with
| [] -> begin
(failwith "empty proof_ns stack!")
end
| (pns)::rest -> begin
(

let pns' = (((path), (b)))::pns
in (

let uu___164_14851 = e
in {solver = uu___164_14851.solver; range = uu___164_14851.range; curmodule = uu___164_14851.curmodule; gamma = uu___164_14851.gamma; gamma_cache = uu___164_14851.gamma_cache; modules = uu___164_14851.modules; expected_typ = uu___164_14851.expected_typ; sigtab = uu___164_14851.sigtab; is_pattern = uu___164_14851.is_pattern; instantiate_imp = uu___164_14851.instantiate_imp; effects = uu___164_14851.effects; generalize = uu___164_14851.generalize; letrecs = uu___164_14851.letrecs; top_level = uu___164_14851.top_level; check_uvars = uu___164_14851.check_uvars; use_eq = uu___164_14851.use_eq; is_iface = uu___164_14851.is_iface; admit = uu___164_14851.admit; lax = uu___164_14851.lax; lax_universes = uu___164_14851.lax_universes; failhard = uu___164_14851.failhard; nosynth = uu___164_14851.nosynth; tc_term = uu___164_14851.tc_term; type_of = uu___164_14851.type_of; universe_of = uu___164_14851.universe_of; use_bv_sorts = uu___164_14851.use_bv_sorts; qname_and_index = uu___164_14851.qname_and_index; proof_ns = (pns')::rest; synth = uu___164_14851.synth; is_native_tactic = uu___164_14851.is_native_tactic; identifier_info = uu___164_14851.identifier_info; tc_hooks = uu___164_14851.tc_hooks; dsenv = uu___164_14851.dsenv}))
end))


let add_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns true e path))


let rem_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns false e path))


let push_proof_ns : env  ->  env = (fun e -> (

let uu___165_14878 = e
in {solver = uu___165_14878.solver; range = uu___165_14878.range; curmodule = uu___165_14878.curmodule; gamma = uu___165_14878.gamma; gamma_cache = uu___165_14878.gamma_cache; modules = uu___165_14878.modules; expected_typ = uu___165_14878.expected_typ; sigtab = uu___165_14878.sigtab; is_pattern = uu___165_14878.is_pattern; instantiate_imp = uu___165_14878.instantiate_imp; effects = uu___165_14878.effects; generalize = uu___165_14878.generalize; letrecs = uu___165_14878.letrecs; top_level = uu___165_14878.top_level; check_uvars = uu___165_14878.check_uvars; use_eq = uu___165_14878.use_eq; is_iface = uu___165_14878.is_iface; admit = uu___165_14878.admit; lax = uu___165_14878.lax; lax_universes = uu___165_14878.lax_universes; failhard = uu___165_14878.failhard; nosynth = uu___165_14878.nosynth; tc_term = uu___165_14878.tc_term; type_of = uu___165_14878.type_of; universe_of = uu___165_14878.universe_of; use_bv_sorts = uu___165_14878.use_bv_sorts; qname_and_index = uu___165_14878.qname_and_index; proof_ns = ([])::e.proof_ns; synth = uu___165_14878.synth; is_native_tactic = uu___165_14878.is_native_tactic; identifier_info = uu___165_14878.identifier_info; tc_hooks = uu___165_14878.tc_hooks; dsenv = uu___165_14878.dsenv}))


let pop_proof_ns : env  ->  env = (fun e -> (match (e.proof_ns) with
| [] -> begin
(failwith "empty proof_ns stack!")
end
| (uu____14893)::rest -> begin
(

let uu___166_14897 = e
in {solver = uu___166_14897.solver; range = uu___166_14897.range; curmodule = uu___166_14897.curmodule; gamma = uu___166_14897.gamma; gamma_cache = uu___166_14897.gamma_cache; modules = uu___166_14897.modules; expected_typ = uu___166_14897.expected_typ; sigtab = uu___166_14897.sigtab; is_pattern = uu___166_14897.is_pattern; instantiate_imp = uu___166_14897.instantiate_imp; effects = uu___166_14897.effects; generalize = uu___166_14897.generalize; letrecs = uu___166_14897.letrecs; top_level = uu___166_14897.top_level; check_uvars = uu___166_14897.check_uvars; use_eq = uu___166_14897.use_eq; is_iface = uu___166_14897.is_iface; admit = uu___166_14897.admit; lax = uu___166_14897.lax; lax_universes = uu___166_14897.lax_universes; failhard = uu___166_14897.failhard; nosynth = uu___166_14897.nosynth; tc_term = uu___166_14897.tc_term; type_of = uu___166_14897.type_of; universe_of = uu___166_14897.universe_of; use_bv_sorts = uu___166_14897.use_bv_sorts; qname_and_index = uu___166_14897.qname_and_index; proof_ns = rest; synth = uu___166_14897.synth; is_native_tactic = uu___166_14897.is_native_tactic; identifier_info = uu___166_14897.identifier_info; tc_hooks = uu___166_14897.tc_hooks; dsenv = uu___166_14897.dsenv})
end))


let get_proof_ns : env  ->  proof_namespace = (fun e -> e.proof_ns)


let set_proof_ns : proof_namespace  ->  env  ->  env = (fun ns e -> (

let uu___167_14910 = e
in {solver = uu___167_14910.solver; range = uu___167_14910.range; curmodule = uu___167_14910.curmodule; gamma = uu___167_14910.gamma; gamma_cache = uu___167_14910.gamma_cache; modules = uu___167_14910.modules; expected_typ = uu___167_14910.expected_typ; sigtab = uu___167_14910.sigtab; is_pattern = uu___167_14910.is_pattern; instantiate_imp = uu___167_14910.instantiate_imp; effects = uu___167_14910.effects; generalize = uu___167_14910.generalize; letrecs = uu___167_14910.letrecs; top_level = uu___167_14910.top_level; check_uvars = uu___167_14910.check_uvars; use_eq = uu___167_14910.use_eq; is_iface = uu___167_14910.is_iface; admit = uu___167_14910.admit; lax = uu___167_14910.lax; lax_universes = uu___167_14910.lax_universes; failhard = uu___167_14910.failhard; nosynth = uu___167_14910.nosynth; tc_term = uu___167_14910.tc_term; type_of = uu___167_14910.type_of; universe_of = uu___167_14910.universe_of; use_bv_sorts = uu___167_14910.use_bv_sorts; qname_and_index = uu___167_14910.qname_and_index; proof_ns = ns; synth = uu___167_14910.synth; is_native_tactic = uu___167_14910.is_native_tactic; identifier_info = uu___167_14910.identifier_info; tc_hooks = uu___167_14910.tc_hooks; dsenv = uu___167_14910.dsenv}))


let string_of_proof_ns : env  ->  Prims.string = (fun env -> (

let string_of_proof_ns' = (fun pns -> (

let uu____14939 = (FStar_List.map (fun fpns -> (

let uu____14961 = (

let uu____14962 = (

let uu____14963 = (FStar_List.map (fun uu____14975 -> (match (uu____14975) with
| (p, b) -> begin
(Prims.strcat (match (b) with
| true -> begin
"+"
end
| uu____14988 -> begin
"-"
end) (FStar_String.concat "." p))
end)) fpns)
in (FStar_String.concat "," uu____14963))
in (Prims.strcat uu____14962 "]"))
in (Prims.strcat "[" uu____14961))) pns)
in (FStar_String.concat ";" uu____14939)))
in (string_of_proof_ns' env.proof_ns)))


let dummy_solver : solver_t = {init = (fun uu____14991 -> ()); push = (fun uu____14993 -> ()); pop = (fun uu____14995 -> ()); encode_modul = (fun uu____14998 uu____14999 -> ()); encode_sig = (fun uu____15002 uu____15003 -> ()); preprocess = (fun e g -> (

let uu____15009 = (

let uu____15016 = (FStar_Options.peek ())
in ((e), (g), (uu____15016)))
in (uu____15009)::[])); solve = (fun uu____15032 uu____15033 uu____15034 -> ()); is_trivial = (fun uu____15041 uu____15042 -> false); finish = (fun uu____15044 -> ()); refresh = (fun uu____15046 -> ())}





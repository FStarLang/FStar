
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
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; lax : Prims.bool; lax_universes : Prims.bool; failhard : Prims.bool; nosynth : Prims.bool; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool; qname_and_index : (FStar_Ident.lident * Prims.int) FStar_Pervasives_Native.option; proof_ns : proof_namespace; synth : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term; is_native_tactic : FStar_Ident.lid  ->  Prims.bool; identifier_info : FStar_TypeChecker_Common.id_info_table FStar_ST.ref; dsenv : FStar_ToSyntax_Env.env} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; preprocess : env  ->  goal  ->  (env * goal * FStar_Options.optionstate) Prims.list; solve : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : (FStar_Syntax_Syntax.universe Prims.list * FStar_TypeChecker_Common.univ_ineq Prims.list); implicits : (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list}


let __proj__Mkenv__item__solver : env  ->  solver_t = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__solver
end))


let __proj__Mkenv__item__range : env  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__range
end))


let __proj__Mkenv__item__curmodule : env  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__curmodule
end))


let __proj__Mkenv__item__gamma : env  ->  binding Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__gamma
end))


let __proj__Mkenv__item__gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__gamma_cache
end))


let __proj__Mkenv__item__modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__modules
end))


let __proj__Mkenv__item__expected_typ : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__expected_typ
end))


let __proj__Mkenv__item__sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__sigtab
end))


let __proj__Mkenv__item__is_pattern : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__is_pattern
end))


let __proj__Mkenv__item__instantiate_imp : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__instantiate_imp
end))


let __proj__Mkenv__item__effects : env  ->  effects = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__effects
end))


let __proj__Mkenv__item__generalize : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__generalize
end))


let __proj__Mkenv__item__letrecs : env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__letrecs
end))


let __proj__Mkenv__item__top_level : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__top_level
end))


let __proj__Mkenv__item__check_uvars : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__check_uvars
end))


let __proj__Mkenv__item__use_eq : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__use_eq
end))


let __proj__Mkenv__item__is_iface : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__is_iface
end))


let __proj__Mkenv__item__admit : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__admit
end))


let __proj__Mkenv__item__lax : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__lax
end))


let __proj__Mkenv__item__lax_universes : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__lax_universes
end))


let __proj__Mkenv__item__failhard : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__failhard
end))


let __proj__Mkenv__item__nosynth : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__nosynth
end))


let __proj__Mkenv__item__type_of : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t) = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__type_of
end))


let __proj__Mkenv__item__universe_of : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__universe_of
end))


let __proj__Mkenv__item__use_bv_sorts : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__use_bv_sorts
end))


let __proj__Mkenv__item__qname_and_index : env  ->  (FStar_Ident.lident * Prims.int) FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__qname_and_index
end))


let __proj__Mkenv__item__proof_ns : env  ->  proof_namespace = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__proof_ns
end))


let __proj__Mkenv__item__synth : env  ->  env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__synth
end))


let __proj__Mkenv__item__is_native_tactic : env  ->  FStar_Ident.lid  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__is_native_tactic
end))


let __proj__Mkenv__item__identifier_info : env  ->  FStar_TypeChecker_Common.id_info_table FStar_ST.ref = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
__fname__identifier_info
end))


let __proj__Mkenv__item__dsenv : env  ->  FStar_ToSyntax_Env.env = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; dsenv = __fname__dsenv} -> begin
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


type implicits =
(Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list


type env_t =
env


type sigtable =
FStar_Syntax_Syntax.sigelt FStar_Util.smap


let should_verify : env  ->  Prims.bool = (fun env -> (((not (env.lax)) && (not (env.admit))) && (FStar_Options.should_verify env.curmodule.FStar_Ident.str)))


let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match (((d), (q))) with
| (NoDelta, uu____4413) -> begin
true
end
| (Eager_unfolding_only, FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____4414), FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____4415), FStar_Syntax_Syntax.Visible_default) -> begin
true
end
| (Inlining, FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| uu____4416 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab : 'Auu____4425 . Prims.unit  ->  'Auu____4425 FStar_Util.smap = (fun uu____4431 -> (FStar_Util.smap_create default_table_size))


let new_gamma_cache : 'Auu____4436 . Prims.unit  ->  'Auu____4436 FStar_Util.smap = (fun uu____4442 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (

let uu____4491 = (new_gamma_cache ())
in (

let uu____4494 = (new_sigtab ())
in (

let uu____4497 = (

let uu____4498 = (FStar_Options.using_facts_from ())
in (match (uu____4498) with
| FStar_Pervasives_Native.Some (ns) -> begin
(

let uu____4508 = (

let uu____4517 = (FStar_List.map (fun s -> (((FStar_Ident.path_of_text s)), (true))) ns)
in (FStar_List.append uu____4517 (((([]), (false)))::[])))
in (uu____4508)::[])
end
| FStar_Pervasives_Native.None -> begin
([])::[]
end))
in (

let uu____4590 = (FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty)
in (

let uu____4593 = (FStar_ToSyntax_Env.empty_env ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = uu____4491; modules = []; expected_typ = FStar_Pervasives_Native.None; sigtab = uu____4494; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; failhard = false; nosynth = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = FStar_Pervasives_Native.None; proof_ns = uu____4497; synth = (fun e g tau -> (failwith "no synthesizer available")); is_native_tactic = (fun uu____4625 -> false); identifier_info = uu____4590; dsenv = uu____4593}))))))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


let query_indices : (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let push_query_indices : Prims.unit  ->  Prims.unit = (fun uu____4696 -> (

let uu____4697 = (FStar_ST.op_Bang query_indices)
in (match (uu____4697) with
| [] -> begin
(failwith "Empty query indices!")
end
| uu____4754 -> begin
(

let uu____4763 = (

let uu____4772 = (

let uu____4779 = (FStar_ST.op_Bang query_indices)
in (FStar_List.hd uu____4779))
in (

let uu____4836 = (FStar_ST.op_Bang query_indices)
in (uu____4772)::uu____4836))
in (FStar_ST.op_Colon_Equals query_indices uu____4763))
end)))


let pop_query_indices : Prims.unit  ->  Prims.unit = (fun uu____4938 -> (

let uu____4939 = (FStar_ST.op_Bang query_indices)
in (match (uu____4939) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals query_indices tl1)
end)))


let add_query_index : (FStar_Ident.lident * Prims.int)  ->  Prims.unit = (fun uu____5067 -> (match (uu____5067) with
| (l, n1) -> begin
(

let uu____5074 = (FStar_ST.op_Bang query_indices)
in (match (uu____5074) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals query_indices (((((l), (n1)))::hd1)::tl1))
end
| uu____5199 -> begin
(failwith "Empty query indices")
end))
end))


let peek_query_indices : Prims.unit  ->  (FStar_Ident.lident * Prims.int) Prims.list = (fun uu____5217 -> (

let uu____5218 = (FStar_ST.op_Bang query_indices)
in (FStar_List.hd uu____5218)))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push_stack : env  ->  env = (fun env -> ((

let uu____5293 = (

let uu____5296 = (FStar_ST.op_Bang stack)
in (env)::uu____5296)
in (FStar_ST.op_Colon_Equals stack uu____5293));
(

let uu___144_5335 = env
in (

let uu____5336 = (FStar_Util.smap_copy (gamma_cache env))
in (

let uu____5339 = (FStar_Util.smap_copy (sigtab env))
in (

let uu____5342 = (

let uu____5345 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_Util.mk_ref uu____5345))
in {solver = uu___144_5335.solver; range = uu___144_5335.range; curmodule = uu___144_5335.curmodule; gamma = uu___144_5335.gamma; gamma_cache = uu____5336; modules = uu___144_5335.modules; expected_typ = uu___144_5335.expected_typ; sigtab = uu____5339; is_pattern = uu___144_5335.is_pattern; instantiate_imp = uu___144_5335.instantiate_imp; effects = uu___144_5335.effects; generalize = uu___144_5335.generalize; letrecs = uu___144_5335.letrecs; top_level = uu___144_5335.top_level; check_uvars = uu___144_5335.check_uvars; use_eq = uu___144_5335.use_eq; is_iface = uu___144_5335.is_iface; admit = uu___144_5335.admit; lax = uu___144_5335.lax; lax_universes = uu___144_5335.lax_universes; failhard = uu___144_5335.failhard; nosynth = uu___144_5335.nosynth; type_of = uu___144_5335.type_of; universe_of = uu___144_5335.universe_of; use_bv_sorts = uu___144_5335.use_bv_sorts; qname_and_index = uu___144_5335.qname_and_index; proof_ns = uu___144_5335.proof_ns; synth = uu___144_5335.synth; is_native_tactic = uu___144_5335.is_native_tactic; identifier_info = uu____5342; dsenv = uu___144_5335.dsenv}))));
))


let pop_stack : Prims.unit  ->  env = (fun uu____5373 -> (

let uu____5374 = (FStar_ST.op_Bang stack)
in (match (uu____5374) with
| (env)::tl1 -> begin
((FStar_ST.op_Colon_Equals stack tl1);
env;
)
end
| uu____5418 -> begin
(failwith "Impossible: Too many pops")
end)))


let cleanup_interactive : env  ->  Prims.unit = (fun env -> (env.solver.pop ""))


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

let uu____5466 = (FStar_All.pipe_right qix (FStar_List.tryFind (fun uu____5492 -> (match (uu____5492) with
| (m, uu____5498) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____5466) with
| FStar_Pervasives_Native.None -> begin
(

let next = (n1 + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___145_5505 = env
in {solver = uu___145_5505.solver; range = uu___145_5505.range; curmodule = uu___145_5505.curmodule; gamma = uu___145_5505.gamma; gamma_cache = uu___145_5505.gamma_cache; modules = uu___145_5505.modules; expected_typ = uu___145_5505.expected_typ; sigtab = uu___145_5505.sigtab; is_pattern = uu___145_5505.is_pattern; instantiate_imp = uu___145_5505.instantiate_imp; effects = uu___145_5505.effects; generalize = uu___145_5505.generalize; letrecs = uu___145_5505.letrecs; top_level = uu___145_5505.top_level; check_uvars = uu___145_5505.check_uvars; use_eq = uu___145_5505.use_eq; is_iface = uu___145_5505.is_iface; admit = uu___145_5505.admit; lax = uu___145_5505.lax; lax_universes = uu___145_5505.lax_universes; failhard = uu___145_5505.failhard; nosynth = uu___145_5505.nosynth; type_of = uu___145_5505.type_of; universe_of = uu___145_5505.universe_of; use_bv_sorts = uu___145_5505.use_bv_sorts; qname_and_index = FStar_Pervasives_Native.Some (((l), (next))); proof_ns = uu___145_5505.proof_ns; synth = uu___145_5505.synth; is_native_tactic = uu___145_5505.is_native_tactic; identifier_info = uu___145_5505.identifier_info; dsenv = uu___145_5505.dsenv});
))
end
| FStar_Pervasives_Native.Some (uu____5510, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___146_5518 = env
in {solver = uu___146_5518.solver; range = uu___146_5518.range; curmodule = uu___146_5518.curmodule; gamma = uu___146_5518.gamma; gamma_cache = uu___146_5518.gamma_cache; modules = uu___146_5518.modules; expected_typ = uu___146_5518.expected_typ; sigtab = uu___146_5518.sigtab; is_pattern = uu___146_5518.is_pattern; instantiate_imp = uu___146_5518.instantiate_imp; effects = uu___146_5518.effects; generalize = uu___146_5518.generalize; letrecs = uu___146_5518.letrecs; top_level = uu___146_5518.top_level; check_uvars = uu___146_5518.check_uvars; use_eq = uu___146_5518.use_eq; is_iface = uu___146_5518.is_iface; admit = uu___146_5518.admit; lax = uu___146_5518.lax; lax_universes = uu___146_5518.lax_universes; failhard = uu___146_5518.failhard; nosynth = uu___146_5518.nosynth; type_of = uu___146_5518.type_of; universe_of = uu___146_5518.universe_of; use_bv_sorts = uu___146_5518.use_bv_sorts; qname_and_index = FStar_Pervasives_Native.Some (((l), (next))); proof_ns = uu___146_5518.proof_ns; synth = uu___146_5518.synth; is_native_tactic = uu___146_5518.is_native_tactic; identifier_info = uu___146_5518.identifier_info; dsenv = uu___146_5518.dsenv});
))
end))
end)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> (match ((Prims.op_Equality r FStar_Range.dummyRange)) with
| true -> begin
e
end
| uu____5539 -> begin
(

let uu___147_5540 = e
in {solver = uu___147_5540.solver; range = r; curmodule = uu___147_5540.curmodule; gamma = uu___147_5540.gamma; gamma_cache = uu___147_5540.gamma_cache; modules = uu___147_5540.modules; expected_typ = uu___147_5540.expected_typ; sigtab = uu___147_5540.sigtab; is_pattern = uu___147_5540.is_pattern; instantiate_imp = uu___147_5540.instantiate_imp; effects = uu___147_5540.effects; generalize = uu___147_5540.generalize; letrecs = uu___147_5540.letrecs; top_level = uu___147_5540.top_level; check_uvars = uu___147_5540.check_uvars; use_eq = uu___147_5540.use_eq; is_iface = uu___147_5540.is_iface; admit = uu___147_5540.admit; lax = uu___147_5540.lax; lax_universes = uu___147_5540.lax_universes; failhard = uu___147_5540.failhard; nosynth = uu___147_5540.nosynth; type_of = uu___147_5540.type_of; universe_of = uu___147_5540.universe_of; use_bv_sorts = uu___147_5540.use_bv_sorts; qname_and_index = uu___147_5540.qname_and_index; proof_ns = uu___147_5540.proof_ns; synth = uu___147_5540.synth; is_native_tactic = uu___147_5540.is_native_tactic; identifier_info = uu___147_5540.identifier_info; dsenv = uu___147_5540.dsenv})
end))


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let toggle_id_info : env  ->  Prims.bool  ->  Prims.unit = (fun env enabled -> (

let uu____5553 = (

let uu____5554 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_toggle uu____5554 enabled))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____5553)))


let insert_bv_info : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env bv ty -> (

let uu____5587 = (

let uu____5588 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_insert_bv uu____5588 bv ty))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____5587)))


let insert_fv_info : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env fv ty -> (

let uu____5621 = (

let uu____5622 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_insert_fv uu____5622 fv ty))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____5621)))


let promote_id_info : env  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  Prims.unit = (fun env ty_map -> (

let uu____5656 = (

let uu____5657 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_promote uu____5657 ty_map))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____5656)))


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let uu___148_5696 = env
in {solver = uu___148_5696.solver; range = uu___148_5696.range; curmodule = lid; gamma = uu___148_5696.gamma; gamma_cache = uu___148_5696.gamma_cache; modules = uu___148_5696.modules; expected_typ = uu___148_5696.expected_typ; sigtab = uu___148_5696.sigtab; is_pattern = uu___148_5696.is_pattern; instantiate_imp = uu___148_5696.instantiate_imp; effects = uu___148_5696.effects; generalize = uu___148_5696.generalize; letrecs = uu___148_5696.letrecs; top_level = uu___148_5696.top_level; check_uvars = uu___148_5696.check_uvars; use_eq = uu___148_5696.use_eq; is_iface = uu___148_5696.is_iface; admit = uu___148_5696.admit; lax = uu___148_5696.lax; lax_universes = uu___148_5696.lax_universes; failhard = uu___148_5696.failhard; nosynth = uu___148_5696.nosynth; type_of = uu___148_5696.type_of; universe_of = uu___148_5696.universe_of; use_bv_sorts = uu___148_5696.use_bv_sorts; qname_and_index = uu___148_5696.qname_and_index; proof_ns = uu___148_5696.proof_ns; synth = uu___148_5696.synth; is_native_tactic = uu___148_5696.is_native_tactic; identifier_info = uu___148_5696.identifier_info; dsenv = uu___148_5696.dsenv}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v1 -> (

let uu____5727 = (FStar_Syntax_Print.bv_to_string v1)
in (FStar_Util.format1 "Variable \"%s\" not found" uu____5727)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun uu____5731 -> (

let uu____5732 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____5732)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), uu____5772) -> begin
(

let n1 = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n1 - i)), (u))))))
in (

let uu____5796 = (FStar_Syntax_Subst.subst vs t)
in ((us), (uu____5796)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun uu___131_5810 -> (match (uu___131_5810) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun uu____5834 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let uu____5849 = (inst_tscheme t)
in (match (uu____5849) with
| (us, t1) -> begin
(

let uu____5860 = (FStar_Syntax_Subst.set_use_range r t1)
in ((us), (uu____5860)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed uu____5876 -> (match (uu____5876) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs1 = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in ((match ((Prims.op_disEquality (FStar_List.length insts) (FStar_List.length univs1))) with
| true -> begin
(

let uu____5891 = (

let uu____5892 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (

let uu____5893 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (

let uu____5894 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____5895 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" uu____5892 uu____5893 uu____5894 uu____5895)))))
in (failwith uu____5891))
end
| uu____5896 -> begin
()
end);
(

let uu____5897 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (FStar_Pervasives_Native.snd uu____5897));
))
end
| uu____5904 -> begin
(

let uu____5905 = (

let uu____5906 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" uu____5906))
in (failwith uu____5905))
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
| uu____5911 -> begin
false
end))


let uu___is_No : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____5916 -> begin
false
end))


let uu___is_Maybe : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____5921 -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in (match ((Prims.op_Equality l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
Yes
end
| uu____5931 -> begin
(match ((FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur1 = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l1 -> (match (((c), (l1))) with
| ([], uu____5957) -> begin
Maybe
end
| (uu____5964, []) -> begin
No
end
| ((hd1)::tl1, (hd')::tl') when (Prims.op_Equality hd1.FStar_Ident.idText hd'.FStar_Ident.idText) -> begin
(aux tl1 tl')
end
| uu____5983 -> begin
No
end))
in (aux cur1 lns))))
end
| uu____5992 -> begin
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

let uu____6090 = (FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)
in (match (uu____6090) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.find_map env.gamma (fun uu___132_6135 -> (match (uu___132_6135) with
| Binding_lid (l, t) -> begin
(match ((FStar_Ident.lid_equals lid l)) with
| true -> begin
(

let uu____6178 = (

let uu____6197 = (

let uu____6212 = (inst_tscheme t)
in FStar_Util.Inl (uu____6212))
in ((uu____6197), ((FStar_Ident.range_of_lid l))))
in FStar_Pervasives_Native.Some (uu____6178))
end
| uu____6259 -> begin
FStar_Pervasives_Native.None
end)
end
| Binding_sig (uu____6278, {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (ses, uu____6280); FStar_Syntax_Syntax.sigrng = uu____6281; FStar_Syntax_Syntax.sigquals = uu____6282; FStar_Syntax_Syntax.sigmeta = uu____6283; FStar_Syntax_Syntax.sigattrs = uu____6284}) -> begin
(FStar_Util.find_map ses (fun se -> (

let uu____6304 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____6304) with
| true -> begin
(cache ((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| uu____6335 -> begin
FStar_Pervasives_Native.None
end))))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____6350) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____6357 -> begin
(cache t)
end))
in (

let uu____6358 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____6358) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (l) -> begin
(maybe_cache ((FStar_Util.Inr (((s), (FStar_Pervasives_Native.None)))), ((FStar_Ident.range_of_lid l))))
end)))
end
| Binding_sig_inst (lids, s, us) -> begin
(

let uu____6433 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____6433) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (l) -> begin
FStar_Pervasives_Native.Some (((FStar_Util.Inr (((s), (FStar_Pervasives_Native.Some (us))))), ((FStar_Ident.range_of_lid l))))
end))
end
| uu____6519 -> begin
FStar_Pervasives_Native.None
end)))
end
| se -> begin
se
end))
end
| uu____6541 -> begin
FStar_Pervasives_Native.None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| uu____6598 -> begin
(

let uu____6599 = (find_in_sigtab env lid)
in (match (uu____6599) with
| FStar_Pervasives_Native.Some (se) -> begin
FStar_Pervasives_Native.Some (((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end)))))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____6698) -> begin
(add_sigelts env ses)
end
| uu____6707 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids);
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| uu____6721 -> begin
()
end);
))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) FStar_Pervasives_Native.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun uu___133_6750 -> (match (uu___133_6750) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
FStar_Pervasives_Native.Some (((id.FStar_Syntax_Syntax.sort), (id.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
end
| uu____6768 -> begin
FStar_Pervasives_Native.None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) * FStar_Range.range) FStar_Pervasives_Native.option = (fun se lid -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____6803, (lb)::[]), uu____6805) -> begin
(

let uu____6818 = (

let uu____6827 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____6836 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in ((uu____6827), (uu____6836))))
in FStar_Pervasives_Native.Some (uu____6818))
end
| FStar_Syntax_Syntax.Sig_let ((uu____6849, lbs), uu____6851) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____6887) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
(

let uu____6899 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____6899) with
| true -> begin
(

let uu____6910 = (

let uu____6919 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____6928 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____6919), (uu____6928))))
in FStar_Pervasives_Native.Some (uu____6910))
end
| uu____6941 -> begin
FStar_Pervasives_Native.None
end))
end)))
end
| uu____6950 -> begin
FStar_Pervasives_Native.None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) * FStar_Range.range) FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____6984 = (

let uu____6993 = (

let uu____6998 = (

let uu____6999 = (

let uu____7002 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders uu____7002))
in ((ne.FStar_Syntax_Syntax.univs), (uu____6999)))
in (inst_tscheme uu____6998))
in ((uu____6993), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____6984))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, uu____7022, uu____7023) -> begin
(

let uu____7028 = (

let uu____7037 = (

let uu____7042 = (

let uu____7043 = (

let uu____7046 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders uu____7046))
in ((us), (uu____7043)))
in (inst_tscheme uu____7042))
in ((uu____7037), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____7028))
end
| uu____7063 -> begin
FStar_Pervasives_Native.None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) * FStar_Range.range) FStar_Pervasives_Native.option = (fun env lid -> (

let mapper = (fun uu____7123 -> (match (uu____7123) with
| (lr, rng) -> begin
(match (lr) with
| FStar_Util.Inl (t) -> begin
FStar_Pervasives_Native.Some (((t), (rng)))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____7219, uvs, t, uu____7222, uu____7223, uu____7224); FStar_Syntax_Syntax.sigrng = uu____7225; FStar_Syntax_Syntax.sigquals = uu____7226; FStar_Syntax_Syntax.sigmeta = uu____7227; FStar_Syntax_Syntax.sigattrs = uu____7228}, FStar_Pervasives_Native.None) -> begin
(

let uu____7249 = (

let uu____7258 = (inst_tscheme ((uvs), (t)))
in ((uu____7258), (rng)))
in FStar_Pervasives_Native.Some (uu____7249))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t); FStar_Syntax_Syntax.sigrng = uu____7278; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____7280; FStar_Syntax_Syntax.sigattrs = uu____7281}, FStar_Pervasives_Native.None) -> begin
(

let uu____7298 = (

let uu____7299 = (in_cur_mod env l)
in (Prims.op_Equality uu____7299 Yes))
in (match (uu____7298) with
| true -> begin
(

let uu____7310 = ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface)
in (match (uu____7310) with
| true -> begin
(

let uu____7323 = (

let uu____7332 = (inst_tscheme ((uvs), (t)))
in ((uu____7332), (rng)))
in FStar_Pervasives_Native.Some (uu____7323))
end
| uu____7349 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7358 -> begin
(

let uu____7359 = (

let uu____7368 = (inst_tscheme ((uvs), (t)))
in ((uu____7368), (rng)))
in FStar_Pervasives_Native.Some (uu____7359))
end))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____7389, uu____7390); FStar_Syntax_Syntax.sigrng = uu____7391; FStar_Syntax_Syntax.sigquals = uu____7392; FStar_Syntax_Syntax.sigmeta = uu____7393; FStar_Syntax_Syntax.sigattrs = uu____7394}, FStar_Pervasives_Native.None) -> begin
(match (tps) with
| [] -> begin
(

let uu____7433 = (

let uu____7442 = (inst_tscheme ((uvs), (k)))
in ((uu____7442), (rng)))
in FStar_Pervasives_Native.Some (uu____7433))
end
| uu____7459 -> begin
(

let uu____7460 = (

let uu____7469 = (

let uu____7474 = (

let uu____7475 = (

let uu____7478 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____7478))
in ((uvs), (uu____7475)))
in (inst_tscheme uu____7474))
in ((uu____7469), (rng)))
in FStar_Pervasives_Native.Some (uu____7460))
end)
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____7499, uu____7500); FStar_Syntax_Syntax.sigrng = uu____7501; FStar_Syntax_Syntax.sigquals = uu____7502; FStar_Syntax_Syntax.sigmeta = uu____7503; FStar_Syntax_Syntax.sigattrs = uu____7504}, FStar_Pervasives_Native.Some (us)) -> begin
(match (tps) with
| [] -> begin
(

let uu____7544 = (

let uu____7553 = (inst_tscheme_with ((uvs), (k)) us)
in ((uu____7553), (rng)))
in FStar_Pervasives_Native.Some (uu____7544))
end
| uu____7570 -> begin
(

let uu____7571 = (

let uu____7580 = (

let uu____7585 = (

let uu____7586 = (

let uu____7589 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____7589))
in ((uvs), (uu____7586)))
in (inst_tscheme_with uu____7585 us))
in ((uu____7580), (rng)))
in FStar_Pervasives_Native.Some (uu____7571))
end)
end
| FStar_Util.Inr (se) -> begin
(

let uu____7623 = (match (se) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____7644); FStar_Syntax_Syntax.sigrng = uu____7645; FStar_Syntax_Syntax.sigquals = uu____7646; FStar_Syntax_Syntax.sigmeta = uu____7647; FStar_Syntax_Syntax.sigattrs = uu____7648}, FStar_Pervasives_Native.None) -> begin
(lookup_type_of_let (FStar_Pervasives_Native.fst se) lid)
end
| uu____7663 -> begin
(effect_signature (FStar_Pervasives_Native.fst se))
end)
in (FStar_All.pipe_right uu____7623 (FStar_Util.map_option (fun uu____7711 -> (match (uu____7711) with
| (us_t, rng1) -> begin
((us_t), (rng1))
end)))))
end)
end))
in (

let uu____7742 = (

let uu____7753 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____7753 mapper))
in (match (uu____7742) with
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
FStar_Pervasives_Native.Some (((((us), ((

let uu___149_7846 = t
in {FStar_Syntax_Syntax.n = uu___149_7846.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = uu___149_7846.FStar_Syntax_Syntax.vars})))), (r)))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____7873 = (lookup_qname env l)
in (match (uu____7873) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____7912) -> begin
true
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) = (fun env bv -> (

let bvr = (FStar_Syntax_Syntax.range_of_bv bv)
in (

let uu____7962 = (try_lookup_bv env bv)
in (match (uu____7962) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7977 = (

let uu____7978 = (

let uu____7983 = (variable_not_found bv)
in ((uu____7983), (bvr)))
in FStar_Errors.Error (uu____7978))
in (FStar_Exn.raise uu____7977))
end
| FStar_Pervasives_Native.Some (t, r) -> begin
(

let uu____7994 = (FStar_Syntax_Subst.set_use_range bvr t)
in (

let uu____7995 = (FStar_Range.set_use_range r bvr)
in ((uu____7994), (uu____7995))))
end))))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) FStar_Pervasives_Native.option = (fun env l -> (

let uu____8014 = (try_lookup_lid_aux env l)
in (match (uu____8014) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
(

let use_range = (FStar_Ident.range_of_lid l)
in (

let r1 = (FStar_Range.set_use_range r use_range)
in (

let uu____8080 = (

let uu____8089 = (

let uu____8094 = (FStar_Syntax_Subst.set_use_range use_range t)
in ((us), (uu____8094)))
in ((uu____8089), (r1)))
in FStar_Pervasives_Native.Some (uu____8080))))
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) = (fun env l -> (

let uu____8123 = (try_lookup_lid env l)
in (match (uu____8123) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8150 = (

let uu____8151 = (

let uu____8156 = (name_not_found l)
in ((uu____8156), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____8151))
in (FStar_Exn.raise uu____8150))
end
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end)))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun uu___134_8194 -> (match (uu___134_8194) with
| Binding_univ (y) -> begin
(Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)
end
| uu____8196 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env lid -> (

let uu____8213 = (lookup_qname env lid)
in (match (uu____8213) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____8242, uvs, t); FStar_Syntax_Syntax.sigrng = uu____8245; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____8247; FStar_Syntax_Syntax.sigattrs = uu____8248}, FStar_Pervasives_Native.None), uu____8249) -> begin
(

let uu____8298 = (

let uu____8309 = (

let uu____8314 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (uu____8314)))
in ((uu____8309), (q)))
in FStar_Pervasives_Native.Some (uu____8298))
end
| uu____8331 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____8370 = (lookup_qname env lid)
in (match (uu____8370) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____8395, uvs, t); FStar_Syntax_Syntax.sigrng = uu____8398; FStar_Syntax_Syntax.sigquals = uu____8399; FStar_Syntax_Syntax.sigmeta = uu____8400; FStar_Syntax_Syntax.sigattrs = uu____8401}, FStar_Pervasives_Native.None), uu____8402) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____8451 -> begin
(

let uu____8472 = (

let uu____8473 = (

let uu____8478 = (name_not_found lid)
in ((uu____8478), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____8473))
in (FStar_Exn.raise uu____8472))
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____8495 = (lookup_qname env lid)
in (match (uu____8495) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____8520, uvs, t, uu____8523, uu____8524, uu____8525); FStar_Syntax_Syntax.sigrng = uu____8526; FStar_Syntax_Syntax.sigquals = uu____8527; FStar_Syntax_Syntax.sigmeta = uu____8528; FStar_Syntax_Syntax.sigattrs = uu____8529}, FStar_Pervasives_Native.None), uu____8530) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____8583 -> begin
(

let uu____8604 = (

let uu____8605 = (

let uu____8610 = (name_not_found lid)
in ((uu____8610), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____8605))
in (FStar_Exn.raise uu____8604))
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  (Prims.bool * FStar_Ident.lident Prims.list) = (fun env lid -> (

let uu____8629 = (lookup_qname env lid)
in (match (uu____8629) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____8656, uu____8657, uu____8658, uu____8659, uu____8660, dcs); FStar_Syntax_Syntax.sigrng = uu____8662; FStar_Syntax_Syntax.sigquals = uu____8663; FStar_Syntax_Syntax.sigmeta = uu____8664; FStar_Syntax_Syntax.sigattrs = uu____8665}, uu____8666), uu____8667) -> begin
((true), (dcs))
end
| uu____8728 -> begin
((false), ([]))
end)))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____8759 = (lookup_qname env lid)
in (match (uu____8759) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____8780, uu____8781, uu____8782, l, uu____8784, uu____8785); FStar_Syntax_Syntax.sigrng = uu____8786; FStar_Syntax_Syntax.sigquals = uu____8787; FStar_Syntax_Syntax.sigmeta = uu____8788; FStar_Syntax_Syntax.sigattrs = uu____8789}, uu____8790), uu____8791) -> begin
l
end
| uu____8846 -> begin
(

let uu____8867 = (

let uu____8868 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" uu____8868))
in (failwith uu____8867))
end)))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (

let uu____8905 = (lookup_qname env lid)
in (match (uu____8905) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____8933) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____8984, lbs), uu____8986) when (visible se.FStar_Syntax_Syntax.sigquals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____9014 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____9014) with
| true -> begin
FStar_Pervasives_Native.Some (((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbdef)))
end
| uu____9037 -> begin
FStar_Pervasives_Native.None
end)))))
end
| uu____9046 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____9051 -> begin
FStar_Pervasives_Native.None
end))))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env ftv -> (

let uu____9088 = (lookup_qname env ftv)
in (match (uu____9088) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____9112) -> begin
(

let uu____9157 = (effect_signature se)
in (match (uu____9157) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((uu____9178, t), r) -> begin
(

let uu____9193 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t)
in FStar_Pervasives_Native.Some (uu____9193))
end))
end
| uu____9194 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (

let uu____9223 = (try_lookup_effect_lid env ftv)
in (match (uu____9223) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9226 = (

let uu____9227 = (

let uu____9232 = (name_not_found ftv)
in ((uu____9232), ((FStar_Ident.range_of_lid ftv))))
in FStar_Errors.Error (uu____9227))
in (FStar_Exn.raise uu____9226))
end
| FStar_Pervasives_Native.Some (k) -> begin
k
end)))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun env univ_insts lid0 -> (

let uu____9252 = (lookup_qname env lid0)
in (match (uu____9252) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs1, binders, c, uu____9283); FStar_Syntax_Syntax.sigrng = uu____9284; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____9286; FStar_Syntax_Syntax.sigattrs = uu____9287}, FStar_Pervasives_Native.None), uu____9288) -> begin
(

let lid1 = (

let uu____9342 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) (FStar_Ident.range_of_lid lid0))
in (FStar_Ident.set_lid_range lid uu____9342))
in (

let uu____9343 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___135_9347 -> (match (uu___135_9347) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____9348 -> begin
false
end))))
in (match (uu____9343) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____9359 -> begin
(

let insts = (match ((Prims.op_Equality (FStar_List.length univ_insts) (FStar_List.length univs1))) with
| true -> begin
univ_insts
end
| uu____9361 -> begin
(

let uu____9362 = (

let uu____9363 = (

let uu____9364 = (get_range env)
in (FStar_Range.string_of_range uu____9364))
in (

let uu____9365 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____9366 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format3 "(%s) Unexpected instantiation of effect %s with %s universes" uu____9363 uu____9365 uu____9366))))
in (failwith uu____9362))
end)
in (match (((binders), (univs1))) with
| ([], uu____9373) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (uu____9390, (uu____9391)::(uu____9392)::uu____9393) -> begin
(

let uu____9398 = (

let uu____9399 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____9400 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" uu____9399 uu____9400)))
in (failwith uu____9398))
end
| uu____9407 -> begin
(

let uu____9412 = (

let uu____9417 = (

let uu____9418 = (FStar_Syntax_Util.arrow binders c)
in ((univs1), (uu____9418)))
in (inst_tscheme_with uu____9417 insts))
in (match (uu____9412) with
| (uu____9429, t) -> begin
(

let t1 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid1) t)
in (

let uu____9432 = (

let uu____9433 = (FStar_Syntax_Subst.compress t1)
in uu____9433.FStar_Syntax_Syntax.n)
in (match (uu____9432) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
FStar_Pervasives_Native.Some (((binders1), (c1)))
end
| uu____9480 -> begin
(failwith "Impossible")
end)))
end))
end))
end)))
end
| uu____9487 -> begin
FStar_Pervasives_Native.None
end)))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find1 = (fun l1 -> (

let uu____9529 = (lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l1)
in (match (uu____9529) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____9542, c) -> begin
(

let l2 = (FStar_Syntax_Util.comp_effect_name c)
in (

let uu____9549 = (find1 l2)
in (match (uu____9549) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (l2)
end
| FStar_Pervasives_Native.Some (l') -> begin
FStar_Pervasives_Native.Some (l')
end)))
end)))
in (

let res = (

let uu____9556 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____9556) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____9560 = (find1 l)
in (match (uu____9560) with
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

let uu____9576 = (lookup_qname env l1)
in (match (uu____9576) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (uu____9599); FStar_Syntax_Syntax.sigrng = uu____9600; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____9602; FStar_Syntax_Syntax.sigattrs = uu____9603}, uu____9604), uu____9605) -> begin
q
end
| uu____9656 -> begin
[]
end))))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun uu____9692 -> (

let uu____9693 = (

let uu____9694 = (FStar_Util.string_of_int i)
in (

let uu____9695 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" uu____9694 uu____9695)))
in (failwith uu____9693)))
in (

let uu____9696 = (lookup_datacon env lid)
in (match (uu____9696) with
| (uu____9701, t) -> begin
(

let uu____9703 = (

let uu____9704 = (FStar_Syntax_Subst.compress t)
in uu____9704.FStar_Syntax_Syntax.n)
in (match (uu____9703) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____9708) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____9729 -> begin
(

let b = (FStar_List.nth binders i)
in (

let uu____9739 = (FStar_Syntax_Util.mk_field_projector_name lid (FStar_Pervasives_Native.fst b) i)
in (FStar_All.pipe_right uu____9739 FStar_Pervasives_Native.fst)))
end)
end
| uu____9748 -> begin
(fail ())
end))
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____9757 = (lookup_qname env l)
in (match (uu____9757) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____9778, uu____9779, uu____9780); FStar_Syntax_Syntax.sigrng = uu____9781; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____9783; FStar_Syntax_Syntax.sigattrs = uu____9784}, uu____9785), uu____9786) -> begin
(FStar_Util.for_some (fun uu___136_9839 -> (match (uu___136_9839) with
| FStar_Syntax_Syntax.Projector (uu____9840) -> begin
true
end
| uu____9845 -> begin
false
end)) quals)
end
| uu____9846 -> begin
false
end)))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____9875 = (lookup_qname env lid)
in (match (uu____9875) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____9896, uu____9897, uu____9898, uu____9899, uu____9900, uu____9901); FStar_Syntax_Syntax.sigrng = uu____9902; FStar_Syntax_Syntax.sigquals = uu____9903; FStar_Syntax_Syntax.sigmeta = uu____9904; FStar_Syntax_Syntax.sigattrs = uu____9905}, uu____9906), uu____9907) -> begin
true
end
| uu____9962 -> begin
false
end)))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____9991 = (lookup_qname env lid)
in (match (uu____9991) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____10012, uu____10013, uu____10014, uu____10015, uu____10016, uu____10017); FStar_Syntax_Syntax.sigrng = uu____10018; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____10020; FStar_Syntax_Syntax.sigattrs = uu____10021}, uu____10022), uu____10023) -> begin
(FStar_Util.for_some (fun uu___137_10084 -> (match (uu___137_10084) with
| FStar_Syntax_Syntax.RecordType (uu____10085) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____10094) -> begin
true
end
| uu____10103 -> begin
false
end)) quals)
end
| uu____10104 -> begin
false
end)))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____10133 = (lookup_qname env lid)
in (match (uu____10133) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____10154, uu____10155); FStar_Syntax_Syntax.sigrng = uu____10156; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____10158; FStar_Syntax_Syntax.sigattrs = uu____10159}, uu____10160), uu____10161) -> begin
(FStar_Util.for_some (fun uu___138_10218 -> (match (uu___138_10218) with
| FStar_Syntax_Syntax.Action (uu____10219) -> begin
true
end
| uu____10220 -> begin
false
end)) quals)
end
| uu____10221 -> begin
false
end)))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (fun env head1 -> (

let uu____10253 = (

let uu____10254 = (FStar_Syntax_Util.un_uinst head1)
in uu____10254.FStar_Syntax_Syntax.n)
in (match (uu____10253) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(Prims.op_Equality fv.FStar_Syntax_Syntax.fv_delta FStar_Syntax_Syntax.Delta_equational)
end
| uu____10258 -> begin
false
end))))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun x -> (match ((FStar_Pervasives_Native.fst x)) with
| FStar_Util.Inl (uu____10325) -> begin
FStar_Pervasives_Native.Some (false)
end
| FStar_Util.Inr (se, uu____10341) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____10358) -> begin
FStar_Pervasives_Native.Some ((FStar_List.contains FStar_Syntax_Syntax.New se.FStar_Syntax_Syntax.sigquals))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____10365) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____10382 -> begin
FStar_Pervasives_Native.Some (false)
end)
end))
in (

let uu____10383 = (

let uu____10386 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____10386 mapper))
in (match (uu____10383) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
false
end))))


let num_inductive_ty_params : env  ->  FStar_Ident.lident  ->  Prims.int = (fun env lid -> (

let uu____10434 = (lookup_qname env lid)
in (match (uu____10434) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____10455, uu____10456, tps, uu____10458, uu____10459, uu____10460); FStar_Syntax_Syntax.sigrng = uu____10461; FStar_Syntax_Syntax.sigquals = uu____10462; FStar_Syntax_Syntax.sigmeta = uu____10463; FStar_Syntax_Syntax.sigattrs = uu____10464}, uu____10465), uu____10466) -> begin
(FStar_List.length tps)
end
| uu____10529 -> begin
(

let uu____10550 = (

let uu____10551 = (

let uu____10556 = (name_not_found lid)
in ((uu____10556), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____10551))
in (FStar_Exn.raise uu____10550))
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun uu____10598 -> (match (uu____10598) with
| (d, uu____10606) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)
end)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (

let uu____10619 = (effect_decl_opt env l)
in (match (uu____10619) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10634 = (

let uu____10635 = (

let uu____10640 = (name_not_found l)
in ((uu____10640), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____10635))
in (FStar_Exn.raise uu____10634))
end
| FStar_Pervasives_Native.Some (md) -> begin
(FStar_Pervasives_Native.fst md)
end)))


let identity_mlift : mlift = {mlift_wp = (fun t wp -> wp); mlift_term = FStar_Pervasives_Native.Some ((fun t wp e -> (FStar_Util.return_all e)))}


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> (match ((FStar_Ident.lid_equals l1 l2)) with
| true -> begin
((l1), (identity_mlift), (identity_mlift))
end
| uu____10698 -> begin
(match ((((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid)))) with
| true -> begin
((FStar_Parser_Const.effect_GTot_lid), (identity_mlift), (identity_mlift))
end
| uu____10705 -> begin
(

let uu____10706 = (FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun uu____10759 -> (match (uu____10759) with
| (m1, m2, uu____10772, uu____10773, uu____10774) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))
in (match (uu____10706) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10791 = (

let uu____10792 = (

let uu____10797 = (

let uu____10798 = (FStar_Syntax_Print.lid_to_string l1)
in (

let uu____10799 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" uu____10798 uu____10799)))
in ((uu____10797), (env.range)))
in FStar_Errors.Error (uu____10792))
in (FStar_Exn.raise uu____10791))
end
| FStar_Pervasives_Native.Some (uu____10806, uu____10807, m3, j1, j2) -> begin
((m3), (j1), (j2))
end))
end)
end))


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge FStar_Pervasives_Native.option = (fun env l1 l2 -> (match (((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)))) with
| true -> begin
FStar_Pervasives_Native.Some ({msource = l1; mtarget = l2; mlift = identity_mlift})
end
| uu____10837 -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end))


let wp_sig_aux : 'Auu____10850 . (FStar_Syntax_Syntax.eff_decl * 'Auu____10850) Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun decls m -> (

let uu____10877 = (FStar_All.pipe_right decls (FStar_Util.find_opt (fun uu____10903 -> (match (uu____10903) with
| (d, uu____10909) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)
end))))
in (match (uu____10877) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10920 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith uu____10920))
end
| FStar_Pervasives_Native.Some (md, _q) -> begin
(

let uu____10933 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (uu____10933) with
| (uu____10944, s) -> begin
(

let s1 = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s1.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, uu____10954))::((wp, uu____10956))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____10992 -> begin
(failwith "Impossible")
end))
end))
end)))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let null_wp_for_eff : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env eff_name res_u res_t -> (match ((FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' res_t (FStar_Pervasives_Native.Some (res_u)))
end
| uu____11033 -> begin
(match ((FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal' res_t (FStar_Pervasives_Native.Some (res_u)))
end
| uu____11034 -> begin
(

let eff_name1 = (norm_eff_name env eff_name)
in (

let ed = (get_effect_decl env eff_name1)
in (

let null_wp = (inst_effect_fun_with ((res_u)::[]) env ed ed.FStar_Syntax_Syntax.null_wp)
in (

let null_wp_res = (

let uu____11041 = (get_range env)
in (

let uu____11042 = (

let uu____11045 = (

let uu____11046 = (

let uu____11061 = (

let uu____11064 = (FStar_Syntax_Syntax.as_arg res_t)
in (uu____11064)::[])
in ((null_wp), (uu____11061)))
in FStar_Syntax_Syntax.Tm_app (uu____11046))
in (FStar_Syntax_Syntax.mk uu____11045))
in (uu____11042 FStar_Pervasives_Native.None uu____11041)))
in (

let uu____11070 = (

let uu____11071 = (

let uu____11080 = (FStar_Syntax_Syntax.as_arg null_wp_res)
in (uu____11080)::[])
in {FStar_Syntax_Syntax.comp_univs = (res_u)::[]; FStar_Syntax_Syntax.effect_name = eff_name1; FStar_Syntax_Syntax.result_typ = res_t; FStar_Syntax_Syntax.effect_args = uu____11071; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp uu____11070))))))
end)
end))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let effects = (

let uu___150_11091 = env.effects
in {decls = (((ne), (se.FStar_Syntax_Syntax.sigquals)))::env.effects.decls; order = uu___150_11091.order; joins = uu___150_11091.joins})
in (

let uu___151_11100 = env
in {solver = uu___151_11100.solver; range = uu___151_11100.range; curmodule = uu___151_11100.curmodule; gamma = uu___151_11100.gamma; gamma_cache = uu___151_11100.gamma_cache; modules = uu___151_11100.modules; expected_typ = uu___151_11100.expected_typ; sigtab = uu___151_11100.sigtab; is_pattern = uu___151_11100.is_pattern; instantiate_imp = uu___151_11100.instantiate_imp; effects = effects; generalize = uu___151_11100.generalize; letrecs = uu___151_11100.letrecs; top_level = uu___151_11100.top_level; check_uvars = uu___151_11100.check_uvars; use_eq = uu___151_11100.use_eq; is_iface = uu___151_11100.is_iface; admit = uu___151_11100.admit; lax = uu___151_11100.lax; lax_universes = uu___151_11100.lax_universes; failhard = uu___151_11100.failhard; nosynth = uu___151_11100.nosynth; type_of = uu___151_11100.type_of; universe_of = uu___151_11100.universe_of; use_bv_sorts = uu___151_11100.use_bv_sorts; qname_and_index = uu___151_11100.qname_and_index; proof_ns = uu___151_11100.proof_ns; synth = uu___151_11100.synth; is_native_tactic = uu___151_11100.is_native_tactic; identifier_info = uu___151_11100.identifier_info; dsenv = uu___151_11100.dsenv}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let compose_edges = (fun e1 e2 -> (

let composed_lift = (

let mlift_wp = (fun r wp1 -> (

let uu____11117 = (e1.mlift.mlift_wp r wp1)
in (e2.mlift.mlift_wp r uu____11117)))
in (

let mlift_term = (match (((e1.mlift.mlift_term), (e2.mlift.mlift_term))) with
| (FStar_Pervasives_Native.Some (l1), FStar_Pervasives_Native.Some (l2)) -> begin
FStar_Pervasives_Native.Some ((fun t wp e -> (

let uu____11207 = (e1.mlift.mlift_wp t wp)
in (

let uu____11208 = (l1 t wp e)
in (l2 t uu____11207 uu____11208)))))
end
| uu____11209 -> begin
FStar_Pervasives_Native.None
end)
in {mlift_wp = mlift_wp; mlift_term = mlift_term}))
in {msource = e1.msource; mtarget = e2.mtarget; mlift = composed_lift}))
in (

let mk_mlift_wp = (fun lift_t r wp1 -> (

let uu____11248 = (inst_tscheme lift_t)
in (match (uu____11248) with
| (uu____11255, lift_t1) -> begin
(

let uu____11257 = (

let uu____11260 = (

let uu____11261 = (

let uu____11276 = (

let uu____11279 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____11280 = (

let uu____11283 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____11283)::[])
in (uu____11279)::uu____11280))
in ((lift_t1), (uu____11276)))
in FStar_Syntax_Syntax.Tm_app (uu____11261))
in (FStar_Syntax_Syntax.mk uu____11260))
in (uu____11257 FStar_Pervasives_Native.None wp1.FStar_Syntax_Syntax.pos))
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

let uu____11324 = (inst_tscheme lift_t)
in (match (uu____11324) with
| (uu____11331, lift_t1) -> begin
(

let uu____11333 = (

let uu____11336 = (

let uu____11337 = (

let uu____11352 = (

let uu____11355 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____11356 = (

let uu____11359 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____11360 = (

let uu____11363 = (FStar_Syntax_Syntax.as_arg e)
in (uu____11363)::[])
in (uu____11359)::uu____11360))
in (uu____11355)::uu____11356))
in ((lift_t1), (uu____11352)))
in FStar_Syntax_Syntax.Tm_app (uu____11337))
in (FStar_Syntax_Syntax.mk uu____11336))
in (uu____11333 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
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

let uu____11401 = (

let uu____11402 = (FStar_Ident.lid_of_path ((s)::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____11402 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.fv_to_tm uu____11401)))
in (

let arg = (bogus_term "ARG")
in (

let wp = (bogus_term "WP")
in (

let e = (bogus_term "COMP")
in (

let uu____11406 = (

let uu____11407 = (l.mlift_wp arg wp)
in (FStar_Syntax_Print.term_to_string uu____11407))
in (

let uu____11408 = (

let uu____11409 = (FStar_Util.map_opt l.mlift_term (fun l1 -> (

let uu____11427 = (l1 arg wp e)
in (FStar_Syntax_Print.term_to_string uu____11427))))
in (FStar_Util.dflt "none" uu____11409))
in (FStar_Util.format2 "{ wp : %s ; term : %s }" uu____11406 uu____11408))))))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun uu____11453 -> (match (uu____11453) with
| (e, uu____11461) -> begin
e.FStar_Syntax_Syntax.mname
end))))
in (

let find_edge = (fun order1 uu____11480 -> (match (uu____11480) with
| (i, j) -> begin
(match ((FStar_Ident.lid_equals i j)) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)))
end
| uu____11495 -> begin
(FStar_All.pipe_right order1 (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end)
end))
in (

let order1 = (

let fold_fun = (fun order1 k -> (

let uu____11518 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (match ((FStar_Ident.lid_equals i k)) with
| true -> begin
[]
end
| uu____11529 -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (match ((FStar_Ident.lid_equals j k)) with
| true -> begin
[]
end
| uu____11538 -> begin
(

let uu____11539 = (

let uu____11548 = (find_edge order1 ((i), (k)))
in (

let uu____11551 = (find_edge order1 ((k), (j)))
in ((uu____11548), (uu____11551))))
in (match (uu____11539) with
| (FStar_Pervasives_Native.Some (e1), FStar_Pervasives_Native.Some (e2)) -> begin
(

let uu____11566 = (compose_edges e1 e2)
in (uu____11566)::[])
end
| uu____11567 -> begin
[]
end))
end))))
end))))
in (FStar_List.append order1 uu____11518)))
in (FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)))
in (

let order2 = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order1)
in ((FStar_All.pipe_right order2 (FStar_List.iter (fun edge1 -> (

let uu____11596 = ((FStar_Ident.lid_equals edge1.msource FStar_Parser_Const.effect_DIV_lid) && (

let uu____11598 = (lookup_effect_quals env edge1.mtarget)
in (FStar_All.pipe_right uu____11598 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))))
in (match (uu____11596) with
| true -> begin
(

let uu____11603 = (

let uu____11604 = (

let uu____11609 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge1.mtarget.FStar_Ident.str)
in (

let uu____11610 = (get_range env)
in ((uu____11609), (uu____11610))))
in FStar_Errors.Error (uu____11604))
in (FStar_Exn.raise uu____11603))
end
| uu____11611 -> begin
()
end)))));
(

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (match ((FStar_Ident.lid_equals i j)) with
| true -> begin
FStar_Pervasives_Native.Some (((i), ((id_edge i)), ((id_edge i))))
end
| uu____11701 -> begin
(FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (

let uu____11735 = (

let uu____11744 = (find_edge order2 ((i), (k)))
in (

let uu____11747 = (find_edge order2 ((j), (k)))
in ((uu____11744), (uu____11747))))
in (match (uu____11735) with
| (FStar_Pervasives_Native.Some (ik), FStar_Pervasives_Native.Some (jk)) -> begin
(match (bopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((k), (ik), (jk)))
end
| FStar_Pervasives_Native.Some (ub, uu____11789, uu____11790) -> begin
(

let uu____11797 = (

let uu____11802 = (

let uu____11803 = (find_edge order2 ((k), (ub)))
in (FStar_Util.is_some uu____11803))
in (

let uu____11806 = (

let uu____11807 = (find_edge order2 ((ub), (k)))
in (FStar_Util.is_some uu____11807))
in ((uu____11802), (uu____11806))))
in (match (uu____11797) with
| (true, true) -> begin
(match ((FStar_Ident.lid_equals k ub)) with
| true -> begin
((FStar_Util.print_warning "Looking multiple times at the same upper bound candidate");
bopt;
)
end
| uu____11827 -> begin
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
| uu____11842 -> begin
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

let uu___152_11915 = env.effects
in {decls = uu___152_11915.decls; order = order2; joins = joins})
in (

let uu___153_11916 = env
in {solver = uu___153_11916.solver; range = uu___153_11916.range; curmodule = uu___153_11916.curmodule; gamma = uu___153_11916.gamma; gamma_cache = uu___153_11916.gamma_cache; modules = uu___153_11916.modules; expected_typ = uu___153_11916.expected_typ; sigtab = uu___153_11916.sigtab; is_pattern = uu___153_11916.is_pattern; instantiate_imp = uu___153_11916.instantiate_imp; effects = effects; generalize = uu___153_11916.generalize; letrecs = uu___153_11916.letrecs; top_level = uu___153_11916.top_level; check_uvars = uu___153_11916.check_uvars; use_eq = uu___153_11916.use_eq; is_iface = uu___153_11916.is_iface; admit = uu___153_11916.admit; lax = uu___153_11916.lax; lax_universes = uu___153_11916.lax_universes; failhard = uu___153_11916.failhard; nosynth = uu___153_11916.nosynth; type_of = uu___153_11916.type_of; universe_of = uu___153_11916.universe_of; use_bv_sorts = uu___153_11916.use_bv_sorts; qname_and_index = uu___153_11916.qname_and_index; proof_ns = uu___153_11916.proof_ns; synth = uu___153_11916.synth; is_native_tactic = uu___153_11916.is_native_tactic; identifier_info = uu___153_11916.identifier_info; dsenv = uu___153_11916.dsenv})));
))))))))))))))
end
| uu____11917 -> begin
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
| uu____11943 -> begin
c
end)
in (FStar_Syntax_Util.comp_to_comp_typ c1)))


let rec unfold_effect_abbrev : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (comp_to_comp_typ env comp)
in (

let uu____11953 = (lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name)
in (match (uu____11953) with
| FStar_Pervasives_Native.None -> begin
c
end
| FStar_Pervasives_Native.Some (binders, cdef) -> begin
(

let uu____11970 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (uu____11970) with
| (binders1, cdef1) -> begin
((match ((Prims.op_disEquality (FStar_List.length binders1) ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))) with
| true -> begin
(

let uu____11988 = (

let uu____11989 = (

let uu____11994 = (

let uu____11995 = (FStar_Util.string_of_int (FStar_List.length binders1))
in (

let uu____12000 = (FStar_Util.string_of_int ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))
in (

let uu____12007 = (

let uu____12008 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Print.comp_to_string uu____12008))
in (FStar_Util.format3 "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s" uu____11995 uu____12000 uu____12007))))
in ((uu____11994), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____11989))
in (FStar_Exn.raise uu____11988))
end
| uu____12009 -> begin
()
end);
(

let inst1 = (

let uu____12013 = (

let uu____12022 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (uu____12022)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun uu____12039 uu____12040 -> (match (((uu____12039), (uu____12040))) with
| ((x, uu____12062), (t, uu____12064)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders1 uu____12013))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst1 cdef1)
in (

let c2 = (

let uu____12083 = (

let uu___154_12084 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = uu___154_12084.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___154_12084.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___154_12084.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___154_12084.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right uu____12083 FStar_Syntax_Syntax.mk_Comp))
in (unfold_effect_abbrev env c2))));
)
end))
end))))


let effect_repr_aux : Prims.bool  ->  env  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun only_reifiable env c u_c -> (

let effect_name = (norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (

let uu____12110 = (effect_decl_opt env effect_name)
in (match (uu____12110) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____12143 = (only_reifiable && (

let uu____12145 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____12145))))
in (match (uu____12143) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____12154 -> begin
(match (ed.FStar_Syntax_Syntax.repr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| uu____12161 -> begin
(

let c1 = (unfold_effect_abbrev env c)
in (

let res_typ = c1.FStar_Syntax_Syntax.result_typ
in (

let wp = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (hd1)::uu____12180 -> begin
hd1
end
| [] -> begin
(

let name = (FStar_Ident.string_of_lid effect_name)
in (

let message = (

let uu____12209 = (FStar_Util.format1 "Not enough arguments for effect %s. " name)
in (Prims.strcat uu____12209 (Prims.strcat "This usually happens when you use a partially applied DM4F effect, " "like [TAC int] instead of [Tac int].")))
in (

let uu____12210 = (

let uu____12211 = (

let uu____12216 = (get_range env)
in ((message), (uu____12216)))
in FStar_Errors.Error (uu____12211))
in (FStar_Exn.raise uu____12210))))
end)
in (

let repr = (inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____12226 = (

let uu____12229 = (get_range env)
in (

let uu____12230 = (

let uu____12233 = (

let uu____12234 = (

let uu____12249 = (

let uu____12252 = (FStar_Syntax_Syntax.as_arg res_typ)
in (uu____12252)::(wp)::[])
in ((repr), (uu____12249)))
in FStar_Syntax_Syntax.Tm_app (uu____12234))
in (FStar_Syntax_Syntax.mk uu____12233))
in (uu____12230 FStar_Pervasives_Native.None uu____12229)))
in FStar_Pervasives_Native.Some (uu____12226))))))
end)
end))
end))))


let effect_repr : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (

let uu____12304 = (

let uu____12305 = (

let uu____12310 = (

let uu____12311 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format1 "Effect %s cannot be reified" uu____12311))
in (

let uu____12312 = (get_range env)
in ((uu____12310), (uu____12312))))
in FStar_Errors.Error (uu____12305))
in (FStar_Exn.raise uu____12304)))
in (

let uu____12313 = (effect_repr_aux true env c u_c)
in (match (uu____12313) with
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
| uu____12353 -> begin
false
end))


let is_reifiable_function : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____12362 = (

let uu____12363 = (FStar_Syntax_Subst.compress t)
in uu____12363.FStar_Syntax_Syntax.n)
in (match (uu____12362) with
| FStar_Syntax_Syntax.Tm_arrow (uu____12366, c) -> begin
(is_reifiable_comp env c)
end
| uu____12384 -> begin
false
end)))


let push_in_gamma : env  ->  binding  ->  env = (fun env s -> (

let rec push1 = (fun x rest -> (match (rest) with
| (Binding_sig (uu____12408))::uu____12409 -> begin
(x)::rest
end
| (Binding_sig_inst (uu____12418))::uu____12419 -> begin
(x)::rest
end
| [] -> begin
(x)::[]
end
| (local)::rest1 -> begin
(

let uu____12434 = (push1 x rest1)
in (local)::uu____12434)
end))
in (

let uu___155_12437 = env
in (

let uu____12438 = (push1 s env.gamma)
in {solver = uu___155_12437.solver; range = uu___155_12437.range; curmodule = uu___155_12437.curmodule; gamma = uu____12438; gamma_cache = uu___155_12437.gamma_cache; modules = uu___155_12437.modules; expected_typ = uu___155_12437.expected_typ; sigtab = uu___155_12437.sigtab; is_pattern = uu___155_12437.is_pattern; instantiate_imp = uu___155_12437.instantiate_imp; effects = uu___155_12437.effects; generalize = uu___155_12437.generalize; letrecs = uu___155_12437.letrecs; top_level = uu___155_12437.top_level; check_uvars = uu___155_12437.check_uvars; use_eq = uu___155_12437.use_eq; is_iface = uu___155_12437.is_iface; admit = uu___155_12437.admit; lax = uu___155_12437.lax; lax_universes = uu___155_12437.lax_universes; failhard = uu___155_12437.failhard; nosynth = uu___155_12437.nosynth; type_of = uu___155_12437.type_of; universe_of = uu___155_12437.universe_of; use_bv_sorts = uu___155_12437.use_bv_sorts; qname_and_index = uu___155_12437.qname_and_index; proof_ns = uu___155_12437.proof_ns; synth = uu___155_12437.synth; is_native_tactic = uu___155_12437.is_native_tactic; identifier_info = uu___155_12437.identifier_info; dsenv = uu___155_12437.dsenv}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env1 = (push_in_gamma env (Binding_sig ((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))))
in (build_lattice env1 s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env1 = (push_in_gamma env (Binding_sig_inst ((((FStar_Syntax_Util.lids_of_sigelt s)), (s), (us)))))
in (build_lattice env1 s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let uu___156_12475 = env
in {solver = uu___156_12475.solver; range = uu___156_12475.range; curmodule = uu___156_12475.curmodule; gamma = (b)::env.gamma; gamma_cache = uu___156_12475.gamma_cache; modules = uu___156_12475.modules; expected_typ = uu___156_12475.expected_typ; sigtab = uu___156_12475.sigtab; is_pattern = uu___156_12475.is_pattern; instantiate_imp = uu___156_12475.instantiate_imp; effects = uu___156_12475.effects; generalize = uu___156_12475.generalize; letrecs = uu___156_12475.letrecs; top_level = uu___156_12475.top_level; check_uvars = uu___156_12475.check_uvars; use_eq = uu___156_12475.use_eq; is_iface = uu___156_12475.is_iface; admit = uu___156_12475.admit; lax = uu___156_12475.lax; lax_universes = uu___156_12475.lax_universes; failhard = uu___156_12475.failhard; nosynth = uu___156_12475.nosynth; type_of = uu___156_12475.type_of; universe_of = uu___156_12475.universe_of; use_bv_sorts = uu___156_12475.use_bv_sorts; qname_and_index = uu___156_12475.qname_and_index; proof_ns = uu___156_12475.proof_ns; synth = uu___156_12475.synth; is_native_tactic = uu___156_12475.is_native_tactic; identifier_info = uu___156_12475.identifier_info; dsenv = uu___156_12475.dsenv}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let pop_bv : env  ->  (FStar_Syntax_Syntax.bv * env) FStar_Pervasives_Native.option = (fun env -> (match (env.gamma) with
| (Binding_var (x))::rest -> begin
FStar_Pervasives_Native.Some (((x), ((

let uu___157_12509 = env
in {solver = uu___157_12509.solver; range = uu___157_12509.range; curmodule = uu___157_12509.curmodule; gamma = rest; gamma_cache = uu___157_12509.gamma_cache; modules = uu___157_12509.modules; expected_typ = uu___157_12509.expected_typ; sigtab = uu___157_12509.sigtab; is_pattern = uu___157_12509.is_pattern; instantiate_imp = uu___157_12509.instantiate_imp; effects = uu___157_12509.effects; generalize = uu___157_12509.generalize; letrecs = uu___157_12509.letrecs; top_level = uu___157_12509.top_level; check_uvars = uu___157_12509.check_uvars; use_eq = uu___157_12509.use_eq; is_iface = uu___157_12509.is_iface; admit = uu___157_12509.admit; lax = uu___157_12509.lax; lax_universes = uu___157_12509.lax_universes; failhard = uu___157_12509.failhard; nosynth = uu___157_12509.nosynth; type_of = uu___157_12509.type_of; universe_of = uu___157_12509.universe_of; use_bv_sorts = uu___157_12509.use_bv_sorts; qname_and_index = uu___157_12509.qname_and_index; proof_ns = uu___157_12509.proof_ns; synth = uu___157_12509.synth; is_native_tactic = uu___157_12509.is_native_tactic; identifier_info = uu___157_12509.identifier_info; dsenv = uu___157_12509.dsenv}))))
end
| uu____12510 -> begin
FStar_Pervasives_Native.None
end))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env1 uu____12534 -> (match (uu____12534) with
| (x, uu____12540) -> begin
(push_bv env1 x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x1) -> begin
(

let x2 = (

let uu___158_12570 = x1
in {FStar_Syntax_Syntax.ppname = uu___158_12570.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___158_12570.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)})
in Binding_var (x2))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> ((add_sigelts env m.FStar_Syntax_Syntax.exports);
(

let uu___159_12605 = env
in {solver = uu___159_12605.solver; range = uu___159_12605.range; curmodule = uu___159_12605.curmodule; gamma = []; gamma_cache = uu___159_12605.gamma_cache; modules = (m)::env.modules; expected_typ = FStar_Pervasives_Native.None; sigtab = uu___159_12605.sigtab; is_pattern = uu___159_12605.is_pattern; instantiate_imp = uu___159_12605.instantiate_imp; effects = uu___159_12605.effects; generalize = uu___159_12605.generalize; letrecs = uu___159_12605.letrecs; top_level = uu___159_12605.top_level; check_uvars = uu___159_12605.check_uvars; use_eq = uu___159_12605.use_eq; is_iface = uu___159_12605.is_iface; admit = uu___159_12605.admit; lax = uu___159_12605.lax; lax_universes = uu___159_12605.lax_universes; failhard = uu___159_12605.failhard; nosynth = uu___159_12605.nosynth; type_of = uu___159_12605.type_of; universe_of = uu___159_12605.universe_of; use_bv_sorts = uu___159_12605.use_bv_sorts; qname_and_index = uu___159_12605.qname_and_index; proof_ns = uu___159_12605.proof_ns; synth = uu___159_12605.synth; is_native_tactic = uu___159_12605.is_native_tactic; identifier_info = uu___159_12605.identifier_info; dsenv = uu___159_12605.dsenv});
))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env1 x -> (push_local_binding env1 (Binding_univ (x)))) env xs))


let open_universes_in : env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term Prims.list  ->  (env * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term Prims.list) = (fun env uvs terms -> (

let uu____12642 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____12642) with
| (univ_subst, univ_vars) -> begin
(

let env' = (push_univ_vars env univ_vars)
in (

let uu____12670 = (FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms)
in ((env'), (univ_vars), (uu____12670))))
end)))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let uu___160_12685 = env
in {solver = uu___160_12685.solver; range = uu___160_12685.range; curmodule = uu___160_12685.curmodule; gamma = uu___160_12685.gamma; gamma_cache = uu___160_12685.gamma_cache; modules = uu___160_12685.modules; expected_typ = FStar_Pervasives_Native.Some (t); sigtab = uu___160_12685.sigtab; is_pattern = uu___160_12685.is_pattern; instantiate_imp = uu___160_12685.instantiate_imp; effects = uu___160_12685.effects; generalize = uu___160_12685.generalize; letrecs = uu___160_12685.letrecs; top_level = uu___160_12685.top_level; check_uvars = uu___160_12685.check_uvars; use_eq = false; is_iface = uu___160_12685.is_iface; admit = uu___160_12685.admit; lax = uu___160_12685.lax; lax_universes = uu___160_12685.lax_universes; failhard = uu___160_12685.failhard; nosynth = uu___160_12685.nosynth; type_of = uu___160_12685.type_of; universe_of = uu___160_12685.universe_of; use_bv_sorts = uu___160_12685.use_bv_sorts; qname_and_index = uu___160_12685.qname_and_index; proof_ns = uu___160_12685.proof_ns; synth = uu___160_12685.synth; is_native_tactic = uu___160_12685.is_native_tactic; identifier_info = uu___160_12685.identifier_info; dsenv = uu___160_12685.dsenv}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun env -> (match (env.expected_typ) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) = (fun env_ -> (

let uu____12711 = (expected_typ env_)
in (((

let uu___161_12717 = env_
in {solver = uu___161_12717.solver; range = uu___161_12717.range; curmodule = uu___161_12717.curmodule; gamma = uu___161_12717.gamma; gamma_cache = uu___161_12717.gamma_cache; modules = uu___161_12717.modules; expected_typ = FStar_Pervasives_Native.None; sigtab = uu___161_12717.sigtab; is_pattern = uu___161_12717.is_pattern; instantiate_imp = uu___161_12717.instantiate_imp; effects = uu___161_12717.effects; generalize = uu___161_12717.generalize; letrecs = uu___161_12717.letrecs; top_level = uu___161_12717.top_level; check_uvars = uu___161_12717.check_uvars; use_eq = false; is_iface = uu___161_12717.is_iface; admit = uu___161_12717.admit; lax = uu___161_12717.lax; lax_universes = uu___161_12717.lax_universes; failhard = uu___161_12717.failhard; nosynth = uu___161_12717.nosynth; type_of = uu___161_12717.type_of; universe_of = uu___161_12717.universe_of; use_bv_sorts = uu___161_12717.use_bv_sorts; qname_and_index = uu___161_12717.qname_and_index; proof_ns = uu___161_12717.proof_ns; synth = uu___161_12717.synth; is_native_tactic = uu___161_12717.is_native_tactic; identifier_info = uu___161_12717.identifier_info; dsenv = uu___161_12717.dsenv})), (uu____12711))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = (match ((FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Parser_Const.prims_lid)) with
| true -> begin
(

let uu____12732 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun uu___139_12742 -> (match (uu___139_12742) with
| Binding_sig (uu____12745, se) -> begin
(se)::[]
end
| uu____12751 -> begin
[]
end))))
in (FStar_All.pipe_right uu____12732 FStar_List.rev))
end
| uu____12756 -> begin
m.FStar_Syntax_Syntax.exports
end)
in ((add_sigelts env sigs);
(

let uu___162_12758 = env
in {solver = uu___162_12758.solver; range = uu___162_12758.range; curmodule = empty_lid; gamma = []; gamma_cache = uu___162_12758.gamma_cache; modules = (m)::env.modules; expected_typ = uu___162_12758.expected_typ; sigtab = uu___162_12758.sigtab; is_pattern = uu___162_12758.is_pattern; instantiate_imp = uu___162_12758.instantiate_imp; effects = uu___162_12758.effects; generalize = uu___162_12758.generalize; letrecs = uu___162_12758.letrecs; top_level = uu___162_12758.top_level; check_uvars = uu___162_12758.check_uvars; use_eq = uu___162_12758.use_eq; is_iface = uu___162_12758.is_iface; admit = uu___162_12758.admit; lax = uu___162_12758.lax; lax_universes = uu___162_12758.lax_universes; failhard = uu___162_12758.failhard; nosynth = uu___162_12758.nosynth; type_of = uu___162_12758.type_of; universe_of = uu___162_12758.universe_of; use_bv_sorts = uu___162_12758.use_bv_sorts; qname_and_index = uu___162_12758.qname_and_index; proof_ns = uu___162_12758.proof_ns; synth = uu___162_12758.synth; is_native_tactic = uu___162_12758.is_native_tactic; identifier_info = uu___162_12758.identifier_info; dsenv = uu___162_12758.dsenv});
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
| (Binding_univ (uu____12840))::tl1 -> begin
(aux out tl1)
end
| (Binding_lid (uu____12844, (uu____12845, t)))::tl1 -> begin
(

let uu____12860 = (

let uu____12867 = (FStar_Syntax_Free.uvars t)
in (ext out uu____12867))
in (aux uu____12860 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____12874; FStar_Syntax_Syntax.index = uu____12875; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____12882 = (

let uu____12889 = (FStar_Syntax_Free.uvars t)
in (ext out uu____12889))
in (aux uu____12882 tl1))
end
| (Binding_sig (uu____12896))::uu____12897 -> begin
out
end
| (Binding_sig_inst (uu____12906))::uu____12907 -> begin
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
| (Binding_sig_inst (uu____12963))::tl1 -> begin
(aux out tl1)
end
| (Binding_univ (uu____12975))::tl1 -> begin
(aux out tl1)
end
| (Binding_lid (uu____12979, (uu____12980, t)))::tl1 -> begin
(

let uu____12995 = (

let uu____12998 = (FStar_Syntax_Free.univs t)
in (ext out uu____12998))
in (aux uu____12995 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____13001; FStar_Syntax_Syntax.index = uu____13002; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____13009 = (

let uu____13012 = (FStar_Syntax_Free.univs t)
in (ext out uu____13012))
in (aux uu____13009 tl1))
end
| (Binding_sig (uu____13015))::uu____13016 -> begin
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
| (Binding_sig_inst (uu____13070))::tl1 -> begin
(aux out tl1)
end
| (Binding_univ (uname))::tl1 -> begin
(

let uu____13086 = (FStar_Util.fifo_set_add uname out)
in (aux uu____13086 tl1))
end
| (Binding_lid (uu____13089, (uu____13090, t)))::tl1 -> begin
(

let uu____13105 = (

let uu____13108 = (FStar_Syntax_Free.univnames t)
in (ext out uu____13108))
in (aux uu____13105 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____13111; FStar_Syntax_Syntax.index = uu____13112; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____13119 = (

let uu____13122 = (FStar_Syntax_Free.univnames t)
in (ext out uu____13122))
in (aux uu____13119 tl1))
end
| (Binding_sig (uu____13125))::uu____13126 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu___140_13151 -> (match (uu___140_13151) with
| Binding_var (x) -> begin
(x)::[]
end
| Binding_lid (uu____13155) -> begin
[]
end
| Binding_sig (uu____13160) -> begin
[]
end
| Binding_univ (uu____13167) -> begin
[]
end
| Binding_sig_inst (uu____13168) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____13185 = (

let uu____13188 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right uu____13188 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right uu____13185 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let print_gamma : env  ->  Prims.unit = (fun env -> (

let uu____13213 = (

let uu____13214 = (FStar_All.pipe_right env.gamma (FStar_List.map (fun uu___141_13224 -> (match (uu___141_13224) with
| Binding_var (x) -> begin
(

let uu____13226 = (FStar_Syntax_Print.bv_to_string x)
in (Prims.strcat "Binding_var " uu____13226))
end
| Binding_univ (u) -> begin
(Prims.strcat "Binding_univ " u.FStar_Ident.idText)
end
| Binding_lid (l, uu____13229) -> begin
(

let uu____13230 = (FStar_Ident.string_of_lid l)
in (Prims.strcat "Binding_lid " uu____13230))
end
| Binding_sig (ls, uu____13232) -> begin
(

let uu____13237 = (

let uu____13238 = (FStar_All.pipe_right ls (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____13238 (FStar_String.concat ", ")))
in (Prims.strcat "Binding_sig " uu____13237))
end
| Binding_sig_inst (ls, uu____13248, uu____13249) -> begin
(

let uu____13254 = (

let uu____13255 = (FStar_All.pipe_right ls (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____13255 (FStar_String.concat ", ")))
in (Prims.strcat "Binding_sig_inst " uu____13254))
end))))
in (FStar_All.pipe_right uu____13214 (FStar_String.concat "::\n")))
in (FStar_All.pipe_right uu____13213 (FStar_Util.print1 "%s\n"))))


let eq_gamma : env  ->  env  ->  Prims.bool = (fun env env' -> (

let uu____13274 = (FStar_Util.physical_equality env.gamma env'.gamma)
in (match (uu____13274) with
| true -> begin
true
end
| uu____13277 -> begin
(

let g = (all_binders env)
in (

let g' = (all_binders env')
in ((Prims.op_Equality (FStar_List.length g) (FStar_List.length g')) && (FStar_List.forall2 (fun uu____13302 uu____13303 -> (match (((uu____13302), (uu____13303))) with
| ((b1, uu____13321), (b2, uu____13323)) -> begin
(FStar_Syntax_Syntax.bv_eq b1 b2)
end)) g g'))))
end)))


let fold_env : 'a . env  ->  ('a  ->  binding  ->  'a)  ->  'a  ->  'a = (fun env f a -> (FStar_List.fold_right (fun e a1 -> (f a1 e)) env.gamma a))


let string_of_delta_level : delta_level  ->  Prims.string = (fun uu___142_13370 -> (match (uu___142_13370) with
| NoDelta -> begin
"NoDelta"
end
| Inlining -> begin
"Inlining"
end
| Eager_unfolding_only -> begin
"Eager_unfolding_only"
end
| Unfold (uu____13371) -> begin
"Unfold _"
end
| UnfoldTac -> begin
"UnfoldTac"
end))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys uu___143_13390 -> (match (uu___143_13390) with
| Binding_sig (lids, uu____13396) -> begin
(FStar_List.append lids keys)
end
| uu____13401 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun uu____13407 v1 keys1 -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)) keys)))


let should_enc_path : env  ->  Prims.string Prims.list  ->  Prims.bool = (fun env path -> (

let rec list_prefix = (fun xs ys -> (match (((xs), (ys))) with
| ([], uu____13443) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((Prims.op_Equality x y) && (list_prefix xs1 ys1))
end
| (uu____13462, uu____13463) -> begin
false
end))
in (

let rec should_enc_path' = (fun pns path1 -> (match (pns) with
| [] -> begin
true
end
| ((p, b))::pns1 -> begin
(

let uu____13500 = (list_prefix p path1)
in (match (uu____13500) with
| true -> begin
b
end
| uu____13501 -> begin
(should_enc_path' pns1 path1)
end))
end))
in (should_enc_path' (FStar_List.flatten env.proof_ns) path))))


let should_enc_lid : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____13514 = (FStar_Ident.path_of_lid lid)
in (should_enc_path env uu____13514)))


let cons_proof_ns : Prims.bool  ->  env  ->  name_prefix  ->  env = (fun b e path -> (match (e.proof_ns) with
| [] -> begin
(failwith "empty proof_ns stack!")
end
| (pns)::rest -> begin
(

let pns' = (((path), (b)))::pns
in (

let uu___163_13544 = e
in {solver = uu___163_13544.solver; range = uu___163_13544.range; curmodule = uu___163_13544.curmodule; gamma = uu___163_13544.gamma; gamma_cache = uu___163_13544.gamma_cache; modules = uu___163_13544.modules; expected_typ = uu___163_13544.expected_typ; sigtab = uu___163_13544.sigtab; is_pattern = uu___163_13544.is_pattern; instantiate_imp = uu___163_13544.instantiate_imp; effects = uu___163_13544.effects; generalize = uu___163_13544.generalize; letrecs = uu___163_13544.letrecs; top_level = uu___163_13544.top_level; check_uvars = uu___163_13544.check_uvars; use_eq = uu___163_13544.use_eq; is_iface = uu___163_13544.is_iface; admit = uu___163_13544.admit; lax = uu___163_13544.lax; lax_universes = uu___163_13544.lax_universes; failhard = uu___163_13544.failhard; nosynth = uu___163_13544.nosynth; type_of = uu___163_13544.type_of; universe_of = uu___163_13544.universe_of; use_bv_sorts = uu___163_13544.use_bv_sorts; qname_and_index = uu___163_13544.qname_and_index; proof_ns = (pns')::rest; synth = uu___163_13544.synth; is_native_tactic = uu___163_13544.is_native_tactic; identifier_info = uu___163_13544.identifier_info; dsenv = uu___163_13544.dsenv}))
end))


let add_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns true e path))


let rem_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns false e path))


let push_proof_ns : env  ->  env = (fun e -> (

let uu___164_13571 = e
in {solver = uu___164_13571.solver; range = uu___164_13571.range; curmodule = uu___164_13571.curmodule; gamma = uu___164_13571.gamma; gamma_cache = uu___164_13571.gamma_cache; modules = uu___164_13571.modules; expected_typ = uu___164_13571.expected_typ; sigtab = uu___164_13571.sigtab; is_pattern = uu___164_13571.is_pattern; instantiate_imp = uu___164_13571.instantiate_imp; effects = uu___164_13571.effects; generalize = uu___164_13571.generalize; letrecs = uu___164_13571.letrecs; top_level = uu___164_13571.top_level; check_uvars = uu___164_13571.check_uvars; use_eq = uu___164_13571.use_eq; is_iface = uu___164_13571.is_iface; admit = uu___164_13571.admit; lax = uu___164_13571.lax; lax_universes = uu___164_13571.lax_universes; failhard = uu___164_13571.failhard; nosynth = uu___164_13571.nosynth; type_of = uu___164_13571.type_of; universe_of = uu___164_13571.universe_of; use_bv_sorts = uu___164_13571.use_bv_sorts; qname_and_index = uu___164_13571.qname_and_index; proof_ns = ([])::e.proof_ns; synth = uu___164_13571.synth; is_native_tactic = uu___164_13571.is_native_tactic; identifier_info = uu___164_13571.identifier_info; dsenv = uu___164_13571.dsenv}))


let pop_proof_ns : env  ->  env = (fun e -> (match (e.proof_ns) with
| [] -> begin
(failwith "empty proof_ns stack!")
end
| (uu____13586)::rest -> begin
(

let uu___165_13590 = e
in {solver = uu___165_13590.solver; range = uu___165_13590.range; curmodule = uu___165_13590.curmodule; gamma = uu___165_13590.gamma; gamma_cache = uu___165_13590.gamma_cache; modules = uu___165_13590.modules; expected_typ = uu___165_13590.expected_typ; sigtab = uu___165_13590.sigtab; is_pattern = uu___165_13590.is_pattern; instantiate_imp = uu___165_13590.instantiate_imp; effects = uu___165_13590.effects; generalize = uu___165_13590.generalize; letrecs = uu___165_13590.letrecs; top_level = uu___165_13590.top_level; check_uvars = uu___165_13590.check_uvars; use_eq = uu___165_13590.use_eq; is_iface = uu___165_13590.is_iface; admit = uu___165_13590.admit; lax = uu___165_13590.lax; lax_universes = uu___165_13590.lax_universes; failhard = uu___165_13590.failhard; nosynth = uu___165_13590.nosynth; type_of = uu___165_13590.type_of; universe_of = uu___165_13590.universe_of; use_bv_sorts = uu___165_13590.use_bv_sorts; qname_and_index = uu___165_13590.qname_and_index; proof_ns = rest; synth = uu___165_13590.synth; is_native_tactic = uu___165_13590.is_native_tactic; identifier_info = uu___165_13590.identifier_info; dsenv = uu___165_13590.dsenv})
end))


let get_proof_ns : env  ->  proof_namespace = (fun e -> e.proof_ns)


let set_proof_ns : proof_namespace  ->  env  ->  env = (fun ns e -> (

let uu___166_13603 = e
in {solver = uu___166_13603.solver; range = uu___166_13603.range; curmodule = uu___166_13603.curmodule; gamma = uu___166_13603.gamma; gamma_cache = uu___166_13603.gamma_cache; modules = uu___166_13603.modules; expected_typ = uu___166_13603.expected_typ; sigtab = uu___166_13603.sigtab; is_pattern = uu___166_13603.is_pattern; instantiate_imp = uu___166_13603.instantiate_imp; effects = uu___166_13603.effects; generalize = uu___166_13603.generalize; letrecs = uu___166_13603.letrecs; top_level = uu___166_13603.top_level; check_uvars = uu___166_13603.check_uvars; use_eq = uu___166_13603.use_eq; is_iface = uu___166_13603.is_iface; admit = uu___166_13603.admit; lax = uu___166_13603.lax; lax_universes = uu___166_13603.lax_universes; failhard = uu___166_13603.failhard; nosynth = uu___166_13603.nosynth; type_of = uu___166_13603.type_of; universe_of = uu___166_13603.universe_of; use_bv_sorts = uu___166_13603.use_bv_sorts; qname_and_index = uu___166_13603.qname_and_index; proof_ns = ns; synth = uu___166_13603.synth; is_native_tactic = uu___166_13603.is_native_tactic; identifier_info = uu___166_13603.identifier_info; dsenv = uu___166_13603.dsenv}))


let string_of_proof_ns : env  ->  Prims.string = (fun env -> (

let string_of_proof_ns' = (fun pns -> (

let uu____13632 = (FStar_List.map (fun fpns -> (

let uu____13654 = (

let uu____13655 = (

let uu____13656 = (FStar_List.map (fun uu____13668 -> (match (uu____13668) with
| (p, b) -> begin
(Prims.strcat (match (b) with
| true -> begin
"+"
end
| uu____13681 -> begin
"-"
end) (FStar_String.concat "." p))
end)) fpns)
in (FStar_String.concat "," uu____13656))
in (Prims.strcat uu____13655 "]"))
in (Prims.strcat "[" uu____13654))) pns)
in (FStar_String.concat ";" uu____13632)))
in (string_of_proof_ns' env.proof_ns)))


let dummy_solver : solver_t = {init = (fun uu____13684 -> ()); push = (fun uu____13686 -> ()); pop = (fun uu____13688 -> ()); encode_modul = (fun uu____13691 uu____13692 -> ()); encode_sig = (fun uu____13695 uu____13696 -> ()); preprocess = (fun e g -> (

let uu____13702 = (

let uu____13709 = (FStar_Options.peek ())
in ((e), (g), (uu____13709)))
in (uu____13702)::[])); solve = (fun uu____13725 uu____13726 uu____13727 -> ()); is_trivial = (fun uu____13734 uu____13735 -> false); finish = (fun uu____13737 -> ()); refresh = (fun uu____13739 -> ())}





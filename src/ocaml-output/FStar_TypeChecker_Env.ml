
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
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; lax : Prims.bool; lax_universes : Prims.bool; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool; qname_and_index : (FStar_Ident.lident * Prims.int) FStar_Pervasives_Native.option; proof_ns : proof_namespace; synth : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term; is_native_tactic : FStar_Ident.lid  ->  Prims.bool} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; preprocess : env  ->  goal  ->  (env * goal * FStar_Options.optionstate) Prims.list; solve : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : (FStar_Syntax_Syntax.universe Prims.list * FStar_TypeChecker_Common.univ_ineq Prims.list); implicits : (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list}


let __proj__Mkenv__item__solver : env  ->  solver_t = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__solver
end))


let __proj__Mkenv__item__range : env  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__range
end))


let __proj__Mkenv__item__curmodule : env  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__curmodule
end))


let __proj__Mkenv__item__gamma : env  ->  binding Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__gamma
end))


let __proj__Mkenv__item__gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__gamma_cache
end))


let __proj__Mkenv__item__modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__modules
end))


let __proj__Mkenv__item__expected_typ : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__expected_typ
end))


let __proj__Mkenv__item__sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__sigtab
end))


let __proj__Mkenv__item__is_pattern : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__is_pattern
end))


let __proj__Mkenv__item__instantiate_imp : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__instantiate_imp
end))


let __proj__Mkenv__item__effects : env  ->  effects = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__effects
end))


let __proj__Mkenv__item__generalize : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__generalize
end))


let __proj__Mkenv__item__letrecs : env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__letrecs
end))


let __proj__Mkenv__item__top_level : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__top_level
end))


let __proj__Mkenv__item__check_uvars : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__check_uvars
end))


let __proj__Mkenv__item__use_eq : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__use_eq
end))


let __proj__Mkenv__item__is_iface : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__is_iface
end))


let __proj__Mkenv__item__admit : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__admit
end))


let __proj__Mkenv__item__lax : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__lax
end))


let __proj__Mkenv__item__lax_universes : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__lax_universes
end))


let __proj__Mkenv__item__type_of : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t) = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__type_of
end))


let __proj__Mkenv__item__universe_of : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__universe_of
end))


let __proj__Mkenv__item__use_bv_sorts : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__use_bv_sorts
end))


let __proj__Mkenv__item__qname_and_index : env  ->  (FStar_Ident.lident * Prims.int) FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__qname_and_index
end))


let __proj__Mkenv__item__proof_ns : env  ->  proof_namespace = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__proof_ns
end))


let __proj__Mkenv__item__synth : env  ->  env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__synth
end))


let __proj__Mkenv__item__is_native_tactic : env  ->  FStar_Ident.lid  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic} -> begin
__fname__is_native_tactic
end))


let __proj__Mksolver_t__item__init : solver_t  ->  env  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__init
end))


let __proj__Mksolver_t__item__push : solver_t  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__push
end))


let __proj__Mksolver_t__item__pop : solver_t  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__pop
end))


let __proj__Mksolver_t__item__mark : solver_t  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__mark
end))


let __proj__Mksolver_t__item__reset_mark : solver_t  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__reset_mark
end))


let __proj__Mksolver_t__item__commit_mark : solver_t  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__commit_mark
end))


let __proj__Mksolver_t__item__encode_modul : solver_t  ->  env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__encode_modul
end))


let __proj__Mksolver_t__item__encode_sig : solver_t  ->  env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__encode_sig
end))


let __proj__Mksolver_t__item__preprocess : solver_t  ->  env  ->  goal  ->  (env * goal * FStar_Options.optionstate) Prims.list = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__preprocess
end))


let __proj__Mksolver_t__item__solve : solver_t  ->  (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__solve
end))


let __proj__Mksolver_t__item__is_trivial : solver_t  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__is_trivial
end))


let __proj__Mksolver_t__item__finish : solver_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__finish
end))


let __proj__Mksolver_t__item__refresh : solver_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; is_trivial = __fname__is_trivial; finish = __fname__finish; refresh = __fname__refresh} -> begin
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
| (NoDelta, uu____4204) -> begin
true
end
| (Eager_unfolding_only, FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____4205), FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____4206), FStar_Syntax_Syntax.Visible_default) -> begin
true
end
| (Inlining, FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| uu____4207 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab : 'Auu____4216 . Prims.unit  ->  'Auu____4216 FStar_Util.smap = (fun uu____4222 -> (FStar_Util.smap_create default_table_size))


let new_gamma_cache : 'Auu____4227 . Prims.unit  ->  'Auu____4227 FStar_Util.smap = (fun uu____4233 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (

let uu____4282 = (new_gamma_cache ())
in (

let uu____4285 = (new_sigtab ())
in (

let uu____4288 = (

let uu____4289 = (FStar_Options.using_facts_from ())
in (match (uu____4289) with
| FStar_Pervasives_Native.Some (ns) -> begin
(

let uu____4299 = (

let uu____4308 = (FStar_List.map (fun s -> (((FStar_Ident.path_of_text s)), (true))) ns)
in (FStar_List.append uu____4308 (((([]), (false)))::[])))
in (uu____4299)::[])
end
| FStar_Pervasives_Native.None -> begin
([])::[]
end))
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = uu____4282; modules = []; expected_typ = FStar_Pervasives_Native.None; sigtab = uu____4285; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = FStar_Pervasives_Native.None; proof_ns = uu____4288; synth = (fun e g tau -> (failwith "no synthesizer available")); is_native_tactic = (fun uu____4412 -> false)}))))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


let query_indices : (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let push_query_indices : Prims.unit  ->  Prims.unit = (fun uu____4463 -> (

let uu____4464 = (FStar_ST.read query_indices)
in (match (uu____4464) with
| [] -> begin
(failwith "Empty query indices!")
end
| uu____4487 -> begin
(

let uu____4496 = (

let uu____4505 = (

let uu____4512 = (FStar_ST.read query_indices)
in (FStar_List.hd uu____4512))
in (

let uu____4535 = (FStar_ST.read query_indices)
in (uu____4505)::uu____4535))
in (FStar_ST.write query_indices uu____4496))
end)))


let pop_query_indices : Prims.unit  ->  Prims.unit = (fun uu____4569 -> (

let uu____4570 = (FStar_ST.read query_indices)
in (match (uu____4570) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd1)::tl1 -> begin
(FStar_ST.write query_indices tl1)
end)))


let add_query_index : (FStar_Ident.lident * Prims.int)  ->  Prims.unit = (fun uu____4630 -> (match (uu____4630) with
| (l, n1) -> begin
(

let uu____4637 = (FStar_ST.read query_indices)
in (match (uu____4637) with
| (hd1)::tl1 -> begin
(FStar_ST.write query_indices (((((l), (n1)))::hd1)::tl1))
end
| uu____4694 -> begin
(failwith "Empty query indices")
end))
end))


let peek_query_indices : Prims.unit  ->  (FStar_Ident.lident * Prims.int) Prims.list = (fun uu____4712 -> (

let uu____4713 = (FStar_ST.read query_indices)
in (FStar_List.hd uu____4713)))


let commit_query_index_mark : Prims.unit  ->  Prims.unit = (fun uu____4739 -> (

let uu____4740 = (FStar_ST.read query_indices)
in (match (uu____4740) with
| (hd1)::(uu____4758)::tl1 -> begin
(FStar_ST.write query_indices ((hd1)::tl1))
end
| uu____4806 -> begin
(failwith "Unmarked query index stack")
end)))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push_stack : env  ->  env = (fun env -> ((

let uu____4827 = (

let uu____4830 = (FStar_ST.read stack)
in (env)::uu____4830)
in (FStar_ST.write stack uu____4827));
(

let uu___117_4837 = env
in (

let uu____4838 = (FStar_Util.smap_copy (gamma_cache env))
in (

let uu____4841 = (FStar_Util.smap_copy (sigtab env))
in {solver = uu___117_4837.solver; range = uu___117_4837.range; curmodule = uu___117_4837.curmodule; gamma = uu___117_4837.gamma; gamma_cache = uu____4838; modules = uu___117_4837.modules; expected_typ = uu___117_4837.expected_typ; sigtab = uu____4841; is_pattern = uu___117_4837.is_pattern; instantiate_imp = uu___117_4837.instantiate_imp; effects = uu___117_4837.effects; generalize = uu___117_4837.generalize; letrecs = uu___117_4837.letrecs; top_level = uu___117_4837.top_level; check_uvars = uu___117_4837.check_uvars; use_eq = uu___117_4837.use_eq; is_iface = uu___117_4837.is_iface; admit = uu___117_4837.admit; lax = uu___117_4837.lax; lax_universes = uu___117_4837.lax_universes; type_of = uu___117_4837.type_of; universe_of = uu___117_4837.universe_of; use_bv_sorts = uu___117_4837.use_bv_sorts; qname_and_index = uu___117_4837.qname_and_index; proof_ns = uu___117_4837.proof_ns; synth = uu___117_4837.synth; is_native_tactic = uu___117_4837.is_native_tactic})));
))


let pop_stack : Prims.unit  ->  env = (fun uu____4847 -> (

let uu____4848 = (FStar_ST.read stack)
in (match (uu____4848) with
| (env)::tl1 -> begin
((FStar_ST.write stack tl1);
env;
)
end
| uu____4860 -> begin
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


let mark : env  ->  env = (fun env -> ((env.solver.mark "USER MARK");
(push_query_indices ());
(push_stack env);
))


let commit_mark : env  ->  env = (fun env -> ((commit_query_index_mark ());
(env.solver.commit_mark "USER MARK");
(

let uu____4900 = (pop_stack ())
in ());
env;
))


let reset_mark : env  ->  env = (fun env -> ((env.solver.reset_mark "USER MARK");
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

let uu____4928 = (FStar_All.pipe_right qix (FStar_List.tryFind (fun uu____4954 -> (match (uu____4954) with
| (m, uu____4960) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____4928) with
| FStar_Pervasives_Native.None -> begin
(

let next = (n1 + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___118_4967 = env
in {solver = uu___118_4967.solver; range = uu___118_4967.range; curmodule = uu___118_4967.curmodule; gamma = uu___118_4967.gamma; gamma_cache = uu___118_4967.gamma_cache; modules = uu___118_4967.modules; expected_typ = uu___118_4967.expected_typ; sigtab = uu___118_4967.sigtab; is_pattern = uu___118_4967.is_pattern; instantiate_imp = uu___118_4967.instantiate_imp; effects = uu___118_4967.effects; generalize = uu___118_4967.generalize; letrecs = uu___118_4967.letrecs; top_level = uu___118_4967.top_level; check_uvars = uu___118_4967.check_uvars; use_eq = uu___118_4967.use_eq; is_iface = uu___118_4967.is_iface; admit = uu___118_4967.admit; lax = uu___118_4967.lax; lax_universes = uu___118_4967.lax_universes; type_of = uu___118_4967.type_of; universe_of = uu___118_4967.universe_of; use_bv_sorts = uu___118_4967.use_bv_sorts; qname_and_index = FStar_Pervasives_Native.Some (((l), (next))); proof_ns = uu___118_4967.proof_ns; synth = uu___118_4967.synth; is_native_tactic = uu___118_4967.is_native_tactic});
))
end
| FStar_Pervasives_Native.Some (uu____4972, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___119_4980 = env
in {solver = uu___119_4980.solver; range = uu___119_4980.range; curmodule = uu___119_4980.curmodule; gamma = uu___119_4980.gamma; gamma_cache = uu___119_4980.gamma_cache; modules = uu___119_4980.modules; expected_typ = uu___119_4980.expected_typ; sigtab = uu___119_4980.sigtab; is_pattern = uu___119_4980.is_pattern; instantiate_imp = uu___119_4980.instantiate_imp; effects = uu___119_4980.effects; generalize = uu___119_4980.generalize; letrecs = uu___119_4980.letrecs; top_level = uu___119_4980.top_level; check_uvars = uu___119_4980.check_uvars; use_eq = uu___119_4980.use_eq; is_iface = uu___119_4980.is_iface; admit = uu___119_4980.admit; lax = uu___119_4980.lax; lax_universes = uu___119_4980.lax_universes; type_of = uu___119_4980.type_of; universe_of = uu___119_4980.universe_of; use_bv_sorts = uu___119_4980.use_bv_sorts; qname_and_index = FStar_Pervasives_Native.Some (((l), (next))); proof_ns = uu___119_4980.proof_ns; synth = uu___119_4980.synth; is_native_tactic = uu___119_4980.is_native_tactic});
))
end))
end)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> (match ((r = FStar_Range.dummyRange)) with
| true -> begin
e
end
| uu____5001 -> begin
(

let uu___120_5002 = e
in {solver = uu___120_5002.solver; range = r; curmodule = uu___120_5002.curmodule; gamma = uu___120_5002.gamma; gamma_cache = uu___120_5002.gamma_cache; modules = uu___120_5002.modules; expected_typ = uu___120_5002.expected_typ; sigtab = uu___120_5002.sigtab; is_pattern = uu___120_5002.is_pattern; instantiate_imp = uu___120_5002.instantiate_imp; effects = uu___120_5002.effects; generalize = uu___120_5002.generalize; letrecs = uu___120_5002.letrecs; top_level = uu___120_5002.top_level; check_uvars = uu___120_5002.check_uvars; use_eq = uu___120_5002.use_eq; is_iface = uu___120_5002.is_iface; admit = uu___120_5002.admit; lax = uu___120_5002.lax; lax_universes = uu___120_5002.lax_universes; type_of = uu___120_5002.type_of; universe_of = uu___120_5002.universe_of; use_bv_sorts = uu___120_5002.use_bv_sorts; qname_and_index = uu___120_5002.qname_and_index; proof_ns = uu___120_5002.proof_ns; synth = uu___120_5002.synth; is_native_tactic = uu___120_5002.is_native_tactic})
end))


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let uu___121_5025 = env
in {solver = uu___121_5025.solver; range = uu___121_5025.range; curmodule = lid; gamma = uu___121_5025.gamma; gamma_cache = uu___121_5025.gamma_cache; modules = uu___121_5025.modules; expected_typ = uu___121_5025.expected_typ; sigtab = uu___121_5025.sigtab; is_pattern = uu___121_5025.is_pattern; instantiate_imp = uu___121_5025.instantiate_imp; effects = uu___121_5025.effects; generalize = uu___121_5025.generalize; letrecs = uu___121_5025.letrecs; top_level = uu___121_5025.top_level; check_uvars = uu___121_5025.check_uvars; use_eq = uu___121_5025.use_eq; is_iface = uu___121_5025.is_iface; admit = uu___121_5025.admit; lax = uu___121_5025.lax; lax_universes = uu___121_5025.lax_universes; type_of = uu___121_5025.type_of; universe_of = uu___121_5025.universe_of; use_bv_sorts = uu___121_5025.use_bv_sorts; qname_and_index = uu___121_5025.qname_and_index; proof_ns = uu___121_5025.proof_ns; synth = uu___121_5025.synth; is_native_tactic = uu___121_5025.is_native_tactic}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v1 -> (

let uu____5056 = (FStar_Syntax_Print.bv_to_string v1)
in (FStar_Util.format1 "Variable \"%s\" not found" uu____5056)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun uu____5060 -> (

let uu____5061 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____5061)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), uu____5101) -> begin
(

let n1 = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n1 - i)), (u))))))
in (

let uu____5125 = (FStar_Syntax_Subst.subst vs t)
in ((us), (uu____5125)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun uu___105_5133 -> (match (uu___105_5133) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun uu____5157 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let uu____5172 = (inst_tscheme t)
in (match (uu____5172) with
| (us, t1) -> begin
(

let uu____5183 = (FStar_Syntax_Subst.set_use_range r t1)
in ((us), (uu____5183)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed uu____5199 -> (match (uu____5199) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs1 = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in ((match (((FStar_List.length insts) <> (FStar_List.length univs1))) with
| true -> begin
(

let uu____5214 = (

let uu____5215 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (

let uu____5216 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (

let uu____5217 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____5218 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" uu____5215 uu____5216 uu____5217 uu____5218)))))
in (failwith uu____5214))
end
| uu____5219 -> begin
()
end);
(

let uu____5220 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (FStar_Pervasives_Native.snd uu____5220));
))
end
| uu____5227 -> begin
(

let uu____5228 = (

let uu____5229 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" uu____5229))
in (failwith uu____5228))
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
| uu____5234 -> begin
false
end))


let uu___is_No : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____5239 -> begin
false
end))


let uu___is_Maybe : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____5244 -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in (match ((l.FStar_Ident.nsstr = cur.FStar_Ident.str)) with
| true -> begin
Yes
end
| uu____5254 -> begin
(match ((FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur1 = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l1 -> (match (((c), (l1))) with
| ([], uu____5280) -> begin
Maybe
end
| (uu____5287, []) -> begin
No
end
| ((hd1)::tl1, (hd')::tl') when (hd1.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl1 tl')
end
| uu____5306 -> begin
No
end))
in (aux cur1 lns))))
end
| uu____5315 -> begin
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

let found = (match ((cur_mod <> No)) with
| true -> begin
(

let uu____5413 = (FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)
in (match (uu____5413) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.find_map env.gamma (fun uu___106_5458 -> (match (uu___106_5458) with
| Binding_lid (l, t) -> begin
(match ((FStar_Ident.lid_equals lid l)) with
| true -> begin
(

let uu____5501 = (

let uu____5520 = (

let uu____5535 = (inst_tscheme t)
in FStar_Util.Inl (uu____5535))
in ((uu____5520), ((FStar_Ident.range_of_lid l))))
in FStar_Pervasives_Native.Some (uu____5501))
end
| uu____5582 -> begin
FStar_Pervasives_Native.None
end)
end
| Binding_sig (uu____5601, {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (ses, uu____5603); FStar_Syntax_Syntax.sigrng = uu____5604; FStar_Syntax_Syntax.sigquals = uu____5605; FStar_Syntax_Syntax.sigmeta = uu____5606; FStar_Syntax_Syntax.sigattrs = uu____5607}) -> begin
(FStar_Util.find_map ses (fun se -> (

let uu____5627 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____5627) with
| true -> begin
(cache ((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| uu____5658 -> begin
FStar_Pervasives_Native.None
end))))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____5673) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____5680 -> begin
(cache t)
end))
in (

let uu____5681 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____5681) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (l) -> begin
(maybe_cache ((FStar_Util.Inr (((s), (FStar_Pervasives_Native.None)))), ((FStar_Ident.range_of_lid l))))
end)))
end
| Binding_sig_inst (lids, s, us) -> begin
(

let uu____5756 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____5756) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (l) -> begin
FStar_Pervasives_Native.Some (((FStar_Util.Inr (((s), (FStar_Pervasives_Native.Some (us))))), ((FStar_Ident.range_of_lid l))))
end))
end
| uu____5842 -> begin
FStar_Pervasives_Native.None
end)))
end
| se -> begin
se
end))
end
| uu____5864 -> begin
FStar_Pervasives_Native.None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| uu____5921 -> begin
(

let uu____5922 = (find_in_sigtab env lid)
in (match (uu____5922) with
| FStar_Pervasives_Native.Some (se) -> begin
FStar_Pervasives_Native.Some (((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end)))))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____6021) -> begin
(add_sigelts env ses)
end
| uu____6030 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids);
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| uu____6044 -> begin
()
end);
))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) FStar_Pervasives_Native.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun uu___107_6073 -> (match (uu___107_6073) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
FStar_Pervasives_Native.Some (((id.FStar_Syntax_Syntax.sort), (id.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
end
| uu____6091 -> begin
FStar_Pervasives_Native.None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) * FStar_Range.range) FStar_Pervasives_Native.option = (fun se lid -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____6126, (lb)::[]), uu____6128) -> begin
(

let uu____6141 = (

let uu____6150 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____6159 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in ((uu____6150), (uu____6159))))
in FStar_Pervasives_Native.Some (uu____6141))
end
| FStar_Syntax_Syntax.Sig_let ((uu____6172, lbs), uu____6174) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____6210) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
(

let uu____6222 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____6222) with
| true -> begin
(

let uu____6233 = (

let uu____6242 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____6251 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____6242), (uu____6251))))
in FStar_Pervasives_Native.Some (uu____6233))
end
| uu____6264 -> begin
FStar_Pervasives_Native.None
end))
end)))
end
| uu____6273 -> begin
FStar_Pervasives_Native.None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) * FStar_Range.range) FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____6307 = (

let uu____6316 = (

let uu____6321 = (

let uu____6322 = (

let uu____6325 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders uu____6325))
in ((ne.FStar_Syntax_Syntax.univs), (uu____6322)))
in (inst_tscheme uu____6321))
in ((uu____6316), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____6307))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, uu____6345, uu____6346) -> begin
(

let uu____6351 = (

let uu____6360 = (

let uu____6365 = (

let uu____6366 = (

let uu____6369 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders uu____6369))
in ((us), (uu____6366)))
in (inst_tscheme uu____6365))
in ((uu____6360), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____6351))
end
| uu____6386 -> begin
FStar_Pervasives_Native.None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) * FStar_Range.range) FStar_Pervasives_Native.option = (fun env lid -> (

let mapper = (fun uu____6446 -> (match (uu____6446) with
| (lr, rng) -> begin
(match (lr) with
| FStar_Util.Inl (t) -> begin
FStar_Pervasives_Native.Some (((t), (rng)))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____6542, uvs, t, uu____6545, uu____6546, uu____6547); FStar_Syntax_Syntax.sigrng = uu____6548; FStar_Syntax_Syntax.sigquals = uu____6549; FStar_Syntax_Syntax.sigmeta = uu____6550; FStar_Syntax_Syntax.sigattrs = uu____6551}, FStar_Pervasives_Native.None) -> begin
(

let uu____6572 = (

let uu____6581 = (inst_tscheme ((uvs), (t)))
in ((uu____6581), (rng)))
in FStar_Pervasives_Native.Some (uu____6572))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t); FStar_Syntax_Syntax.sigrng = uu____6601; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____6603; FStar_Syntax_Syntax.sigattrs = uu____6604}, FStar_Pervasives_Native.None) -> begin
(

let uu____6621 = (

let uu____6622 = (in_cur_mod env l)
in (uu____6622 = Yes))
in (match (uu____6621) with
| true -> begin
(

let uu____6633 = ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface)
in (match (uu____6633) with
| true -> begin
(

let uu____6646 = (

let uu____6655 = (inst_tscheme ((uvs), (t)))
in ((uu____6655), (rng)))
in FStar_Pervasives_Native.Some (uu____6646))
end
| uu____6672 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____6681 -> begin
(

let uu____6682 = (

let uu____6691 = (inst_tscheme ((uvs), (t)))
in ((uu____6691), (rng)))
in FStar_Pervasives_Native.Some (uu____6682))
end))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____6712, uu____6713); FStar_Syntax_Syntax.sigrng = uu____6714; FStar_Syntax_Syntax.sigquals = uu____6715; FStar_Syntax_Syntax.sigmeta = uu____6716; FStar_Syntax_Syntax.sigattrs = uu____6717}, FStar_Pervasives_Native.None) -> begin
(match (tps) with
| [] -> begin
(

let uu____6756 = (

let uu____6765 = (inst_tscheme ((uvs), (k)))
in ((uu____6765), (rng)))
in FStar_Pervasives_Native.Some (uu____6756))
end
| uu____6782 -> begin
(

let uu____6783 = (

let uu____6792 = (

let uu____6797 = (

let uu____6798 = (

let uu____6801 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____6801))
in ((uvs), (uu____6798)))
in (inst_tscheme uu____6797))
in ((uu____6792), (rng)))
in FStar_Pervasives_Native.Some (uu____6783))
end)
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____6822, uu____6823); FStar_Syntax_Syntax.sigrng = uu____6824; FStar_Syntax_Syntax.sigquals = uu____6825; FStar_Syntax_Syntax.sigmeta = uu____6826; FStar_Syntax_Syntax.sigattrs = uu____6827}, FStar_Pervasives_Native.Some (us)) -> begin
(match (tps) with
| [] -> begin
(

let uu____6867 = (

let uu____6876 = (inst_tscheme_with ((uvs), (k)) us)
in ((uu____6876), (rng)))
in FStar_Pervasives_Native.Some (uu____6867))
end
| uu____6893 -> begin
(

let uu____6894 = (

let uu____6903 = (

let uu____6908 = (

let uu____6909 = (

let uu____6912 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____6912))
in ((uvs), (uu____6909)))
in (inst_tscheme_with uu____6908 us))
in ((uu____6903), (rng)))
in FStar_Pervasives_Native.Some (uu____6894))
end)
end
| FStar_Util.Inr (se) -> begin
(

let uu____6946 = (match (se) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____6967); FStar_Syntax_Syntax.sigrng = uu____6968; FStar_Syntax_Syntax.sigquals = uu____6969; FStar_Syntax_Syntax.sigmeta = uu____6970; FStar_Syntax_Syntax.sigattrs = uu____6971}, FStar_Pervasives_Native.None) -> begin
(lookup_type_of_let (FStar_Pervasives_Native.fst se) lid)
end
| uu____6986 -> begin
(effect_signature (FStar_Pervasives_Native.fst se))
end)
in (FStar_All.pipe_right uu____6946 (FStar_Util.map_option (fun uu____7034 -> (match (uu____7034) with
| (us_t, rng1) -> begin
((us_t), (rng1))
end)))))
end)
end))
in (

let uu____7065 = (

let uu____7076 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____7076 mapper))
in (match (uu____7065) with
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
FStar_Pervasives_Native.Some (((((us), ((

let uu___122_7169 = t
in {FStar_Syntax_Syntax.n = uu___122_7169.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = uu___122_7169.FStar_Syntax_Syntax.vars})))), (r)))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____7196 = (lookup_qname env l)
in (match (uu____7196) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____7235) -> begin
true
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) = (fun env bv -> (

let bvr = (FStar_Syntax_Syntax.range_of_bv bv)
in (

let uu____7285 = (try_lookup_bv env bv)
in (match (uu____7285) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7300 = (

let uu____7301 = (

let uu____7306 = (variable_not_found bv)
in ((uu____7306), (bvr)))
in FStar_Errors.Error (uu____7301))
in (FStar_Pervasives.raise uu____7300))
end
| FStar_Pervasives_Native.Some (t, r) -> begin
(

let uu____7317 = (FStar_Syntax_Subst.set_use_range bvr t)
in (

let uu____7318 = (FStar_Range.set_use_range r bvr)
in ((uu____7317), (uu____7318))))
end))))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) FStar_Pervasives_Native.option = (fun env l -> (

let uu____7337 = (try_lookup_lid_aux env l)
in (match (uu____7337) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
(

let use_range = (FStar_Ident.range_of_lid l)
in (

let r1 = (FStar_Range.set_use_range r use_range)
in (

let uu____7403 = (

let uu____7412 = (

let uu____7417 = (FStar_Syntax_Subst.set_use_range use_range t)
in ((us), (uu____7417)))
in ((uu____7412), (r1)))
in FStar_Pervasives_Native.Some (uu____7403))))
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) = (fun env l -> (

let uu____7446 = (try_lookup_lid env l)
in (match (uu____7446) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7473 = (

let uu____7474 = (

let uu____7479 = (name_not_found l)
in ((uu____7479), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____7474))
in (FStar_Pervasives.raise uu____7473))
end
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end)))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun uu___108_7517 -> (match (uu___108_7517) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| uu____7519 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env lid -> (

let uu____7536 = (lookup_qname env lid)
in (match (uu____7536) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____7565, uvs, t); FStar_Syntax_Syntax.sigrng = uu____7568; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____7570; FStar_Syntax_Syntax.sigattrs = uu____7571}, FStar_Pervasives_Native.None), uu____7572) -> begin
(

let uu____7621 = (

let uu____7632 = (

let uu____7637 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (uu____7637)))
in ((uu____7632), (q)))
in FStar_Pervasives_Native.Some (uu____7621))
end
| uu____7654 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____7693 = (lookup_qname env lid)
in (match (uu____7693) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____7718, uvs, t); FStar_Syntax_Syntax.sigrng = uu____7721; FStar_Syntax_Syntax.sigquals = uu____7722; FStar_Syntax_Syntax.sigmeta = uu____7723; FStar_Syntax_Syntax.sigattrs = uu____7724}, FStar_Pervasives_Native.None), uu____7725) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____7774 -> begin
(

let uu____7795 = (

let uu____7796 = (

let uu____7801 = (name_not_found lid)
in ((uu____7801), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____7796))
in (FStar_Pervasives.raise uu____7795))
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____7818 = (lookup_qname env lid)
in (match (uu____7818) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____7843, uvs, t, uu____7846, uu____7847, uu____7848); FStar_Syntax_Syntax.sigrng = uu____7849; FStar_Syntax_Syntax.sigquals = uu____7850; FStar_Syntax_Syntax.sigmeta = uu____7851; FStar_Syntax_Syntax.sigattrs = uu____7852}, FStar_Pervasives_Native.None), uu____7853) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____7906 -> begin
(

let uu____7927 = (

let uu____7928 = (

let uu____7933 = (name_not_found lid)
in ((uu____7933), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____7928))
in (FStar_Pervasives.raise uu____7927))
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  (Prims.bool * FStar_Ident.lident Prims.list) = (fun env lid -> (

let uu____7952 = (lookup_qname env lid)
in (match (uu____7952) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____7979, uu____7980, uu____7981, uu____7982, uu____7983, dcs); FStar_Syntax_Syntax.sigrng = uu____7985; FStar_Syntax_Syntax.sigquals = uu____7986; FStar_Syntax_Syntax.sigmeta = uu____7987; FStar_Syntax_Syntax.sigattrs = uu____7988}, uu____7989), uu____7990) -> begin
((true), (dcs))
end
| uu____8051 -> begin
((false), ([]))
end)))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____8082 = (lookup_qname env lid)
in (match (uu____8082) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____8103, uu____8104, uu____8105, l, uu____8107, uu____8108); FStar_Syntax_Syntax.sigrng = uu____8109; FStar_Syntax_Syntax.sigquals = uu____8110; FStar_Syntax_Syntax.sigmeta = uu____8111; FStar_Syntax_Syntax.sigattrs = uu____8112}, uu____8113), uu____8114) -> begin
l
end
| uu____8169 -> begin
(

let uu____8190 = (

let uu____8191 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" uu____8191))
in (failwith uu____8190))
end)))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (

let uu____8228 = (lookup_qname env lid)
in (match (uu____8228) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____8256) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____8307, lbs), uu____8309) when (visible se.FStar_Syntax_Syntax.sigquals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____8337 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____8337) with
| true -> begin
FStar_Pervasives_Native.Some (((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbdef)))
end
| uu____8360 -> begin
FStar_Pervasives_Native.None
end)))))
end
| uu____8369 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____8374 -> begin
FStar_Pervasives_Native.None
end))))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env ftv -> (

let uu____8411 = (lookup_qname env ftv)
in (match (uu____8411) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____8435) -> begin
(

let uu____8480 = (effect_signature se)
in (match (uu____8480) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((uu____8501, t), r) -> begin
(

let uu____8516 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t)
in FStar_Pervasives_Native.Some (uu____8516))
end))
end
| uu____8517 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (

let uu____8546 = (try_lookup_effect_lid env ftv)
in (match (uu____8546) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8549 = (

let uu____8550 = (

let uu____8555 = (name_not_found ftv)
in ((uu____8555), ((FStar_Ident.range_of_lid ftv))))
in FStar_Errors.Error (uu____8550))
in (FStar_Pervasives.raise uu____8549))
end
| FStar_Pervasives_Native.Some (k) -> begin
k
end)))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun env univ_insts lid0 -> (

let uu____8575 = (lookup_qname env lid0)
in (match (uu____8575) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs1, binders, c, uu____8606); FStar_Syntax_Syntax.sigrng = uu____8607; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____8609; FStar_Syntax_Syntax.sigattrs = uu____8610}, FStar_Pervasives_Native.None), uu____8611) -> begin
(

let lid1 = (

let uu____8665 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) (FStar_Ident.range_of_lid lid0))
in (FStar_Ident.set_lid_range lid uu____8665))
in (

let uu____8666 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___109_8670 -> (match (uu___109_8670) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____8671 -> begin
false
end))))
in (match (uu____8666) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____8682 -> begin
(

let insts = (match (((FStar_List.length univ_insts) = (FStar_List.length univs1))) with
| true -> begin
univ_insts
end
| uu____8684 -> begin
(

let uu____8685 = (

let uu____8686 = (

let uu____8687 = (get_range env)
in (FStar_Range.string_of_range uu____8687))
in (

let uu____8688 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____8689 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format3 "(%s) Unexpected instantiation of effect %s with %s universes" uu____8686 uu____8688 uu____8689))))
in (failwith uu____8685))
end)
in (match (((binders), (univs1))) with
| ([], uu____8696) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (uu____8713, (uu____8714)::(uu____8715)::uu____8716) -> begin
(

let uu____8721 = (

let uu____8722 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____8723 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" uu____8722 uu____8723)))
in (failwith uu____8721))
end
| uu____8730 -> begin
(

let uu____8735 = (

let uu____8740 = (

let uu____8741 = (FStar_Syntax_Util.arrow binders c)
in ((univs1), (uu____8741)))
in (inst_tscheme_with uu____8740 insts))
in (match (uu____8735) with
| (uu____8752, t) -> begin
(

let t1 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid1) t)
in (

let uu____8755 = (

let uu____8756 = (FStar_Syntax_Subst.compress t1)
in uu____8756.FStar_Syntax_Syntax.n)
in (match (uu____8755) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
FStar_Pervasives_Native.Some (((binders1), (c1)))
end
| uu____8803 -> begin
(failwith "Impossible")
end)))
end))
end))
end)))
end
| uu____8810 -> begin
FStar_Pervasives_Native.None
end)))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find1 = (fun l1 -> (

let uu____8852 = (lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l1)
in (match (uu____8852) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____8865, c) -> begin
(

let l2 = (FStar_Syntax_Util.comp_effect_name c)
in (

let uu____8872 = (find1 l2)
in (match (uu____8872) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (l2)
end
| FStar_Pervasives_Native.Some (l') -> begin
FStar_Pervasives_Native.Some (l')
end)))
end)))
in (

let res = (

let uu____8879 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____8879) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8883 = (find1 l)
in (match (uu____8883) with
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

let uu____8899 = (lookup_qname env l1)
in (match (uu____8899) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (uu____8922); FStar_Syntax_Syntax.sigrng = uu____8923; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____8925; FStar_Syntax_Syntax.sigattrs = uu____8926}, uu____8927), uu____8928) -> begin
q
end
| uu____8979 -> begin
[]
end))))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun uu____9015 -> (

let uu____9016 = (

let uu____9017 = (FStar_Util.string_of_int i)
in (

let uu____9018 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" uu____9017 uu____9018)))
in (failwith uu____9016)))
in (

let uu____9019 = (lookup_datacon env lid)
in (match (uu____9019) with
| (uu____9024, t) -> begin
(

let uu____9026 = (

let uu____9027 = (FStar_Syntax_Subst.compress t)
in uu____9027.FStar_Syntax_Syntax.n)
in (match (uu____9026) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____9031) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____9052 -> begin
(

let b = (FStar_List.nth binders i)
in (

let uu____9062 = (FStar_Syntax_Util.mk_field_projector_name lid (FStar_Pervasives_Native.fst b) i)
in (FStar_All.pipe_right uu____9062 FStar_Pervasives_Native.fst)))
end)
end
| uu____9071 -> begin
(fail ())
end))
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____9080 = (lookup_qname env l)
in (match (uu____9080) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____9101, uu____9102, uu____9103); FStar_Syntax_Syntax.sigrng = uu____9104; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____9106; FStar_Syntax_Syntax.sigattrs = uu____9107}, uu____9108), uu____9109) -> begin
(FStar_Util.for_some (fun uu___110_9162 -> (match (uu___110_9162) with
| FStar_Syntax_Syntax.Projector (uu____9163) -> begin
true
end
| uu____9168 -> begin
false
end)) quals)
end
| uu____9169 -> begin
false
end)))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____9198 = (lookup_qname env lid)
in (match (uu____9198) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____9219, uu____9220, uu____9221, uu____9222, uu____9223, uu____9224); FStar_Syntax_Syntax.sigrng = uu____9225; FStar_Syntax_Syntax.sigquals = uu____9226; FStar_Syntax_Syntax.sigmeta = uu____9227; FStar_Syntax_Syntax.sigattrs = uu____9228}, uu____9229), uu____9230) -> begin
true
end
| uu____9285 -> begin
false
end)))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____9314 = (lookup_qname env lid)
in (match (uu____9314) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____9335, uu____9336, uu____9337, uu____9338, uu____9339, uu____9340); FStar_Syntax_Syntax.sigrng = uu____9341; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____9343; FStar_Syntax_Syntax.sigattrs = uu____9344}, uu____9345), uu____9346) -> begin
(FStar_Util.for_some (fun uu___111_9407 -> (match (uu___111_9407) with
| FStar_Syntax_Syntax.RecordType (uu____9408) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____9417) -> begin
true
end
| uu____9426 -> begin
false
end)) quals)
end
| uu____9427 -> begin
false
end)))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____9456 = (lookup_qname env lid)
in (match (uu____9456) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____9477, uu____9478); FStar_Syntax_Syntax.sigrng = uu____9479; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____9481; FStar_Syntax_Syntax.sigattrs = uu____9482}, uu____9483), uu____9484) -> begin
(FStar_Util.for_some (fun uu___112_9541 -> (match (uu___112_9541) with
| FStar_Syntax_Syntax.Action (uu____9542) -> begin
true
end
| uu____9543 -> begin
false
end)) quals)
end
| uu____9544 -> begin
false
end)))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (fun env head1 -> (

let uu____9576 = (

let uu____9577 = (FStar_Syntax_Util.un_uinst head1)
in uu____9577.FStar_Syntax_Syntax.n)
in (match (uu____9576) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____9581 -> begin
false
end))))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun x -> (match ((FStar_Pervasives_Native.fst x)) with
| FStar_Util.Inl (uu____9648) -> begin
FStar_Pervasives_Native.Some (false)
end
| FStar_Util.Inr (se, uu____9664) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____9681) -> begin
FStar_Pervasives_Native.Some ((FStar_List.contains FStar_Syntax_Syntax.New se.FStar_Syntax_Syntax.sigquals))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____9688) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____9705 -> begin
FStar_Pervasives_Native.Some (false)
end)
end))
in (

let uu____9706 = (

let uu____9709 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____9709 mapper))
in (match (uu____9706) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
false
end))))


let num_inductive_ty_params : env  ->  FStar_Ident.lident  ->  Prims.int = (fun env lid -> (

let uu____9757 = (lookup_qname env lid)
in (match (uu____9757) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____9778, uu____9779, tps, uu____9781, uu____9782, uu____9783); FStar_Syntax_Syntax.sigrng = uu____9784; FStar_Syntax_Syntax.sigquals = uu____9785; FStar_Syntax_Syntax.sigmeta = uu____9786; FStar_Syntax_Syntax.sigattrs = uu____9787}, uu____9788), uu____9789) -> begin
(FStar_List.length tps)
end
| uu____9852 -> begin
(

let uu____9873 = (

let uu____9874 = (

let uu____9879 = (name_not_found lid)
in ((uu____9879), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____9874))
in (FStar_Pervasives.raise uu____9873))
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun uu____9921 -> (match (uu____9921) with
| (d, uu____9929) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)
end)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (

let uu____9942 = (effect_decl_opt env l)
in (match (uu____9942) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9957 = (

let uu____9958 = (

let uu____9963 = (name_not_found l)
in ((uu____9963), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____9958))
in (FStar_Pervasives.raise uu____9957))
end
| FStar_Pervasives_Native.Some (md) -> begin
(FStar_Pervasives_Native.fst md)
end)))


let identity_mlift : mlift = {mlift_wp = (fun t wp -> wp); mlift_term = FStar_Pervasives_Native.Some ((fun t wp e -> e))}


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> (match ((FStar_Ident.lid_equals l1 l2)) with
| true -> begin
((l1), (identity_mlift), (identity_mlift))
end
| uu____10021 -> begin
(match ((((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid)))) with
| true -> begin
((FStar_Parser_Const.effect_GTot_lid), (identity_mlift), (identity_mlift))
end
| uu____10028 -> begin
(

let uu____10029 = (FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun uu____10082 -> (match (uu____10082) with
| (m1, m2, uu____10095, uu____10096, uu____10097) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))
in (match (uu____10029) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10114 = (

let uu____10115 = (

let uu____10120 = (

let uu____10121 = (FStar_Syntax_Print.lid_to_string l1)
in (

let uu____10122 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" uu____10121 uu____10122)))
in ((uu____10120), (env.range)))
in FStar_Errors.Error (uu____10115))
in (FStar_Pervasives.raise uu____10114))
end
| FStar_Pervasives_Native.Some (uu____10129, uu____10130, m3, j1, j2) -> begin
((m3), (j1), (j2))
end))
end)
end))


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge FStar_Pervasives_Native.option = (fun env l1 l2 -> (match (((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)))) with
| true -> begin
FStar_Pervasives_Native.Some ({msource = l1; mtarget = l2; mlift = identity_mlift})
end
| uu____10160 -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end))


let wp_sig_aux : 'Auu____10173 . (FStar_Syntax_Syntax.eff_decl * 'Auu____10173) Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun decls m -> (

let uu____10200 = (FStar_All.pipe_right decls (FStar_Util.find_opt (fun uu____10226 -> (match (uu____10226) with
| (d, uu____10232) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)
end))))
in (match (uu____10200) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10243 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith uu____10243))
end
| FStar_Pervasives_Native.Some (md, _q) -> begin
(

let uu____10256 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (uu____10256) with
| (uu____10267, s) -> begin
(

let s1 = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s1.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, uu____10277))::((wp, uu____10279))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____10315 -> begin
(failwith "Impossible")
end))
end))
end)))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let null_wp_for_eff : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env eff_name res_u res_t -> (match ((FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' res_t (FStar_Pervasives_Native.Some (res_u)))
end
| uu____10356 -> begin
(match ((FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal' res_t (FStar_Pervasives_Native.Some (res_u)))
end
| uu____10357 -> begin
(

let eff_name1 = (norm_eff_name env eff_name)
in (

let ed = (get_effect_decl env eff_name1)
in (

let null_wp = (inst_effect_fun_with ((res_u)::[]) env ed ed.FStar_Syntax_Syntax.null_wp)
in (

let null_wp_res = (

let uu____10364 = (get_range env)
in (

let uu____10365 = (

let uu____10368 = (

let uu____10369 = (

let uu____10384 = (

let uu____10387 = (FStar_Syntax_Syntax.as_arg res_t)
in (uu____10387)::[])
in ((null_wp), (uu____10384)))
in FStar_Syntax_Syntax.Tm_app (uu____10369))
in (FStar_Syntax_Syntax.mk uu____10368))
in (uu____10365 FStar_Pervasives_Native.None uu____10364)))
in (

let uu____10393 = (

let uu____10394 = (

let uu____10403 = (FStar_Syntax_Syntax.as_arg null_wp_res)
in (uu____10403)::[])
in {FStar_Syntax_Syntax.comp_univs = (res_u)::[]; FStar_Syntax_Syntax.effect_name = eff_name1; FStar_Syntax_Syntax.result_typ = res_t; FStar_Syntax_Syntax.effect_args = uu____10394; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp uu____10393))))))
end)
end))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let effects = (

let uu___123_10414 = env.effects
in {decls = (((ne), (se.FStar_Syntax_Syntax.sigquals)))::env.effects.decls; order = uu___123_10414.order; joins = uu___123_10414.joins})
in (

let uu___124_10423 = env
in {solver = uu___124_10423.solver; range = uu___124_10423.range; curmodule = uu___124_10423.curmodule; gamma = uu___124_10423.gamma; gamma_cache = uu___124_10423.gamma_cache; modules = uu___124_10423.modules; expected_typ = uu___124_10423.expected_typ; sigtab = uu___124_10423.sigtab; is_pattern = uu___124_10423.is_pattern; instantiate_imp = uu___124_10423.instantiate_imp; effects = effects; generalize = uu___124_10423.generalize; letrecs = uu___124_10423.letrecs; top_level = uu___124_10423.top_level; check_uvars = uu___124_10423.check_uvars; use_eq = uu___124_10423.use_eq; is_iface = uu___124_10423.is_iface; admit = uu___124_10423.admit; lax = uu___124_10423.lax; lax_universes = uu___124_10423.lax_universes; type_of = uu___124_10423.type_of; universe_of = uu___124_10423.universe_of; use_bv_sorts = uu___124_10423.use_bv_sorts; qname_and_index = uu___124_10423.qname_and_index; proof_ns = uu___124_10423.proof_ns; synth = uu___124_10423.synth; is_native_tactic = uu___124_10423.is_native_tactic}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let compose_edges = (fun e1 e2 -> (

let composed_lift = (

let mlift_wp = (fun r wp1 -> (

let uu____10440 = (e1.mlift.mlift_wp r wp1)
in (e2.mlift.mlift_wp r uu____10440)))
in (

let mlift_term = (match (((e1.mlift.mlift_term), (e2.mlift.mlift_term))) with
| (FStar_Pervasives_Native.Some (l1), FStar_Pervasives_Native.Some (l2)) -> begin
FStar_Pervasives_Native.Some ((fun t wp e -> (

let uu____10530 = (e1.mlift.mlift_wp t wp)
in (

let uu____10531 = (l1 t wp e)
in (l2 t uu____10530 uu____10531)))))
end
| uu____10532 -> begin
FStar_Pervasives_Native.None
end)
in {mlift_wp = mlift_wp; mlift_term = mlift_term}))
in {msource = e1.msource; mtarget = e2.mtarget; mlift = composed_lift}))
in (

let mk_mlift_wp = (fun lift_t r wp1 -> (

let uu____10571 = (inst_tscheme lift_t)
in (match (uu____10571) with
| (uu____10578, lift_t1) -> begin
(

let uu____10580 = (

let uu____10583 = (

let uu____10584 = (

let uu____10599 = (

let uu____10602 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____10603 = (

let uu____10606 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____10606)::[])
in (uu____10602)::uu____10603))
in ((lift_t1), (uu____10599)))
in FStar_Syntax_Syntax.Tm_app (uu____10584))
in (FStar_Syntax_Syntax.mk uu____10583))
in (uu____10580 FStar_Pervasives_Native.None wp1.FStar_Syntax_Syntax.pos))
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

let uu____10647 = (inst_tscheme lift_t)
in (match (uu____10647) with
| (uu____10654, lift_t1) -> begin
(

let uu____10656 = (

let uu____10659 = (

let uu____10660 = (

let uu____10675 = (

let uu____10678 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____10679 = (

let uu____10682 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____10683 = (

let uu____10686 = (FStar_Syntax_Syntax.as_arg e)
in (uu____10686)::[])
in (uu____10682)::uu____10683))
in (uu____10678)::uu____10679))
in ((lift_t1), (uu____10675)))
in FStar_Syntax_Syntax.Tm_app (uu____10660))
in (FStar_Syntax_Syntax.mk uu____10659))
in (uu____10656 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
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

let uu____10724 = (

let uu____10725 = (FStar_Ident.lid_of_path ((s)::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____10725 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.fv_to_tm uu____10724)))
in (

let arg = (bogus_term "ARG")
in (

let wp = (bogus_term "WP")
in (

let e = (bogus_term "COMP")
in (

let uu____10729 = (

let uu____10730 = (l.mlift_wp arg wp)
in (FStar_Syntax_Print.term_to_string uu____10730))
in (

let uu____10731 = (

let uu____10732 = (FStar_Util.map_opt l.mlift_term (fun l1 -> (

let uu____10750 = (l1 arg wp e)
in (FStar_Syntax_Print.term_to_string uu____10750))))
in (FStar_Util.dflt "none" uu____10732))
in (FStar_Util.format2 "{ wp : %s ; term : %s }" uu____10729 uu____10731))))))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun uu____10776 -> (match (uu____10776) with
| (e, uu____10784) -> begin
e.FStar_Syntax_Syntax.mname
end))))
in (

let find_edge = (fun order1 uu____10803 -> (match (uu____10803) with
| (i, j) -> begin
(match ((FStar_Ident.lid_equals i j)) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _0_39 -> FStar_Pervasives_Native.Some (_0_39)))
end
| uu____10818 -> begin
(FStar_All.pipe_right order1 (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end)
end))
in (

let order1 = (

let fold_fun = (fun order1 k -> (

let uu____10841 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (match ((FStar_Ident.lid_equals i k)) with
| true -> begin
[]
end
| uu____10852 -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (match ((FStar_Ident.lid_equals j k)) with
| true -> begin
[]
end
| uu____10861 -> begin
(

let uu____10862 = (

let uu____10871 = (find_edge order1 ((i), (k)))
in (

let uu____10874 = (find_edge order1 ((k), (j)))
in ((uu____10871), (uu____10874))))
in (match (uu____10862) with
| (FStar_Pervasives_Native.Some (e1), FStar_Pervasives_Native.Some (e2)) -> begin
(

let uu____10889 = (compose_edges e1 e2)
in (uu____10889)::[])
end
| uu____10890 -> begin
[]
end))
end))))
end))))
in (FStar_List.append order1 uu____10841)))
in (FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)))
in (

let order2 = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order1)
in ((FStar_All.pipe_right order2 (FStar_List.iter (fun edge1 -> (

let uu____10919 = ((FStar_Ident.lid_equals edge1.msource FStar_Parser_Const.effect_DIV_lid) && (

let uu____10921 = (lookup_effect_quals env edge1.mtarget)
in (FStar_All.pipe_right uu____10921 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))))
in (match (uu____10919) with
| true -> begin
(

let uu____10926 = (

let uu____10927 = (

let uu____10932 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge1.mtarget.FStar_Ident.str)
in (

let uu____10933 = (get_range env)
in ((uu____10932), (uu____10933))))
in FStar_Errors.Error (uu____10927))
in (FStar_Pervasives.raise uu____10926))
end
| uu____10934 -> begin
()
end)))));
(

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (match ((FStar_Ident.lid_equals i j)) with
| true -> begin
FStar_Pervasives_Native.Some (((i), ((id_edge i)), ((id_edge i))))
end
| uu____11024 -> begin
(FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (

let uu____11058 = (

let uu____11067 = (find_edge order2 ((i), (k)))
in (

let uu____11070 = (find_edge order2 ((j), (k)))
in ((uu____11067), (uu____11070))))
in (match (uu____11058) with
| (FStar_Pervasives_Native.Some (ik), FStar_Pervasives_Native.Some (jk)) -> begin
(match (bopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((k), (ik), (jk)))
end
| FStar_Pervasives_Native.Some (ub, uu____11112, uu____11113) -> begin
(

let uu____11120 = (

let uu____11125 = (

let uu____11126 = (find_edge order2 ((k), (ub)))
in (FStar_Util.is_some uu____11126))
in (

let uu____11129 = (

let uu____11130 = (find_edge order2 ((ub), (k)))
in (FStar_Util.is_some uu____11130))
in ((uu____11125), (uu____11129))))
in (match (uu____11120) with
| (true, true) -> begin
(match ((FStar_Ident.lid_equals k ub)) with
| true -> begin
((FStar_Util.print_warning "Looking multiple times at the same upper bound candidate");
bopt;
)
end
| uu____11150 -> begin
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
| uu____11165 -> begin
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

let uu___125_11238 = env.effects
in {decls = uu___125_11238.decls; order = order2; joins = joins})
in (

let uu___126_11239 = env
in {solver = uu___126_11239.solver; range = uu___126_11239.range; curmodule = uu___126_11239.curmodule; gamma = uu___126_11239.gamma; gamma_cache = uu___126_11239.gamma_cache; modules = uu___126_11239.modules; expected_typ = uu___126_11239.expected_typ; sigtab = uu___126_11239.sigtab; is_pattern = uu___126_11239.is_pattern; instantiate_imp = uu___126_11239.instantiate_imp; effects = effects; generalize = uu___126_11239.generalize; letrecs = uu___126_11239.letrecs; top_level = uu___126_11239.top_level; check_uvars = uu___126_11239.check_uvars; use_eq = uu___126_11239.use_eq; is_iface = uu___126_11239.is_iface; admit = uu___126_11239.admit; lax = uu___126_11239.lax; lax_universes = uu___126_11239.lax_universes; type_of = uu___126_11239.type_of; universe_of = uu___126_11239.universe_of; use_bv_sorts = uu___126_11239.use_bv_sorts; qname_and_index = uu___126_11239.qname_and_index; proof_ns = uu___126_11239.proof_ns; synth = uu___126_11239.synth; is_native_tactic = uu___126_11239.is_native_tactic})));
))))))))))))))
end
| uu____11240 -> begin
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
| uu____11266 -> begin
c
end)
in (FStar_Syntax_Util.comp_to_comp_typ c1)))


let rec unfold_effect_abbrev : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (comp_to_comp_typ env comp)
in (

let uu____11276 = (lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name)
in (match (uu____11276) with
| FStar_Pervasives_Native.None -> begin
c
end
| FStar_Pervasives_Native.Some (binders, cdef) -> begin
(

let uu____11293 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (uu____11293) with
| (binders1, cdef1) -> begin
((match (((FStar_List.length binders1) <> ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))) with
| true -> begin
(

let uu____11311 = (

let uu____11312 = (

let uu____11317 = (

let uu____11318 = (FStar_Util.string_of_int (FStar_List.length binders1))
in (

let uu____11323 = (FStar_Util.string_of_int ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))
in (

let uu____11330 = (

let uu____11331 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Print.comp_to_string uu____11331))
in (FStar_Util.format3 "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s" uu____11318 uu____11323 uu____11330))))
in ((uu____11317), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____11312))
in (FStar_Pervasives.raise uu____11311))
end
| uu____11332 -> begin
()
end);
(

let inst1 = (

let uu____11336 = (

let uu____11345 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (uu____11345)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun uu____11362 uu____11363 -> (match (((uu____11362), (uu____11363))) with
| ((x, uu____11385), (t, uu____11387)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders1 uu____11336))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst1 cdef1)
in (

let c2 = (

let uu____11406 = (

let uu___127_11407 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = uu___127_11407.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___127_11407.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___127_11407.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___127_11407.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right uu____11406 FStar_Syntax_Syntax.mk_Comp))
in (unfold_effect_abbrev env c2))));
)
end))
end))))


let effect_repr_aux : Prims.bool  ->  env  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun only_reifiable env c u_c -> (

let uu____11432 = (

let uu____11441 = (norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (effect_decl_opt env uu____11441))
in (match (uu____11432) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____11466 = (only_reifiable && (

let uu____11468 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____11468))))
in (match (uu____11466) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____11477 -> begin
(match (ed.FStar_Syntax_Syntax.repr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| uu____11484 -> begin
(

let c1 = (unfold_effect_abbrev env c)
in (

let uu____11486 = (

let uu____11499 = (FStar_List.hd c1.FStar_Syntax_Syntax.effect_args)
in ((c1.FStar_Syntax_Syntax.result_typ), (uu____11499)))
in (match (uu____11486) with
| (res_typ, wp) -> begin
(

let repr = (inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____11545 = (

let uu____11548 = (get_range env)
in (

let uu____11549 = (

let uu____11552 = (

let uu____11553 = (

let uu____11568 = (

let uu____11571 = (FStar_Syntax_Syntax.as_arg res_typ)
in (uu____11571)::(wp)::[])
in ((repr), (uu____11568)))
in FStar_Syntax_Syntax.Tm_app (uu____11553))
in (FStar_Syntax_Syntax.mk uu____11552))
in (uu____11549 FStar_Pervasives_Native.None uu____11548)))
in FStar_Pervasives_Native.Some (uu____11545)))
end)))
end)
end))
end)))


let effect_repr : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (

let uu____11623 = (

let uu____11624 = (

let uu____11629 = (

let uu____11630 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format1 "Effect %s cannot be reified" uu____11630))
in (

let uu____11631 = (get_range env)
in ((uu____11629), (uu____11631))))
in FStar_Errors.Error (uu____11624))
in (FStar_Pervasives.raise uu____11623)))
in (

let uu____11632 = (effect_repr_aux true env c u_c)
in (match (uu____11632) with
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
| uu____11672 -> begin
false
end))


let is_reifiable_function : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____11681 = (

let uu____11682 = (FStar_Syntax_Subst.compress t)
in uu____11682.FStar_Syntax_Syntax.n)
in (match (uu____11681) with
| FStar_Syntax_Syntax.Tm_arrow (uu____11685, c) -> begin
(is_reifiable_comp env c)
end
| uu____11703 -> begin
false
end)))


let push_in_gamma : env  ->  binding  ->  env = (fun env s -> (

let rec push1 = (fun x rest -> (match (rest) with
| (Binding_sig (uu____11727))::uu____11728 -> begin
(x)::rest
end
| (Binding_sig_inst (uu____11737))::uu____11738 -> begin
(x)::rest
end
| [] -> begin
(x)::[]
end
| (local)::rest1 -> begin
(

let uu____11753 = (push1 x rest1)
in (local)::uu____11753)
end))
in (

let uu___128_11756 = env
in (

let uu____11757 = (push1 s env.gamma)
in {solver = uu___128_11756.solver; range = uu___128_11756.range; curmodule = uu___128_11756.curmodule; gamma = uu____11757; gamma_cache = uu___128_11756.gamma_cache; modules = uu___128_11756.modules; expected_typ = uu___128_11756.expected_typ; sigtab = uu___128_11756.sigtab; is_pattern = uu___128_11756.is_pattern; instantiate_imp = uu___128_11756.instantiate_imp; effects = uu___128_11756.effects; generalize = uu___128_11756.generalize; letrecs = uu___128_11756.letrecs; top_level = uu___128_11756.top_level; check_uvars = uu___128_11756.check_uvars; use_eq = uu___128_11756.use_eq; is_iface = uu___128_11756.is_iface; admit = uu___128_11756.admit; lax = uu___128_11756.lax; lax_universes = uu___128_11756.lax_universes; type_of = uu___128_11756.type_of; universe_of = uu___128_11756.universe_of; use_bv_sorts = uu___128_11756.use_bv_sorts; qname_and_index = uu___128_11756.qname_and_index; proof_ns = uu___128_11756.proof_ns; synth = uu___128_11756.synth; is_native_tactic = uu___128_11756.is_native_tactic}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env1 = (push_in_gamma env (Binding_sig ((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))))
in (build_lattice env1 s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env1 = (push_in_gamma env (Binding_sig_inst ((((FStar_Syntax_Util.lids_of_sigelt s)), (s), (us)))))
in (build_lattice env1 s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let uu___129_11794 = env
in {solver = uu___129_11794.solver; range = uu___129_11794.range; curmodule = uu___129_11794.curmodule; gamma = (b)::env.gamma; gamma_cache = uu___129_11794.gamma_cache; modules = uu___129_11794.modules; expected_typ = uu___129_11794.expected_typ; sigtab = uu___129_11794.sigtab; is_pattern = uu___129_11794.is_pattern; instantiate_imp = uu___129_11794.instantiate_imp; effects = uu___129_11794.effects; generalize = uu___129_11794.generalize; letrecs = uu___129_11794.letrecs; top_level = uu___129_11794.top_level; check_uvars = uu___129_11794.check_uvars; use_eq = uu___129_11794.use_eq; is_iface = uu___129_11794.is_iface; admit = uu___129_11794.admit; lax = uu___129_11794.lax; lax_universes = uu___129_11794.lax_universes; type_of = uu___129_11794.type_of; universe_of = uu___129_11794.universe_of; use_bv_sorts = uu___129_11794.use_bv_sorts; qname_and_index = uu___129_11794.qname_and_index; proof_ns = uu___129_11794.proof_ns; synth = uu___129_11794.synth; is_native_tactic = uu___129_11794.is_native_tactic}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let pop_bv : env  ->  (FStar_Syntax_Syntax.bv * env) FStar_Pervasives_Native.option = (fun env -> (match (env.gamma) with
| (Binding_var (x))::rest -> begin
FStar_Pervasives_Native.Some (((x), ((

let uu___130_11828 = env
in {solver = uu___130_11828.solver; range = uu___130_11828.range; curmodule = uu___130_11828.curmodule; gamma = rest; gamma_cache = uu___130_11828.gamma_cache; modules = uu___130_11828.modules; expected_typ = uu___130_11828.expected_typ; sigtab = uu___130_11828.sigtab; is_pattern = uu___130_11828.is_pattern; instantiate_imp = uu___130_11828.instantiate_imp; effects = uu___130_11828.effects; generalize = uu___130_11828.generalize; letrecs = uu___130_11828.letrecs; top_level = uu___130_11828.top_level; check_uvars = uu___130_11828.check_uvars; use_eq = uu___130_11828.use_eq; is_iface = uu___130_11828.is_iface; admit = uu___130_11828.admit; lax = uu___130_11828.lax; lax_universes = uu___130_11828.lax_universes; type_of = uu___130_11828.type_of; universe_of = uu___130_11828.universe_of; use_bv_sorts = uu___130_11828.use_bv_sorts; qname_and_index = uu___130_11828.qname_and_index; proof_ns = uu___130_11828.proof_ns; synth = uu___130_11828.synth; is_native_tactic = uu___130_11828.is_native_tactic}))))
end
| uu____11829 -> begin
FStar_Pervasives_Native.None
end))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env1 uu____11853 -> (match (uu____11853) with
| (x, uu____11859) -> begin
(push_bv env1 x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x1) -> begin
(

let x2 = (

let uu___131_11889 = x1
in {FStar_Syntax_Syntax.ppname = uu___131_11889.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___131_11889.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)})
in Binding_var (x2))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> ((add_sigelts env m.FStar_Syntax_Syntax.exports);
(

let uu___132_11924 = env
in {solver = uu___132_11924.solver; range = uu___132_11924.range; curmodule = uu___132_11924.curmodule; gamma = []; gamma_cache = uu___132_11924.gamma_cache; modules = (m)::env.modules; expected_typ = FStar_Pervasives_Native.None; sigtab = uu___132_11924.sigtab; is_pattern = uu___132_11924.is_pattern; instantiate_imp = uu___132_11924.instantiate_imp; effects = uu___132_11924.effects; generalize = uu___132_11924.generalize; letrecs = uu___132_11924.letrecs; top_level = uu___132_11924.top_level; check_uvars = uu___132_11924.check_uvars; use_eq = uu___132_11924.use_eq; is_iface = uu___132_11924.is_iface; admit = uu___132_11924.admit; lax = uu___132_11924.lax; lax_universes = uu___132_11924.lax_universes; type_of = uu___132_11924.type_of; universe_of = uu___132_11924.universe_of; use_bv_sorts = uu___132_11924.use_bv_sorts; qname_and_index = uu___132_11924.qname_and_index; proof_ns = uu___132_11924.proof_ns; synth = uu___132_11924.synth; is_native_tactic = uu___132_11924.is_native_tactic});
))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env1 x -> (push_local_binding env1 (Binding_univ (x)))) env xs))


let open_universes_in : env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term Prims.list  ->  (env * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term Prims.list) = (fun env uvs terms -> (

let uu____11961 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____11961) with
| (univ_subst, univ_vars) -> begin
(

let env' = (push_univ_vars env univ_vars)
in (

let uu____11989 = (FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms)
in ((env'), (univ_vars), (uu____11989))))
end)))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let uu___133_12004 = env
in {solver = uu___133_12004.solver; range = uu___133_12004.range; curmodule = uu___133_12004.curmodule; gamma = uu___133_12004.gamma; gamma_cache = uu___133_12004.gamma_cache; modules = uu___133_12004.modules; expected_typ = FStar_Pervasives_Native.Some (t); sigtab = uu___133_12004.sigtab; is_pattern = uu___133_12004.is_pattern; instantiate_imp = uu___133_12004.instantiate_imp; effects = uu___133_12004.effects; generalize = uu___133_12004.generalize; letrecs = uu___133_12004.letrecs; top_level = uu___133_12004.top_level; check_uvars = uu___133_12004.check_uvars; use_eq = false; is_iface = uu___133_12004.is_iface; admit = uu___133_12004.admit; lax = uu___133_12004.lax; lax_universes = uu___133_12004.lax_universes; type_of = uu___133_12004.type_of; universe_of = uu___133_12004.universe_of; use_bv_sorts = uu___133_12004.use_bv_sorts; qname_and_index = uu___133_12004.qname_and_index; proof_ns = uu___133_12004.proof_ns; synth = uu___133_12004.synth; is_native_tactic = uu___133_12004.is_native_tactic}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun env -> (match (env.expected_typ) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) = (fun env_ -> (

let uu____12030 = (expected_typ env_)
in (((

let uu___134_12036 = env_
in {solver = uu___134_12036.solver; range = uu___134_12036.range; curmodule = uu___134_12036.curmodule; gamma = uu___134_12036.gamma; gamma_cache = uu___134_12036.gamma_cache; modules = uu___134_12036.modules; expected_typ = FStar_Pervasives_Native.None; sigtab = uu___134_12036.sigtab; is_pattern = uu___134_12036.is_pattern; instantiate_imp = uu___134_12036.instantiate_imp; effects = uu___134_12036.effects; generalize = uu___134_12036.generalize; letrecs = uu___134_12036.letrecs; top_level = uu___134_12036.top_level; check_uvars = uu___134_12036.check_uvars; use_eq = false; is_iface = uu___134_12036.is_iface; admit = uu___134_12036.admit; lax = uu___134_12036.lax; lax_universes = uu___134_12036.lax_universes; type_of = uu___134_12036.type_of; universe_of = uu___134_12036.universe_of; use_bv_sorts = uu___134_12036.use_bv_sorts; qname_and_index = uu___134_12036.qname_and_index; proof_ns = uu___134_12036.proof_ns; synth = uu___134_12036.synth; is_native_tactic = uu___134_12036.is_native_tactic})), (uu____12030))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = (match ((FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Parser_Const.prims_lid)) with
| true -> begin
(

let uu____12051 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun uu___113_12061 -> (match (uu___113_12061) with
| Binding_sig (uu____12064, se) -> begin
(se)::[]
end
| uu____12070 -> begin
[]
end))))
in (FStar_All.pipe_right uu____12051 FStar_List.rev))
end
| uu____12075 -> begin
m.FStar_Syntax_Syntax.exports
end)
in ((add_sigelts env sigs);
(

let uu___135_12077 = env
in {solver = uu___135_12077.solver; range = uu___135_12077.range; curmodule = empty_lid; gamma = []; gamma_cache = uu___135_12077.gamma_cache; modules = (m)::env.modules; expected_typ = uu___135_12077.expected_typ; sigtab = uu___135_12077.sigtab; is_pattern = uu___135_12077.is_pattern; instantiate_imp = uu___135_12077.instantiate_imp; effects = uu___135_12077.effects; generalize = uu___135_12077.generalize; letrecs = uu___135_12077.letrecs; top_level = uu___135_12077.top_level; check_uvars = uu___135_12077.check_uvars; use_eq = uu___135_12077.use_eq; is_iface = uu___135_12077.is_iface; admit = uu___135_12077.admit; lax = uu___135_12077.lax; lax_universes = uu___135_12077.lax_universes; type_of = uu___135_12077.type_of; universe_of = uu___135_12077.universe_of; use_bv_sorts = uu___135_12077.use_bv_sorts; qname_and_index = uu___135_12077.qname_and_index; proof_ns = uu___135_12077.proof_ns; synth = uu___135_12077.synth; is_native_tactic = uu___135_12077.is_native_tactic});
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
| (Binding_univ (uu____12159))::tl1 -> begin
(aux out tl1)
end
| (Binding_lid (uu____12163, (uu____12164, t)))::tl1 -> begin
(

let uu____12179 = (

let uu____12186 = (FStar_Syntax_Free.uvars t)
in (ext out uu____12186))
in (aux uu____12179 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____12193; FStar_Syntax_Syntax.index = uu____12194; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____12201 = (

let uu____12208 = (FStar_Syntax_Free.uvars t)
in (ext out uu____12208))
in (aux uu____12201 tl1))
end
| (Binding_sig (uu____12215))::uu____12216 -> begin
out
end
| (Binding_sig_inst (uu____12225))::uu____12226 -> begin
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
| (Binding_sig_inst (uu____12282))::tl1 -> begin
(aux out tl1)
end
| (Binding_univ (uu____12294))::tl1 -> begin
(aux out tl1)
end
| (Binding_lid (uu____12298, (uu____12299, t)))::tl1 -> begin
(

let uu____12314 = (

let uu____12317 = (FStar_Syntax_Free.univs t)
in (ext out uu____12317))
in (aux uu____12314 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____12320; FStar_Syntax_Syntax.index = uu____12321; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____12328 = (

let uu____12331 = (FStar_Syntax_Free.univs t)
in (ext out uu____12331))
in (aux uu____12328 tl1))
end
| (Binding_sig (uu____12334))::uu____12335 -> begin
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
| (Binding_sig_inst (uu____12389))::tl1 -> begin
(aux out tl1)
end
| (Binding_univ (uname))::tl1 -> begin
(

let uu____12405 = (FStar_Util.set_add uname out)
in (aux uu____12405 tl1))
end
| (Binding_lid (uu____12408, (uu____12409, t)))::tl1 -> begin
(

let uu____12424 = (

let uu____12427 = (FStar_Syntax_Free.univnames t)
in (ext out uu____12427))
in (aux uu____12424 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____12430; FStar_Syntax_Syntax.index = uu____12431; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____12438 = (

let uu____12441 = (FStar_Syntax_Free.univnames t)
in (ext out uu____12441))
in (aux uu____12438 tl1))
end
| (Binding_sig (uu____12444))::uu____12445 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu___114_12473 -> (match (uu___114_12473) with
| Binding_var (x) -> begin
(x)::[]
end
| Binding_lid (uu____12477) -> begin
[]
end
| Binding_sig (uu____12482) -> begin
[]
end
| Binding_univ (uu____12489) -> begin
[]
end
| Binding_sig_inst (uu____12490) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____12507 = (

let uu____12510 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right uu____12510 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right uu____12507 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let print_gamma : env  ->  Prims.unit = (fun env -> (

let uu____12535 = (

let uu____12536 = (FStar_All.pipe_right env.gamma (FStar_List.map (fun uu___115_12546 -> (match (uu___115_12546) with
| Binding_var (x) -> begin
(

let uu____12548 = (FStar_Syntax_Print.bv_to_string x)
in (Prims.strcat "Binding_var " uu____12548))
end
| Binding_univ (u) -> begin
(Prims.strcat "Binding_univ " u.FStar_Ident.idText)
end
| Binding_lid (l, uu____12551) -> begin
(

let uu____12552 = (FStar_Ident.string_of_lid l)
in (Prims.strcat "Binding_lid " uu____12552))
end
| Binding_sig (ls, uu____12554) -> begin
(

let uu____12559 = (

let uu____12560 = (FStar_All.pipe_right ls (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____12560 (FStar_String.concat ", ")))
in (Prims.strcat "Binding_sig " uu____12559))
end
| Binding_sig_inst (ls, uu____12570, uu____12571) -> begin
(

let uu____12576 = (

let uu____12577 = (FStar_All.pipe_right ls (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____12577 (FStar_String.concat ", ")))
in (Prims.strcat "Binding_sig_inst " uu____12576))
end))))
in (FStar_All.pipe_right uu____12536 (FStar_String.concat "::\n")))
in (FStar_All.pipe_right uu____12535 (FStar_Util.print1 "%s\n"))))


let eq_gamma : env  ->  env  ->  Prims.bool = (fun env env' -> (

let uu____12596 = (FStar_Util.physical_equality env.gamma env'.gamma)
in (match (uu____12596) with
| true -> begin
true
end
| uu____12599 -> begin
(

let g = (all_binders env)
in (

let g' = (all_binders env')
in (((FStar_List.length g) = (FStar_List.length g')) && (FStar_List.forall2 (fun uu____12624 uu____12625 -> (match (((uu____12624), (uu____12625))) with
| ((b1, uu____12643), (b2, uu____12645)) -> begin
(FStar_Syntax_Syntax.bv_eq b1 b2)
end)) g g'))))
end)))


let fold_env : 'a . env  ->  ('a  ->  binding  ->  'a)  ->  'a  ->  'a = (fun env f a -> (FStar_List.fold_right (fun e a1 -> (f a1 e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys uu___116_12707 -> (match (uu___116_12707) with
| Binding_sig (lids, uu____12713) -> begin
(FStar_List.append lids keys)
end
| uu____12718 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun uu____12724 v1 keys1 -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)) keys)))


let should_enc_path : env  ->  Prims.string Prims.list  ->  Prims.bool = (fun env path -> (

let rec list_prefix = (fun xs ys -> (match (((xs), (ys))) with
| ([], uu____12760) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((x = y) && (list_prefix xs1 ys1))
end
| (uu____12779, uu____12780) -> begin
false
end))
in (

let rec should_enc_path' = (fun pns path1 -> (match (pns) with
| [] -> begin
true
end
| ((p, b))::pns1 -> begin
(

let uu____12817 = (list_prefix p path1)
in (match (uu____12817) with
| true -> begin
b
end
| uu____12818 -> begin
(should_enc_path' pns1 path1)
end))
end))
in (should_enc_path' (FStar_List.flatten env.proof_ns) path))))


let should_enc_lid : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____12831 = (FStar_Ident.path_of_lid lid)
in (should_enc_path env uu____12831)))


let cons_proof_ns : Prims.bool  ->  env  ->  name_prefix  ->  env = (fun b e path -> (match (e.proof_ns) with
| [] -> begin
(failwith "empty proof_ns stack!")
end
| (pns)::rest -> begin
(

let pns' = (((path), (b)))::pns
in (

let uu___136_12861 = e
in {solver = uu___136_12861.solver; range = uu___136_12861.range; curmodule = uu___136_12861.curmodule; gamma = uu___136_12861.gamma; gamma_cache = uu___136_12861.gamma_cache; modules = uu___136_12861.modules; expected_typ = uu___136_12861.expected_typ; sigtab = uu___136_12861.sigtab; is_pattern = uu___136_12861.is_pattern; instantiate_imp = uu___136_12861.instantiate_imp; effects = uu___136_12861.effects; generalize = uu___136_12861.generalize; letrecs = uu___136_12861.letrecs; top_level = uu___136_12861.top_level; check_uvars = uu___136_12861.check_uvars; use_eq = uu___136_12861.use_eq; is_iface = uu___136_12861.is_iface; admit = uu___136_12861.admit; lax = uu___136_12861.lax; lax_universes = uu___136_12861.lax_universes; type_of = uu___136_12861.type_of; universe_of = uu___136_12861.universe_of; use_bv_sorts = uu___136_12861.use_bv_sorts; qname_and_index = uu___136_12861.qname_and_index; proof_ns = (pns')::rest; synth = uu___136_12861.synth; is_native_tactic = uu___136_12861.is_native_tactic}))
end))


let add_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns true e path))


let rem_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns false e path))


let push_proof_ns : env  ->  env = (fun e -> (

let uu___137_12888 = e
in {solver = uu___137_12888.solver; range = uu___137_12888.range; curmodule = uu___137_12888.curmodule; gamma = uu___137_12888.gamma; gamma_cache = uu___137_12888.gamma_cache; modules = uu___137_12888.modules; expected_typ = uu___137_12888.expected_typ; sigtab = uu___137_12888.sigtab; is_pattern = uu___137_12888.is_pattern; instantiate_imp = uu___137_12888.instantiate_imp; effects = uu___137_12888.effects; generalize = uu___137_12888.generalize; letrecs = uu___137_12888.letrecs; top_level = uu___137_12888.top_level; check_uvars = uu___137_12888.check_uvars; use_eq = uu___137_12888.use_eq; is_iface = uu___137_12888.is_iface; admit = uu___137_12888.admit; lax = uu___137_12888.lax; lax_universes = uu___137_12888.lax_universes; type_of = uu___137_12888.type_of; universe_of = uu___137_12888.universe_of; use_bv_sorts = uu___137_12888.use_bv_sorts; qname_and_index = uu___137_12888.qname_and_index; proof_ns = ([])::e.proof_ns; synth = uu___137_12888.synth; is_native_tactic = uu___137_12888.is_native_tactic}))


let pop_proof_ns : env  ->  env = (fun e -> (match (e.proof_ns) with
| [] -> begin
(failwith "empty proof_ns stack!")
end
| (uu____12903)::rest -> begin
(

let uu___138_12907 = e
in {solver = uu___138_12907.solver; range = uu___138_12907.range; curmodule = uu___138_12907.curmodule; gamma = uu___138_12907.gamma; gamma_cache = uu___138_12907.gamma_cache; modules = uu___138_12907.modules; expected_typ = uu___138_12907.expected_typ; sigtab = uu___138_12907.sigtab; is_pattern = uu___138_12907.is_pattern; instantiate_imp = uu___138_12907.instantiate_imp; effects = uu___138_12907.effects; generalize = uu___138_12907.generalize; letrecs = uu___138_12907.letrecs; top_level = uu___138_12907.top_level; check_uvars = uu___138_12907.check_uvars; use_eq = uu___138_12907.use_eq; is_iface = uu___138_12907.is_iface; admit = uu___138_12907.admit; lax = uu___138_12907.lax; lax_universes = uu___138_12907.lax_universes; type_of = uu___138_12907.type_of; universe_of = uu___138_12907.universe_of; use_bv_sorts = uu___138_12907.use_bv_sorts; qname_and_index = uu___138_12907.qname_and_index; proof_ns = rest; synth = uu___138_12907.synth; is_native_tactic = uu___138_12907.is_native_tactic})
end))


let get_proof_ns : env  ->  proof_namespace = (fun e -> e.proof_ns)


let set_proof_ns : proof_namespace  ->  env  ->  env = (fun ns e -> (

let uu___139_12920 = e
in {solver = uu___139_12920.solver; range = uu___139_12920.range; curmodule = uu___139_12920.curmodule; gamma = uu___139_12920.gamma; gamma_cache = uu___139_12920.gamma_cache; modules = uu___139_12920.modules; expected_typ = uu___139_12920.expected_typ; sigtab = uu___139_12920.sigtab; is_pattern = uu___139_12920.is_pattern; instantiate_imp = uu___139_12920.instantiate_imp; effects = uu___139_12920.effects; generalize = uu___139_12920.generalize; letrecs = uu___139_12920.letrecs; top_level = uu___139_12920.top_level; check_uvars = uu___139_12920.check_uvars; use_eq = uu___139_12920.use_eq; is_iface = uu___139_12920.is_iface; admit = uu___139_12920.admit; lax = uu___139_12920.lax; lax_universes = uu___139_12920.lax_universes; type_of = uu___139_12920.type_of; universe_of = uu___139_12920.universe_of; use_bv_sorts = uu___139_12920.use_bv_sorts; qname_and_index = uu___139_12920.qname_and_index; proof_ns = ns; synth = uu___139_12920.synth; is_native_tactic = uu___139_12920.is_native_tactic}))


let string_of_proof_ns : env  ->  Prims.string = (fun env -> (

let string_of_proof_ns' = (fun pns -> (

let uu____12949 = (FStar_List.map (fun fpns -> (

let uu____12971 = (

let uu____12972 = (

let uu____12973 = (FStar_List.map (fun uu____12985 -> (match (uu____12985) with
| (p, b) -> begin
(Prims.strcat (match (b) with
| true -> begin
"+"
end
| uu____12998 -> begin
"-"
end) (FStar_String.concat "." p))
end)) fpns)
in (FStar_String.concat "," uu____12973))
in (Prims.strcat uu____12972 "]"))
in (Prims.strcat "[" uu____12971))) pns)
in (FStar_String.concat ";" uu____12949)))
in (string_of_proof_ns' env.proof_ns)))


let dummy_solver : solver_t = {init = (fun uu____13001 -> ()); push = (fun uu____13003 -> ()); pop = (fun uu____13005 -> ()); mark = (fun uu____13007 -> ()); reset_mark = (fun uu____13009 -> ()); commit_mark = (fun uu____13011 -> ()); encode_modul = (fun uu____13014 uu____13015 -> ()); encode_sig = (fun uu____13018 uu____13019 -> ()); preprocess = (fun e g -> (

let uu____13025 = (

let uu____13032 = (FStar_Options.peek ())
in ((e), (g), (uu____13032)))
in (uu____13025)::[])); solve = (fun uu____13048 uu____13049 uu____13050 -> ()); is_trivial = (fun uu____13057 uu____13058 -> false); finish = (fun uu____13060 -> ()); refresh = (fun uu____13062 -> ())}





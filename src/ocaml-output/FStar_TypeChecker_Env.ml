
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
| uu____35 -> begin
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
| uu____51 -> begin
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
| uu____74 -> begin
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
| uu____97 -> begin
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
| uu____115 -> begin
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
| uu____144 -> begin
false
end))


let uu___is_Inlining : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____149 -> begin
false
end))


let uu___is_Eager_unfolding_only : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding_only -> begin
true
end
| uu____154 -> begin
false
end))


let uu___is_Unfold : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unfold (_0) -> begin
true
end
| uu____160 -> begin
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
| uu____173 -> begin
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
| (NoDelta, uu____3489) -> begin
true
end
| (Eager_unfolding_only, FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____3490), FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____3491), FStar_Syntax_Syntax.Visible_default) -> begin
true
end
| (Inlining, FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| uu____3492 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab = (fun uu____3504 -> (FStar_Util.smap_create default_table_size))


let new_gamma_cache = (fun uu____3514 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (

let uu____3557 = (new_gamma_cache ())
in (

let uu____3559 = (new_sigtab ())
in (

let uu____3561 = (

let uu____3562 = (FStar_Options.using_facts_from ())
in (match (uu____3562) with
| FStar_Pervasives_Native.Some (ns) -> begin
(

let uu____3568 = (

let uu____3573 = (FStar_List.map (fun s -> (((FStar_Ident.path_of_text s)), (true))) ns)
in (FStar_List.append uu____3573 (((([]), (false)))::[])))
in (uu____3568)::[])
end
| FStar_Pervasives_Native.None -> begin
([])::[]
end))
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = uu____3557; modules = []; expected_typ = FStar_Pervasives_Native.None; sigtab = uu____3559; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = FStar_Pervasives_Native.None; proof_ns = uu____3561; synth = (fun e g tau -> (failwith "no synthesizer available")); is_native_tactic = (fun uu____3630 -> false)}))))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


let query_indices : (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let push_query_indices : Prims.unit  ->  Prims.unit = (fun uu____3663 -> (

let uu____3664 = (FStar_ST.read query_indices)
in (match (uu____3664) with
| [] -> begin
(failwith "Empty query indices!")
end
| uu____3678 -> begin
(

let uu____3683 = (

let uu____3688 = (

let uu____3692 = (FStar_ST.read query_indices)
in (FStar_List.hd uu____3692))
in (

let uu____3706 = (FStar_ST.read query_indices)
in (uu____3688)::uu____3706))
in (FStar_ST.write query_indices uu____3683))
end)))


let pop_query_indices : Prims.unit  ->  Prims.unit = (fun uu____3729 -> (

let uu____3730 = (FStar_ST.read query_indices)
in (match (uu____3730) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd1)::tl1 -> begin
(FStar_ST.write query_indices tl1)
end)))


let add_query_index : (FStar_Ident.lident * Prims.int)  ->  Prims.unit = (fun uu____3767 -> (match (uu____3767) with
| (l, n1) -> begin
(

let uu____3772 = (FStar_ST.read query_indices)
in (match (uu____3772) with
| (hd1)::tl1 -> begin
(FStar_ST.write query_indices (((((l), (n1)))::hd1)::tl1))
end
| uu____3806 -> begin
(failwith "Empty query indices")
end))
end))


let peek_query_indices : Prims.unit  ->  (FStar_Ident.lident * Prims.int) Prims.list = (fun uu____3817 -> (

let uu____3818 = (FStar_ST.read query_indices)
in (FStar_List.hd uu____3818)))


let commit_query_index_mark : Prims.unit  ->  Prims.unit = (fun uu____3835 -> (

let uu____3836 = (FStar_ST.read query_indices)
in (match (uu____3836) with
| (hd1)::(uu____3848)::tl1 -> begin
(FStar_ST.write query_indices ((hd1)::tl1))
end
| uu____3875 -> begin
(failwith "Unmarked query index stack")
end)))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push_stack : env  ->  env = (fun env -> ((

let uu____3890 = (

let uu____3892 = (FStar_ST.read stack)
in (env)::uu____3892)
in (FStar_ST.write stack uu____3890));
(

let uu___115_3900 = env
in (

let uu____3901 = (FStar_Util.smap_copy (gamma_cache env))
in (

let uu____3903 = (FStar_Util.smap_copy (sigtab env))
in {solver = uu___115_3900.solver; range = uu___115_3900.range; curmodule = uu___115_3900.curmodule; gamma = uu___115_3900.gamma; gamma_cache = uu____3901; modules = uu___115_3900.modules; expected_typ = uu___115_3900.expected_typ; sigtab = uu____3903; is_pattern = uu___115_3900.is_pattern; instantiate_imp = uu___115_3900.instantiate_imp; effects = uu___115_3900.effects; generalize = uu___115_3900.generalize; letrecs = uu___115_3900.letrecs; top_level = uu___115_3900.top_level; check_uvars = uu___115_3900.check_uvars; use_eq = uu___115_3900.use_eq; is_iface = uu___115_3900.is_iface; admit = uu___115_3900.admit; lax = uu___115_3900.lax; lax_universes = uu___115_3900.lax_universes; type_of = uu___115_3900.type_of; universe_of = uu___115_3900.universe_of; use_bv_sorts = uu___115_3900.use_bv_sorts; qname_and_index = uu___115_3900.qname_and_index; proof_ns = uu___115_3900.proof_ns; synth = uu___115_3900.synth; is_native_tactic = uu___115_3900.is_native_tactic})));
))


let pop_stack : Prims.unit  ->  env = (fun uu____3908 -> (

let uu____3909 = (FStar_ST.read stack)
in (match (uu____3909) with
| (env)::tl1 -> begin
((FStar_ST.write stack tl1);
env;
)
end
| uu____3921 -> begin
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

let uu____3960 = (pop_stack ())
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

let uu____3981 = (FStar_All.pipe_right qix (FStar_List.tryFind (fun uu____3996 -> (match (uu____3996) with
| (m, uu____4000) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____3981) with
| FStar_Pervasives_Native.None -> begin
(

let next = (n1 + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___116_4005 = env
in {solver = uu___116_4005.solver; range = uu___116_4005.range; curmodule = uu___116_4005.curmodule; gamma = uu___116_4005.gamma; gamma_cache = uu___116_4005.gamma_cache; modules = uu___116_4005.modules; expected_typ = uu___116_4005.expected_typ; sigtab = uu___116_4005.sigtab; is_pattern = uu___116_4005.is_pattern; instantiate_imp = uu___116_4005.instantiate_imp; effects = uu___116_4005.effects; generalize = uu___116_4005.generalize; letrecs = uu___116_4005.letrecs; top_level = uu___116_4005.top_level; check_uvars = uu___116_4005.check_uvars; use_eq = uu___116_4005.use_eq; is_iface = uu___116_4005.is_iface; admit = uu___116_4005.admit; lax = uu___116_4005.lax; lax_universes = uu___116_4005.lax_universes; type_of = uu___116_4005.type_of; universe_of = uu___116_4005.universe_of; use_bv_sorts = uu___116_4005.use_bv_sorts; qname_and_index = FStar_Pervasives_Native.Some (((l), (next))); proof_ns = uu___116_4005.proof_ns; synth = uu___116_4005.synth; is_native_tactic = uu___116_4005.is_native_tactic});
))
end
| FStar_Pervasives_Native.Some (uu____4008, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___117_4014 = env
in {solver = uu___117_4014.solver; range = uu___117_4014.range; curmodule = uu___117_4014.curmodule; gamma = uu___117_4014.gamma; gamma_cache = uu___117_4014.gamma_cache; modules = uu___117_4014.modules; expected_typ = uu___117_4014.expected_typ; sigtab = uu___117_4014.sigtab; is_pattern = uu___117_4014.is_pattern; instantiate_imp = uu___117_4014.instantiate_imp; effects = uu___117_4014.effects; generalize = uu___117_4014.generalize; letrecs = uu___117_4014.letrecs; top_level = uu___117_4014.top_level; check_uvars = uu___117_4014.check_uvars; use_eq = uu___117_4014.use_eq; is_iface = uu___117_4014.is_iface; admit = uu___117_4014.admit; lax = uu___117_4014.lax; lax_universes = uu___117_4014.lax_universes; type_of = uu___117_4014.type_of; universe_of = uu___117_4014.universe_of; use_bv_sorts = uu___117_4014.use_bv_sorts; qname_and_index = FStar_Pervasives_Native.Some (((l), (next))); proof_ns = uu___117_4014.proof_ns; synth = uu___117_4014.synth; is_native_tactic = uu___117_4014.is_native_tactic});
))
end))
end)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> (match ((r = FStar_Range.dummyRange)) with
| true -> begin
e
end
| uu____4033 -> begin
(

let uu___118_4034 = e
in {solver = uu___118_4034.solver; range = r; curmodule = uu___118_4034.curmodule; gamma = uu___118_4034.gamma; gamma_cache = uu___118_4034.gamma_cache; modules = uu___118_4034.modules; expected_typ = uu___118_4034.expected_typ; sigtab = uu___118_4034.sigtab; is_pattern = uu___118_4034.is_pattern; instantiate_imp = uu___118_4034.instantiate_imp; effects = uu___118_4034.effects; generalize = uu___118_4034.generalize; letrecs = uu___118_4034.letrecs; top_level = uu___118_4034.top_level; check_uvars = uu___118_4034.check_uvars; use_eq = uu___118_4034.use_eq; is_iface = uu___118_4034.is_iface; admit = uu___118_4034.admit; lax = uu___118_4034.lax; lax_universes = uu___118_4034.lax_universes; type_of = uu___118_4034.type_of; universe_of = uu___118_4034.universe_of; use_bv_sorts = uu___118_4034.use_bv_sorts; qname_and_index = uu___118_4034.qname_and_index; proof_ns = uu___118_4034.proof_ns; synth = uu___118_4034.synth; is_native_tactic = uu___118_4034.is_native_tactic})
end))


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let uu___119_4056 = env
in {solver = uu___119_4056.solver; range = uu___119_4056.range; curmodule = lid; gamma = uu___119_4056.gamma; gamma_cache = uu___119_4056.gamma_cache; modules = uu___119_4056.modules; expected_typ = uu___119_4056.expected_typ; sigtab = uu___119_4056.sigtab; is_pattern = uu___119_4056.is_pattern; instantiate_imp = uu___119_4056.instantiate_imp; effects = uu___119_4056.effects; generalize = uu___119_4056.generalize; letrecs = uu___119_4056.letrecs; top_level = uu___119_4056.top_level; check_uvars = uu___119_4056.check_uvars; use_eq = uu___119_4056.use_eq; is_iface = uu___119_4056.is_iface; admit = uu___119_4056.admit; lax = uu___119_4056.lax; lax_universes = uu___119_4056.lax_universes; type_of = uu___119_4056.type_of; universe_of = uu___119_4056.universe_of; use_bv_sorts = uu___119_4056.use_bv_sorts; qname_and_index = uu___119_4056.qname_and_index; proof_ns = uu___119_4056.proof_ns; synth = uu___119_4056.synth; is_native_tactic = uu___119_4056.is_native_tactic}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v1 -> (

let uu____4085 = (FStar_Syntax_Print.bv_to_string v1)
in (FStar_Util.format1 "Variable \"%s\" not found" uu____4085)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun uu____4089 -> (

let uu____4090 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____4090)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), uu____4116) -> begin
(

let n1 = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n1 - i)), (u))))))
in (

let uu____4138 = (FStar_Syntax_Subst.subst vs t)
in ((us), (uu____4138)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun uu___103_4144 -> (match (uu___103_4144) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun uu____4159 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let uu____4171 = (inst_tscheme t)
in (match (uu____4171) with
| (us, t1) -> begin
(

let uu____4178 = (FStar_Syntax_Subst.set_use_range r t1)
in ((us), (uu____4178)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed uu____4194 -> (match (uu____4194) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs1 = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in ((match (((FStar_List.length insts) <> (FStar_List.length univs1))) with
| true -> begin
(

let uu____4212 = (

let uu____4213 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (

let uu____4218 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (

let uu____4223 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____4224 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" uu____4213 uu____4218 uu____4223 uu____4224)))))
in (failwith uu____4212))
end
| uu____4225 -> begin
()
end);
(

let uu____4226 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (FStar_Pervasives_Native.snd uu____4226));
))
end
| uu____4230 -> begin
(

let uu____4231 = (

let uu____4232 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" uu____4232))
in (failwith uu____4231))
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
| uu____4237 -> begin
false
end))


let uu___is_No : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____4242 -> begin
false
end))


let uu___is_Maybe : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____4247 -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in (match ((l.FStar_Ident.nsstr = cur.FStar_Ident.str)) with
| true -> begin
Yes
end
| uu____4257 -> begin
(match ((FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur1 = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l1 -> (match (((c), (l1))) with
| ([], uu____4275) -> begin
Maybe
end
| (uu____4279, []) -> begin
No
end
| ((hd1)::tl1, (hd')::tl') when (hd1.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl1 tl')
end
| uu____4291 -> begin
No
end))
in (aux cur1 lns))))
end
| uu____4296 -> begin
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

let uu____4353 = (FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)
in (match (uu____4353) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.find_map env.gamma (fun uu___104_4378 -> (match (uu___104_4378) with
| Binding_lid (l, t) -> begin
(match ((FStar_Ident.lid_equals lid l)) with
| true -> begin
(

let uu____4401 = (

let uu____4411 = (

let uu____4419 = (inst_tscheme t)
in FStar_Util.Inl (uu____4419))
in ((uu____4411), ((FStar_Ident.range_of_lid l))))
in FStar_Pervasives_Native.Some (uu____4401))
end
| uu____4443 -> begin
FStar_Pervasives_Native.None
end)
end
| Binding_sig (uu____4453, {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (ses, uu____4455); FStar_Syntax_Syntax.sigrng = uu____4456; FStar_Syntax_Syntax.sigquals = uu____4457; FStar_Syntax_Syntax.sigmeta = uu____4458}) -> begin
(FStar_Util.find_map ses (fun se -> (

let uu____4469 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____4469) with
| true -> begin
(cache ((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| uu____4485 -> begin
FStar_Pervasives_Native.None
end))))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____4496) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____4500 -> begin
(cache t)
end))
in (

let uu____4501 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____4501) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (l) -> begin
(maybe_cache ((FStar_Util.Inr (((s), (FStar_Pervasives_Native.None)))), ((FStar_Ident.range_of_lid l))))
end)))
end
| Binding_sig_inst (lids, s, us) -> begin
(

let uu____4541 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____4541) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (l) -> begin
FStar_Pervasives_Native.Some (((FStar_Util.Inr (((s), (FStar_Pervasives_Native.Some (us))))), ((FStar_Ident.range_of_lid l))))
end))
end
| uu____4585 -> begin
FStar_Pervasives_Native.None
end)))
end
| se -> begin
se
end))
end
| uu____4597 -> begin
FStar_Pervasives_Native.None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| uu____4626 -> begin
(

let uu____4627 = ((cur_mod <> Yes) || (has_interface env env.curmodule))
in (match (uu____4627) with
| true -> begin
(

let uu____4638 = (find_in_sigtab env lid)
in (match (uu____4638) with
| FStar_Pervasives_Native.Some (se) -> begin
FStar_Pervasives_Native.Some (((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4682 -> begin
FStar_Pervasives_Native.None
end))
end)))))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____4704) -> begin
(add_sigelts env ses)
end
| uu____4709 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids);
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| uu____4721 -> begin
()
end);
))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) FStar_Pervasives_Native.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun uu___105_4743 -> (match (uu___105_4743) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
FStar_Pervasives_Native.Some (((id.FStar_Syntax_Syntax.sort), (id.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
end
| uu____4756 -> begin
FStar_Pervasives_Native.None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) * FStar_Range.range) FStar_Pervasives_Native.option = (fun se lid -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____4779, (lb)::[]), uu____4781, uu____4782) -> begin
(

let uu____4791 = (

let uu____4796 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____4802 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in ((uu____4796), (uu____4802))))
in FStar_Pervasives_Native.Some (uu____4791))
end
| FStar_Syntax_Syntax.Sig_let ((uu____4809, lbs), uu____4811, uu____4812) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____4834) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
(

let uu____4841 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____4841) with
| true -> begin
(

let uu____4847 = (

let uu____4852 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____4858 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____4852), (uu____4858))))
in FStar_Pervasives_Native.Some (uu____4847))
end
| uu____4865 -> begin
FStar_Pervasives_Native.None
end))
end)))
end
| uu____4870 -> begin
FStar_Pervasives_Native.None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) * FStar_Range.range) FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____4890 = (

let uu____4895 = (

let uu____4898 = (

let uu____4899 = (

let uu____4902 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders uu____4902))
in ((ne.FStar_Syntax_Syntax.univs), (uu____4899)))
in (inst_tscheme uu____4898))
in ((uu____4895), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____4890))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, uu____4916, uu____4917) -> begin
(

let uu____4920 = (

let uu____4925 = (

let uu____4928 = (

let uu____4929 = (

let uu____4932 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders uu____4932))
in ((us), (uu____4929)))
in (inst_tscheme uu____4928))
in ((uu____4925), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____4920))
end
| uu____4943 -> begin
FStar_Pervasives_Native.None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) * FStar_Range.range) FStar_Pervasives_Native.option = (fun env lid -> (

let mapper = (fun uu____4980 -> (match (uu____4980) with
| (lr, rng) -> begin
(match (lr) with
| FStar_Util.Inl (t) -> begin
FStar_Pervasives_Native.Some (((t), (rng)))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____5030, uvs, t, uu____5033, uu____5034, uu____5035); FStar_Syntax_Syntax.sigrng = uu____5036; FStar_Syntax_Syntax.sigquals = uu____5037; FStar_Syntax_Syntax.sigmeta = uu____5038}, FStar_Pervasives_Native.None) -> begin
(

let uu____5048 = (

let uu____5053 = (inst_tscheme ((uvs), (t)))
in ((uu____5053), (rng)))
in FStar_Pervasives_Native.Some (uu____5048))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t); FStar_Syntax_Syntax.sigrng = uu____5065; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____5067}, FStar_Pervasives_Native.None) -> begin
(

let uu____5075 = (

let uu____5076 = (in_cur_mod env l)
in (uu____5076 = Yes))
in (match (uu____5075) with
| true -> begin
(

let uu____5082 = ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface)
in (match (uu____5082) with
| true -> begin
(

let uu____5089 = (

let uu____5094 = (inst_tscheme ((uvs), (t)))
in ((uu____5094), (rng)))
in FStar_Pervasives_Native.Some (uu____5089))
end
| uu____5103 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____5108 -> begin
(

let uu____5109 = (

let uu____5114 = (inst_tscheme ((uvs), (t)))
in ((uu____5114), (rng)))
in FStar_Pervasives_Native.Some (uu____5109))
end))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____5127, uu____5128); FStar_Syntax_Syntax.sigrng = uu____5129; FStar_Syntax_Syntax.sigquals = uu____5130; FStar_Syntax_Syntax.sigmeta = uu____5131}, FStar_Pervasives_Native.None) -> begin
(match (tps) with
| [] -> begin
(

let uu____5150 = (

let uu____5155 = (inst_tscheme ((uvs), (k)))
in ((uu____5155), (rng)))
in FStar_Pervasives_Native.Some (uu____5150))
end
| uu____5164 -> begin
(

let uu____5165 = (

let uu____5170 = (

let uu____5173 = (

let uu____5174 = (

let uu____5177 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____5177))
in ((uvs), (uu____5174)))
in (inst_tscheme uu____5173))
in ((uu____5170), (rng)))
in FStar_Pervasives_Native.Some (uu____5165))
end)
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____5192, uu____5193); FStar_Syntax_Syntax.sigrng = uu____5194; FStar_Syntax_Syntax.sigquals = uu____5195; FStar_Syntax_Syntax.sigmeta = uu____5196}, FStar_Pervasives_Native.Some (us)) -> begin
(match (tps) with
| [] -> begin
(

let uu____5216 = (

let uu____5221 = (inst_tscheme_with ((uvs), (k)) us)
in ((uu____5221), (rng)))
in FStar_Pervasives_Native.Some (uu____5216))
end
| uu____5230 -> begin
(

let uu____5231 = (

let uu____5236 = (

let uu____5239 = (

let uu____5240 = (

let uu____5243 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____5243))
in ((uvs), (uu____5240)))
in (inst_tscheme_with uu____5239 us))
in ((uu____5236), (rng)))
in FStar_Pervasives_Native.Some (uu____5231))
end)
end
| FStar_Util.Inr (se) -> begin
(

let uu____5263 = (match (se) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____5274); FStar_Syntax_Syntax.sigrng = uu____5275; FStar_Syntax_Syntax.sigquals = uu____5276; FStar_Syntax_Syntax.sigmeta = uu____5277}, FStar_Pervasives_Native.None) -> begin
(lookup_type_of_let (FStar_Pervasives_Native.fst se) lid)
end
| uu____5286 -> begin
(effect_signature (FStar_Pervasives_Native.fst se))
end)
in (FStar_All.pipe_right uu____5263 (FStar_Util.map_option (fun uu____5312 -> (match (uu____5312) with
| (us_t, rng1) -> begin
((us_t), (rng1))
end)))))
end)
end))
in (

let uu____5329 = (

let uu____5335 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____5335 mapper))
in (match (uu____5329) with
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
FStar_Pervasives_Native.Some (((((us), ((

let uu___120_5388 = t
in {FStar_Syntax_Syntax.n = uu___120_5388.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___120_5388.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = uu___120_5388.FStar_Syntax_Syntax.vars})))), (r)))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____5411 = (lookup_qname env l)
in (match (uu____5411) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____5431) -> begin
true
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) = (fun env bv -> (

let bvr = (FStar_Syntax_Syntax.range_of_bv bv)
in (

let uu____5461 = (try_lookup_bv env bv)
in (match (uu____5461) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5469 = (

let uu____5470 = (

let uu____5473 = (variable_not_found bv)
in ((uu____5473), (bvr)))
in FStar_Errors.Error (uu____5470))
in (FStar_Pervasives.raise uu____5469))
end
| FStar_Pervasives_Native.Some (t, r) -> begin
(

let uu____5480 = (FStar_Syntax_Subst.set_use_range bvr t)
in (

let uu____5481 = (FStar_Range.set_use_range r bvr)
in ((uu____5480), (uu____5481))))
end))))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) FStar_Pervasives_Native.option = (fun env l -> (

let uu____5495 = (try_lookup_lid_aux env l)
in (match (uu____5495) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
(

let use_range = (FStar_Ident.range_of_lid l)
in (

let r1 = (FStar_Range.set_use_range r use_range)
in (

let uu____5537 = (

let uu____5542 = (

let uu____5545 = (FStar_Syntax_Subst.set_use_range use_range t)
in ((us), (uu____5545)))
in ((uu____5542), (r1)))
in FStar_Pervasives_Native.Some (uu____5537))))
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) = (fun env l -> (

let uu____5564 = (try_lookup_lid env l)
in (match (uu____5564) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5578 = (

let uu____5579 = (

let uu____5582 = (name_not_found l)
in ((uu____5582), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____5579))
in (FStar_Pervasives.raise uu____5578))
end
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end)))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun uu___106_5607 -> (match (uu___106_5607) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| uu____5609 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env lid -> (

let uu____5622 = (lookup_qname env lid)
in (match (uu____5622) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____5637, uvs, t); FStar_Syntax_Syntax.sigrng = uu____5640; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____5642}, FStar_Pervasives_Native.None), uu____5643) -> begin
(

let uu____5667 = (

let uu____5673 = (

let uu____5676 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (uu____5676)))
in ((uu____5673), (q)))
in FStar_Pervasives_Native.Some (uu____5667))
end
| uu____5685 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____5709 = (lookup_qname env lid)
in (match (uu____5709) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____5722, uvs, t); FStar_Syntax_Syntax.sigrng = uu____5725; FStar_Syntax_Syntax.sigquals = uu____5726; FStar_Syntax_Syntax.sigmeta = uu____5727}, FStar_Pervasives_Native.None), uu____5728) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____5752 -> begin
(

let uu____5763 = (

let uu____5764 = (

let uu____5767 = (name_not_found lid)
in ((uu____5767), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____5764))
in (FStar_Pervasives.raise uu____5763))
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____5780 = (lookup_qname env lid)
in (match (uu____5780) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____5793, uvs, t, uu____5796, uu____5797, uu____5798); FStar_Syntax_Syntax.sigrng = uu____5799; FStar_Syntax_Syntax.sigquals = uu____5800; FStar_Syntax_Syntax.sigmeta = uu____5801}, FStar_Pervasives_Native.None), uu____5802) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____5828 -> begin
(

let uu____5839 = (

let uu____5840 = (

let uu____5843 = (name_not_found lid)
in ((uu____5843), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____5840))
in (FStar_Pervasives.raise uu____5839))
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  (Prims.bool * FStar_Ident.lident Prims.list) = (fun env lid -> (

let uu____5857 = (lookup_qname env lid)
in (match (uu____5857) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____5871, uu____5872, uu____5873, uu____5874, uu____5875, dcs); FStar_Syntax_Syntax.sigrng = uu____5877; FStar_Syntax_Syntax.sigquals = uu____5878; FStar_Syntax_Syntax.sigmeta = uu____5879}, uu____5880), uu____5881) -> begin
((true), (dcs))
end
| uu____5911 -> begin
((false), ([]))
end)))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____5931 = (lookup_qname env lid)
in (match (uu____5931) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____5942, uu____5943, uu____5944, l, uu____5946, uu____5947); FStar_Syntax_Syntax.sigrng = uu____5948; FStar_Syntax_Syntax.sigquals = uu____5949; FStar_Syntax_Syntax.sigmeta = uu____5950}, uu____5951), uu____5952) -> begin
l
end
| uu____5979 -> begin
(

let uu____5990 = (

let uu____5991 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" uu____5991))
in (failwith uu____5990))
end)))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (

let uu____6019 = (lookup_qname env lid)
in (match (uu____6019) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____6034) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____6060, lbs), uu____6062, uu____6063) when (visible se.FStar_Syntax_Syntax.sigquals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____6083 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____6083) with
| true -> begin
FStar_Pervasives_Native.Some (((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbdef)))
end
| uu____6098 -> begin
FStar_Pervasives_Native.None
end)))))
end
| uu____6104 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____6107 -> begin
FStar_Pervasives_Native.None
end))))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env ftv -> (

let uu____6130 = (lookup_qname env ftv)
in (match (uu____6130) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____6143) -> begin
(

let uu____6166 = (effect_signature se)
in (match (uu____6166) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((uu____6177, t), r) -> begin
(

let uu____6186 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t)
in FStar_Pervasives_Native.Some (uu____6186))
end))
end
| uu____6187 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (

let uu____6206 = (try_lookup_effect_lid env ftv)
in (match (uu____6206) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6208 = (

let uu____6209 = (

let uu____6212 = (name_not_found ftv)
in ((uu____6212), ((FStar_Ident.range_of_lid ftv))))
in FStar_Errors.Error (uu____6209))
in (FStar_Pervasives.raise uu____6208))
end
| FStar_Pervasives_Native.Some (k) -> begin
k
end)))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun env univ_insts lid0 -> (

let uu____6229 = (lookup_qname env lid0)
in (match (uu____6229) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs1, binders, c, uu____6247); FStar_Syntax_Syntax.sigrng = uu____6248; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____6250}, FStar_Pervasives_Native.None), uu____6251) -> begin
(

let lid1 = (

let uu____6278 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) (FStar_Ident.range_of_lid lid0))
in (FStar_Ident.set_lid_range lid uu____6278))
in (

let uu____6279 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___107_6282 -> (match (uu___107_6282) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____6283 -> begin
false
end))))
in (match (uu____6279) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____6289 -> begin
(

let insts = (match (((FStar_List.length univ_insts) = (FStar_List.length univs1))) with
| true -> begin
univ_insts
end
| uu____6299 -> begin
(

let uu____6300 = (

let uu____6301 = (

let uu____6302 = (get_range env)
in (FStar_Range.string_of_range uu____6302))
in (

let uu____6303 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____6304 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format3 "(%s) Unexpected instantiation of effect %s with %s universes" uu____6301 uu____6303 uu____6304))))
in (failwith uu____6300))
end)
in (match (((binders), (univs1))) with
| ([], uu____6312) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (uu____6321, (uu____6322)::(uu____6323)::uu____6324) -> begin
(

let uu____6327 = (

let uu____6328 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____6329 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" uu____6328 uu____6329)))
in (failwith uu____6327))
end
| uu____6337 -> begin
(

let uu____6340 = (

let uu____6343 = (

let uu____6344 = (FStar_Syntax_Util.arrow binders c)
in ((univs1), (uu____6344)))
in (inst_tscheme_with uu____6343 insts))
in (match (uu____6340) with
| (uu____6352, t) -> begin
(

let t1 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid1) t)
in (

let uu____6355 = (

let uu____6356 = (FStar_Syntax_Subst.compress t1)
in uu____6356.FStar_Syntax_Syntax.n)
in (match (uu____6355) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
FStar_Pervasives_Native.Some (((binders1), (c1)))
end
| uu____6386 -> begin
(failwith "Impossible")
end)))
end))
end))
end)))
end
| uu____6390 -> begin
FStar_Pervasives_Native.None
end)))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find1 = (fun l1 -> (

let uu____6418 = (lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l1)
in (match (uu____6418) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____6425, c) -> begin
(

let l2 = (FStar_Syntax_Util.comp_effect_name c)
in (

let uu____6430 = (find1 l2)
in (match (uu____6430) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (l2)
end
| FStar_Pervasives_Native.Some (l') -> begin
FStar_Pervasives_Native.Some (l')
end)))
end)))
in (

let res = (

let uu____6435 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____6435) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6438 = (find1 l)
in (match (uu____6438) with
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

let uu____6452 = (lookup_qname env l1)
in (match (uu____6452) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (uu____6464); FStar_Syntax_Syntax.sigrng = uu____6465; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____6467}, uu____6468), uu____6469) -> begin
q
end
| uu____6494 -> begin
[]
end))))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun uu____6520 -> (

let uu____6521 = (

let uu____6522 = (FStar_Util.string_of_int i)
in (

let uu____6523 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" uu____6522 uu____6523)))
in (failwith uu____6521)))
in (

let uu____6524 = (lookup_datacon env lid)
in (match (uu____6524) with
| (uu____6527, t) -> begin
(

let uu____6529 = (

let uu____6530 = (FStar_Syntax_Subst.compress t)
in uu____6530.FStar_Syntax_Syntax.n)
in (match (uu____6529) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____6534) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____6551 -> begin
(

let b = (FStar_List.nth binders i)
in (

let uu____6557 = (FStar_Syntax_Util.mk_field_projector_name lid (FStar_Pervasives_Native.fst b) i)
in (FStar_All.pipe_right uu____6557 FStar_Pervasives_Native.fst)))
end)
end
| uu____6562 -> begin
(fail ())
end))
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____6571 = (lookup_qname env l)
in (match (uu____6571) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____6582, uu____6583, uu____6584); FStar_Syntax_Syntax.sigrng = uu____6585; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____6587}, uu____6588), uu____6589) -> begin
(FStar_Util.for_some (fun uu___108_6616 -> (match (uu___108_6616) with
| FStar_Syntax_Syntax.Projector (uu____6617) -> begin
true
end
| uu____6620 -> begin
false
end)) quals)
end
| uu____6621 -> begin
false
end)))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____6640 = (lookup_qname env lid)
in (match (uu____6640) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____6651, uu____6652, uu____6653, uu____6654, uu____6655, uu____6656); FStar_Syntax_Syntax.sigrng = uu____6657; FStar_Syntax_Syntax.sigquals = uu____6658; FStar_Syntax_Syntax.sigmeta = uu____6659}, uu____6660), uu____6661) -> begin
true
end
| uu____6688 -> begin
false
end)))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____6707 = (lookup_qname env lid)
in (match (uu____6707) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____6718, uu____6719, uu____6720, uu____6721, uu____6722, uu____6723); FStar_Syntax_Syntax.sigrng = uu____6724; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____6726}, uu____6727), uu____6728) -> begin
(FStar_Util.for_some (fun uu___109_6759 -> (match (uu___109_6759) with
| FStar_Syntax_Syntax.RecordType (uu____6760) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____6765) -> begin
true
end
| uu____6770 -> begin
false
end)) quals)
end
| uu____6771 -> begin
false
end)))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____6790 = (lookup_qname env lid)
in (match (uu____6790) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____6801, uu____6802, uu____6803); FStar_Syntax_Syntax.sigrng = uu____6804; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____6806}, uu____6807), uu____6808) -> begin
(FStar_Util.for_some (fun uu___110_6839 -> (match (uu___110_6839) with
| FStar_Syntax_Syntax.Action (uu____6840) -> begin
true
end
| uu____6841 -> begin
false
end)) quals)
end
| uu____6842 -> begin
false
end)))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (fun env head1 -> (

let uu____6863 = (

let uu____6864 = (FStar_Syntax_Util.un_uinst head1)
in uu____6864.FStar_Syntax_Syntax.n)
in (match (uu____6863) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____6868 -> begin
false
end))))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun x -> (match ((FStar_Pervasives_Native.fst x)) with
| FStar_Util.Inl (uu____6908) -> begin
FStar_Pervasives_Native.Some (false)
end
| FStar_Util.Inr (se, uu____6917) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____6926) -> begin
FStar_Pervasives_Native.Some ((FStar_List.contains FStar_Syntax_Syntax.New se.FStar_Syntax_Syntax.sigquals))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____6930) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____6939 -> begin
FStar_Pervasives_Native.Some (false)
end)
end))
in (

let uu____6940 = (

let uu____6942 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____6942 mapper))
in (match (uu____6940) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
false
end))))


let num_inductive_ty_params : env  ->  FStar_Ident.lident  ->  Prims.int = (fun env lid -> (

let uu____6971 = (lookup_qname env lid)
in (match (uu____6971) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____6982, uu____6983, tps, uu____6985, uu____6986, uu____6987); FStar_Syntax_Syntax.sigrng = uu____6988; FStar_Syntax_Syntax.sigquals = uu____6989; FStar_Syntax_Syntax.sigmeta = uu____6990}, uu____6991), uu____6992) -> begin
(FStar_List.length tps)
end
| uu____7025 -> begin
(

let uu____7036 = (

let uu____7037 = (

let uu____7040 = (name_not_found lid)
in ((uu____7040), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____7037))
in (FStar_Pervasives.raise uu____7036))
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun uu____7067 -> (match (uu____7067) with
| (d, uu____7072) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)
end)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (

let uu____7083 = (effect_decl_opt env l)
in (match (uu____7083) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7091 = (

let uu____7092 = (

let uu____7095 = (name_not_found l)
in ((uu____7095), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____7092))
in (FStar_Pervasives.raise uu____7091))
end
| FStar_Pervasives_Native.Some (md) -> begin
(FStar_Pervasives_Native.fst md)
end)))


let identity_mlift : mlift = {mlift_wp = (fun t wp -> wp); mlift_term = FStar_Pervasives_Native.Some ((fun t wp e -> e))}


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> (match ((FStar_Ident.lid_equals l1 l2)) with
| true -> begin
((l1), (identity_mlift), (identity_mlift))
end
| uu____7140 -> begin
(match ((((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid)))) with
| true -> begin
((FStar_Parser_Const.effect_GTot_lid), (identity_mlift), (identity_mlift))
end
| uu____7144 -> begin
(

let uu____7145 = (FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun uu____7175 -> (match (uu____7175) with
| (m1, m2, uu____7183, uu____7184, uu____7185) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))
in (match (uu____7145) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7194 = (

let uu____7195 = (

let uu____7198 = (

let uu____7199 = (FStar_Syntax_Print.lid_to_string l1)
in (

let uu____7200 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" uu____7199 uu____7200)))
in ((uu____7198), (env.range)))
in FStar_Errors.Error (uu____7195))
in (FStar_Pervasives.raise uu____7194))
end
| FStar_Pervasives_Native.Some (uu____7204, uu____7205, m3, j1, j2) -> begin
((m3), (j1), (j2))
end))
end)
end))


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge FStar_Pervasives_Native.option = (fun env l1 l2 -> (match (((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)))) with
| true -> begin
FStar_Pervasives_Native.Some ({msource = l1; mtarget = l2; mlift = identity_mlift})
end
| uu____7228 -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end))


let wp_sig_aux = (fun decls m -> (

let uu____7258 = (FStar_All.pipe_right decls (FStar_Util.find_opt (fun uu____7273 -> (match (uu____7273) with
| (d, uu____7277) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)
end))))
in (match (uu____7258) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7284 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith uu____7284))
end
| FStar_Pervasives_Native.Some (md, _q) -> begin
(

let uu____7293 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (uu____7293) with
| (uu____7300, s) -> begin
(

let s1 = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s1.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, uu____7308))::((wp, uu____7310))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____7332 -> begin
(failwith "Impossible")
end))
end))
end)))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let null_wp_for_eff : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env eff_name res_u res_t -> (match ((FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' res_t (FStar_Pervasives_Native.Some (res_u)))
end
| uu____7366 -> begin
(match ((FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal' res_t (FStar_Pervasives_Native.Some (res_u)))
end
| uu____7367 -> begin
(

let eff_name1 = (norm_eff_name env eff_name)
in (

let ed = (get_effect_decl env eff_name1)
in (

let null_wp = (inst_effect_fun_with ((res_u)::[]) env ed ed.FStar_Syntax_Syntax.null_wp)
in (

let null_wp_res = (

let uu____7374 = (get_range env)
in (

let uu____7375 = (

let uu____7378 = (

let uu____7379 = (

let uu____7389 = (

let uu____7391 = (FStar_Syntax_Syntax.as_arg res_t)
in (uu____7391)::[])
in ((null_wp), (uu____7389)))
in FStar_Syntax_Syntax.Tm_app (uu____7379))
in (FStar_Syntax_Syntax.mk uu____7378))
in (uu____7375 FStar_Pervasives_Native.None uu____7374)))
in (

let uu____7401 = (

let uu____7402 = (

let uu____7408 = (FStar_Syntax_Syntax.as_arg null_wp_res)
in (uu____7408)::[])
in {FStar_Syntax_Syntax.comp_univs = (res_u)::[]; FStar_Syntax_Syntax.effect_name = eff_name1; FStar_Syntax_Syntax.result_typ = res_t; FStar_Syntax_Syntax.effect_args = uu____7402; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp uu____7401))))))
end)
end))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let effects = (

let uu___121_7419 = env.effects
in {decls = (((ne), (se.FStar_Syntax_Syntax.sigquals)))::env.effects.decls; order = uu___121_7419.order; joins = uu___121_7419.joins})
in (

let uu___122_7424 = env
in {solver = uu___122_7424.solver; range = uu___122_7424.range; curmodule = uu___122_7424.curmodule; gamma = uu___122_7424.gamma; gamma_cache = uu___122_7424.gamma_cache; modules = uu___122_7424.modules; expected_typ = uu___122_7424.expected_typ; sigtab = uu___122_7424.sigtab; is_pattern = uu___122_7424.is_pattern; instantiate_imp = uu___122_7424.instantiate_imp; effects = effects; generalize = uu___122_7424.generalize; letrecs = uu___122_7424.letrecs; top_level = uu___122_7424.top_level; check_uvars = uu___122_7424.check_uvars; use_eq = uu___122_7424.use_eq; is_iface = uu___122_7424.is_iface; admit = uu___122_7424.admit; lax = uu___122_7424.lax; lax_universes = uu___122_7424.lax_universes; type_of = uu___122_7424.type_of; universe_of = uu___122_7424.universe_of; use_bv_sorts = uu___122_7424.use_bv_sorts; qname_and_index = uu___122_7424.qname_and_index; proof_ns = uu___122_7424.proof_ns; synth = uu___122_7424.synth; is_native_tactic = uu___122_7424.is_native_tactic}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let compose_edges = (fun e1 e2 -> (

let composed_lift = (

let mlift_wp = (fun r wp1 -> (

let uu____7441 = (e1.mlift.mlift_wp r wp1)
in (e2.mlift.mlift_wp r uu____7441)))
in (

let mlift_term = (match (((e1.mlift.mlift_term), (e2.mlift.mlift_term))) with
| (FStar_Pervasives_Native.Some (l1), FStar_Pervasives_Native.Some (l2)) -> begin
FStar_Pervasives_Native.Some ((fun t wp e -> (

let uu____7525 = (e1.mlift.mlift_wp t wp)
in (

let uu____7526 = (l1 t wp e)
in (l2 t uu____7525 uu____7526)))))
end
| uu____7527 -> begin
FStar_Pervasives_Native.None
end)
in {mlift_wp = mlift_wp; mlift_term = mlift_term}))
in {msource = e1.msource; mtarget = e2.mtarget; mlift = composed_lift}))
in (

let mk_mlift_wp = (fun lift_t r wp1 -> (

let uu____7562 = (inst_tscheme lift_t)
in (match (uu____7562) with
| (uu____7567, lift_t1) -> begin
(

let uu____7569 = (

let uu____7572 = (

let uu____7573 = (

let uu____7583 = (

let uu____7585 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____7586 = (

let uu____7588 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____7588)::[])
in (uu____7585)::uu____7586))
in ((lift_t1), (uu____7583)))
in FStar_Syntax_Syntax.Tm_app (uu____7573))
in (FStar_Syntax_Syntax.mk uu____7572))
in (uu____7569 FStar_Pervasives_Native.None wp1.FStar_Syntax_Syntax.pos))
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

let uu____7633 = (inst_tscheme lift_t)
in (match (uu____7633) with
| (uu____7638, lift_t1) -> begin
(

let uu____7640 = (

let uu____7643 = (

let uu____7644 = (

let uu____7654 = (

let uu____7656 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____7657 = (

let uu____7659 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____7660 = (

let uu____7662 = (FStar_Syntax_Syntax.as_arg e)
in (uu____7662)::[])
in (uu____7659)::uu____7660))
in (uu____7656)::uu____7657))
in ((lift_t1), (uu____7654)))
in FStar_Syntax_Syntax.Tm_app (uu____7644))
in (FStar_Syntax_Syntax.mk uu____7643))
in (uu____7640 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
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

let uu____7703 = (

let uu____7704 = (FStar_Ident.lid_of_path ((s)::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____7704 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.fv_to_tm uu____7703)))
in (

let arg = (bogus_term "ARG")
in (

let wp = (bogus_term "WP")
in (

let e = (bogus_term "COMP")
in (

let uu____7708 = (

let uu____7709 = (l.mlift_wp arg wp)
in (FStar_Syntax_Print.term_to_string uu____7709))
in (

let uu____7710 = (

let uu____7711 = (FStar_Util.map_opt l.mlift_term (fun l1 -> (

let uu____7728 = (l1 arg wp e)
in (FStar_Syntax_Print.term_to_string uu____7728))))
in (FStar_Util.dflt "none" uu____7711))
in (FStar_Util.format2 "{ wp : %s ; term : %s }" uu____7708 uu____7710))))))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun uu____7744 -> (match (uu____7744) with
| (e, uu____7749) -> begin
e.FStar_Syntax_Syntax.mname
end))))
in (

let find_edge = (fun order1 uu____7762 -> (match (uu____7762) with
| (i, j) -> begin
(match ((FStar_Ident.lid_equals i j)) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _0_39 -> FStar_Pervasives_Native.Some (_0_39)))
end
| uu____7771 -> begin
(FStar_All.pipe_right order1 (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end)
end))
in (

let order1 = (

let fold_fun = (fun order1 k -> (

let uu____7788 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (match ((FStar_Ident.lid_equals i k)) with
| true -> begin
[]
end
| uu____7795 -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (match ((FStar_Ident.lid_equals j k)) with
| true -> begin
[]
end
| uu____7801 -> begin
(

let uu____7802 = (

let uu____7807 = (find_edge order1 ((i), (k)))
in (

let uu____7809 = (find_edge order1 ((k), (j)))
in ((uu____7807), (uu____7809))))
in (match (uu____7802) with
| (FStar_Pervasives_Native.Some (e1), FStar_Pervasives_Native.Some (e2)) -> begin
(

let uu____7818 = (compose_edges e1 e2)
in (uu____7818)::[])
end
| uu____7819 -> begin
[]
end))
end))))
end))))
in (FStar_List.append order1 uu____7788)))
in (FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)))
in (

let order2 = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order1)
in ((FStar_All.pipe_right order2 (FStar_List.iter (fun edge1 -> (

let uu____7839 = ((FStar_Ident.lid_equals edge1.msource FStar_Parser_Const.effect_DIV_lid) && (

let uu____7841 = (lookup_effect_quals env edge1.mtarget)
in (FStar_All.pipe_right uu____7841 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))))
in (match (uu____7839) with
| true -> begin
(

let uu____7844 = (

let uu____7845 = (

let uu____7848 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge1.mtarget.FStar_Ident.str)
in (

let uu____7849 = (get_range env)
in ((uu____7848), (uu____7849))))
in FStar_Errors.Error (uu____7845))
in (FStar_Pervasives.raise uu____7844))
end
| uu____7850 -> begin
()
end)))));
(

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (match ((FStar_Ident.lid_equals i j)) with
| true -> begin
FStar_Pervasives_Native.Some (((i), ((id_edge i)), ((id_edge i))))
end
| uu____7899 -> begin
(FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (

let uu____7920 = (

let uu____7925 = (find_edge order2 ((i), (k)))
in (

let uu____7927 = (find_edge order2 ((j), (k)))
in ((uu____7925), (uu____7927))))
in (match (uu____7920) with
| (FStar_Pervasives_Native.Some (ik), FStar_Pervasives_Native.Some (jk)) -> begin
(match (bopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((k), (ik), (jk)))
end
| FStar_Pervasives_Native.Some (ub, uu____7950, uu____7951) -> begin
(

let uu____7955 = (

let uu____7958 = (

let uu____7959 = (find_edge order2 ((k), (ub)))
in (FStar_Util.is_some uu____7959))
in (

let uu____7961 = (

let uu____7962 = (find_edge order2 ((ub), (k)))
in (FStar_Util.is_some uu____7962))
in ((uu____7958), (uu____7961))))
in (match (uu____7955) with
| (true, true) -> begin
(match ((FStar_Ident.lid_equals k ub)) with
| true -> begin
((FStar_Util.print_warning "Looking multiple times at the same upper bound candidate");
bopt;
)
end
| uu____7973 -> begin
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
| uu____7981 -> begin
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

let uu___123_8020 = env.effects
in {decls = uu___123_8020.decls; order = order2; joins = joins})
in (

let uu___124_8021 = env
in {solver = uu___124_8021.solver; range = uu___124_8021.range; curmodule = uu___124_8021.curmodule; gamma = uu___124_8021.gamma; gamma_cache = uu___124_8021.gamma_cache; modules = uu___124_8021.modules; expected_typ = uu___124_8021.expected_typ; sigtab = uu___124_8021.sigtab; is_pattern = uu___124_8021.is_pattern; instantiate_imp = uu___124_8021.instantiate_imp; effects = effects; generalize = uu___124_8021.generalize; letrecs = uu___124_8021.letrecs; top_level = uu___124_8021.top_level; check_uvars = uu___124_8021.check_uvars; use_eq = uu___124_8021.use_eq; is_iface = uu___124_8021.is_iface; admit = uu___124_8021.admit; lax = uu___124_8021.lax; lax_universes = uu___124_8021.lax_universes; type_of = uu___124_8021.type_of; universe_of = uu___124_8021.universe_of; use_bv_sorts = uu___124_8021.use_bv_sorts; qname_and_index = uu___124_8021.qname_and_index; proof_ns = uu___124_8021.proof_ns; synth = uu___124_8021.synth; is_native_tactic = uu___124_8021.is_native_tactic})));
))))))))))))))
end
| uu____8022 -> begin
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
| uu____8046 -> begin
c
end)
in (FStar_Syntax_Util.comp_to_comp_typ c1)))


let rec unfold_effect_abbrev : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (comp_to_comp_typ env comp)
in (

let uu____8056 = (lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name)
in (match (uu____8056) with
| FStar_Pervasives_Native.None -> begin
c
end
| FStar_Pervasives_Native.Some (binders, cdef) -> begin
(

let uu____8066 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (uu____8066) with
| (binders1, cdef1) -> begin
((match (((FStar_List.length binders1) <> ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))) with
| true -> begin
(

let uu____8088 = (

let uu____8089 = (

let uu____8092 = (

let uu____8093 = (FStar_Util.string_of_int (FStar_List.length binders1))
in (

let uu____8102 = (FStar_Util.string_of_int ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))
in (

let uu____8113 = (

let uu____8114 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Print.comp_to_string uu____8114))
in (FStar_Util.format3 "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s" uu____8093 uu____8102 uu____8113))))
in ((uu____8092), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____8089))
in (FStar_Pervasives.raise uu____8088))
end
| uu____8115 -> begin
()
end);
(

let inst1 = (

let uu____8118 = (

let uu____8124 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (uu____8124)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun uu____8137 uu____8138 -> (match (((uu____8137), (uu____8138))) with
| ((x, uu____8152), (t, uu____8154)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders1 uu____8118))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst1 cdef1)
in (

let c2 = (

let uu____8169 = (

let uu___125_8170 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = uu___125_8170.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___125_8170.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___125_8170.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___125_8170.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right uu____8169 FStar_Syntax_Syntax.mk_Comp))
in (unfold_effect_abbrev env c2))));
)
end))
end))))


let effect_repr_aux = (fun only_reifiable env c u_c -> (

let uu____8205 = (

let uu____8210 = (norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (effect_decl_opt env uu____8210))
in (match (uu____8205) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____8226 = (only_reifiable && (

let uu____8228 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____8228))))
in (match (uu____8226) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____8235 -> begin
(match (ed.FStar_Syntax_Syntax.repr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| uu____8241 -> begin
(

let c1 = (unfold_effect_abbrev env c)
in (

let uu____8243 = (

let uu____8252 = (FStar_List.hd c1.FStar_Syntax_Syntax.effect_args)
in ((c1.FStar_Syntax_Syntax.result_typ), (uu____8252)))
in (match (uu____8243) with
| (res_typ, wp) -> begin
(

let repr = (inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____8286 = (

let uu____8289 = (get_range env)
in (

let uu____8290 = (

let uu____8293 = (

let uu____8294 = (

let uu____8304 = (

let uu____8306 = (FStar_Syntax_Syntax.as_arg res_typ)
in (uu____8306)::(wp)::[])
in ((repr), (uu____8304)))
in FStar_Syntax_Syntax.Tm_app (uu____8294))
in (FStar_Syntax_Syntax.mk uu____8293))
in (uu____8290 FStar_Pervasives_Native.None uu____8289)))
in FStar_Pervasives_Native.Some (uu____8286)))
end)))
end)
end))
end)))


let effect_repr : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (

let uu____8356 = (

let uu____8357 = (

let uu____8360 = (

let uu____8361 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format1 "Effect %s cannot be reified" uu____8361))
in (

let uu____8362 = (get_range env)
in ((uu____8360), (uu____8362))))
in FStar_Errors.Error (uu____8357))
in (FStar_Pervasives.raise uu____8356)))
in (

let uu____8363 = (effect_repr_aux true env c u_c)
in (match (uu____8363) with
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
| uu____8401 -> begin
false
end))


let is_reifiable_function : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____8410 = (

let uu____8411 = (FStar_Syntax_Subst.compress t)
in uu____8411.FStar_Syntax_Syntax.n)
in (match (uu____8410) with
| FStar_Syntax_Syntax.Tm_arrow (uu____8414, c) -> begin
(is_reifiable_comp env c)
end
| uu____8426 -> begin
false
end)))


let push_in_gamma : env  ->  binding  ->  env = (fun env s -> (

let rec push1 = (fun x rest -> (match (rest) with
| (Binding_sig (uu____8446))::uu____8447 -> begin
(x)::rest
end
| (Binding_sig_inst (uu____8452))::uu____8453 -> begin
(x)::rest
end
| [] -> begin
(x)::[]
end
| (local)::rest1 -> begin
(

let uu____8462 = (push1 x rest1)
in (local)::uu____8462)
end))
in (

let uu___126_8464 = env
in (

let uu____8465 = (push1 s env.gamma)
in {solver = uu___126_8464.solver; range = uu___126_8464.range; curmodule = uu___126_8464.curmodule; gamma = uu____8465; gamma_cache = uu___126_8464.gamma_cache; modules = uu___126_8464.modules; expected_typ = uu___126_8464.expected_typ; sigtab = uu___126_8464.sigtab; is_pattern = uu___126_8464.is_pattern; instantiate_imp = uu___126_8464.instantiate_imp; effects = uu___126_8464.effects; generalize = uu___126_8464.generalize; letrecs = uu___126_8464.letrecs; top_level = uu___126_8464.top_level; check_uvars = uu___126_8464.check_uvars; use_eq = uu___126_8464.use_eq; is_iface = uu___126_8464.is_iface; admit = uu___126_8464.admit; lax = uu___126_8464.lax; lax_universes = uu___126_8464.lax_universes; type_of = uu___126_8464.type_of; universe_of = uu___126_8464.universe_of; use_bv_sorts = uu___126_8464.use_bv_sorts; qname_and_index = uu___126_8464.qname_and_index; proof_ns = uu___126_8464.proof_ns; synth = uu___126_8464.synth; is_native_tactic = uu___126_8464.is_native_tactic}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env1 = (push_in_gamma env (Binding_sig ((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))))
in (build_lattice env1 s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env1 = (push_in_gamma env (Binding_sig_inst ((((FStar_Syntax_Util.lids_of_sigelt s)), (s), (us)))))
in (build_lattice env1 s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let uu___127_8499 = env
in {solver = uu___127_8499.solver; range = uu___127_8499.range; curmodule = uu___127_8499.curmodule; gamma = (b)::env.gamma; gamma_cache = uu___127_8499.gamma_cache; modules = uu___127_8499.modules; expected_typ = uu___127_8499.expected_typ; sigtab = uu___127_8499.sigtab; is_pattern = uu___127_8499.is_pattern; instantiate_imp = uu___127_8499.instantiate_imp; effects = uu___127_8499.effects; generalize = uu___127_8499.generalize; letrecs = uu___127_8499.letrecs; top_level = uu___127_8499.top_level; check_uvars = uu___127_8499.check_uvars; use_eq = uu___127_8499.use_eq; is_iface = uu___127_8499.is_iface; admit = uu___127_8499.admit; lax = uu___127_8499.lax; lax_universes = uu___127_8499.lax_universes; type_of = uu___127_8499.type_of; universe_of = uu___127_8499.universe_of; use_bv_sorts = uu___127_8499.use_bv_sorts; qname_and_index = uu___127_8499.qname_and_index; proof_ns = uu___127_8499.proof_ns; synth = uu___127_8499.synth; is_native_tactic = uu___127_8499.is_native_tactic}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let pop_bv : env  ->  (FStar_Syntax_Syntax.bv * env) FStar_Pervasives_Native.option = (fun env -> (match (env.gamma) with
| (Binding_var (x))::rest -> begin
FStar_Pervasives_Native.Some (((x), ((

let uu___128_8524 = env
in {solver = uu___128_8524.solver; range = uu___128_8524.range; curmodule = uu___128_8524.curmodule; gamma = rest; gamma_cache = uu___128_8524.gamma_cache; modules = uu___128_8524.modules; expected_typ = uu___128_8524.expected_typ; sigtab = uu___128_8524.sigtab; is_pattern = uu___128_8524.is_pattern; instantiate_imp = uu___128_8524.instantiate_imp; effects = uu___128_8524.effects; generalize = uu___128_8524.generalize; letrecs = uu___128_8524.letrecs; top_level = uu___128_8524.top_level; check_uvars = uu___128_8524.check_uvars; use_eq = uu___128_8524.use_eq; is_iface = uu___128_8524.is_iface; admit = uu___128_8524.admit; lax = uu___128_8524.lax; lax_universes = uu___128_8524.lax_universes; type_of = uu___128_8524.type_of; universe_of = uu___128_8524.universe_of; use_bv_sorts = uu___128_8524.use_bv_sorts; qname_and_index = uu___128_8524.qname_and_index; proof_ns = uu___128_8524.proof_ns; synth = uu___128_8524.synth; is_native_tactic = uu___128_8524.is_native_tactic}))))
end
| uu____8525 -> begin
FStar_Pervasives_Native.None
end))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env1 uu____8544 -> (match (uu____8544) with
| (x, uu____8548) -> begin
(push_bv env1 x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Syntax_Syntax.univ_name Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x1) -> begin
(

let x2 = (

let uu___129_8571 = x1
in {FStar_Syntax_Syntax.ppname = uu___129_8571.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___129_8571.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)})
in Binding_var (x2))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> ((add_sigelts env m.FStar_Syntax_Syntax.exports);
(

let uu___130_8602 = env
in {solver = uu___130_8602.solver; range = uu___130_8602.range; curmodule = uu___130_8602.curmodule; gamma = []; gamma_cache = uu___130_8602.gamma_cache; modules = (m)::env.modules; expected_typ = FStar_Pervasives_Native.None; sigtab = uu___130_8602.sigtab; is_pattern = uu___130_8602.is_pattern; instantiate_imp = uu___130_8602.instantiate_imp; effects = uu___130_8602.effects; generalize = uu___130_8602.generalize; letrecs = uu___130_8602.letrecs; top_level = uu___130_8602.top_level; check_uvars = uu___130_8602.check_uvars; use_eq = uu___130_8602.use_eq; is_iface = uu___130_8602.is_iface; admit = uu___130_8602.admit; lax = uu___130_8602.lax; lax_universes = uu___130_8602.lax_universes; type_of = uu___130_8602.type_of; universe_of = uu___130_8602.universe_of; use_bv_sorts = uu___130_8602.use_bv_sorts; qname_and_index = uu___130_8602.qname_and_index; proof_ns = uu___130_8602.proof_ns; synth = uu___130_8602.synth; is_native_tactic = uu___130_8602.is_native_tactic});
))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env1 x -> (push_local_binding env1 (Binding_univ (x)))) env xs))


let open_universes_in : env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term Prims.list  ->  (env * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term Prims.list) = (fun env uvs terms -> (

let uu____8633 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____8633) with
| (univ_subst, univ_vars) -> begin
(

let env' = (push_univ_vars env univ_vars)
in (

let uu____8649 = (FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms)
in ((env'), (univ_vars), (uu____8649))))
end)))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let uu___131_8661 = env
in {solver = uu___131_8661.solver; range = uu___131_8661.range; curmodule = uu___131_8661.curmodule; gamma = uu___131_8661.gamma; gamma_cache = uu___131_8661.gamma_cache; modules = uu___131_8661.modules; expected_typ = FStar_Pervasives_Native.Some (t); sigtab = uu___131_8661.sigtab; is_pattern = uu___131_8661.is_pattern; instantiate_imp = uu___131_8661.instantiate_imp; effects = uu___131_8661.effects; generalize = uu___131_8661.generalize; letrecs = uu___131_8661.letrecs; top_level = uu___131_8661.top_level; check_uvars = uu___131_8661.check_uvars; use_eq = false; is_iface = uu___131_8661.is_iface; admit = uu___131_8661.admit; lax = uu___131_8661.lax; lax_universes = uu___131_8661.lax_universes; type_of = uu___131_8661.type_of; universe_of = uu___131_8661.universe_of; use_bv_sorts = uu___131_8661.use_bv_sorts; qname_and_index = uu___131_8661.qname_and_index; proof_ns = uu___131_8661.proof_ns; synth = uu___131_8661.synth; is_native_tactic = uu___131_8661.is_native_tactic}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun env -> (match (env.expected_typ) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) = (fun env_ -> (

let uu____8679 = (expected_typ env_)
in (((

let uu___132_8683 = env_
in {solver = uu___132_8683.solver; range = uu___132_8683.range; curmodule = uu___132_8683.curmodule; gamma = uu___132_8683.gamma; gamma_cache = uu___132_8683.gamma_cache; modules = uu___132_8683.modules; expected_typ = FStar_Pervasives_Native.None; sigtab = uu___132_8683.sigtab; is_pattern = uu___132_8683.is_pattern; instantiate_imp = uu___132_8683.instantiate_imp; effects = uu___132_8683.effects; generalize = uu___132_8683.generalize; letrecs = uu___132_8683.letrecs; top_level = uu___132_8683.top_level; check_uvars = uu___132_8683.check_uvars; use_eq = false; is_iface = uu___132_8683.is_iface; admit = uu___132_8683.admit; lax = uu___132_8683.lax; lax_universes = uu___132_8683.lax_universes; type_of = uu___132_8683.type_of; universe_of = uu___132_8683.universe_of; use_bv_sorts = uu___132_8683.use_bv_sorts; qname_and_index = uu___132_8683.qname_and_index; proof_ns = uu___132_8683.proof_ns; synth = uu___132_8683.synth; is_native_tactic = uu___132_8683.is_native_tactic})), (uu____8679))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = (match ((FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Parser_Const.prims_lid)) with
| true -> begin
(

let uu____8696 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun uu___111_8703 -> (match (uu___111_8703) with
| Binding_sig (uu____8705, se) -> begin
(se)::[]
end
| uu____8709 -> begin
[]
end))))
in (FStar_All.pipe_right uu____8696 FStar_List.rev))
end
| uu____8712 -> begin
m.FStar_Syntax_Syntax.exports
end)
in ((add_sigelts env sigs);
(

let uu___133_8714 = env
in {solver = uu___133_8714.solver; range = uu___133_8714.range; curmodule = empty_lid; gamma = []; gamma_cache = uu___133_8714.gamma_cache; modules = (m)::env.modules; expected_typ = uu___133_8714.expected_typ; sigtab = uu___133_8714.sigtab; is_pattern = uu___133_8714.is_pattern; instantiate_imp = uu___133_8714.instantiate_imp; effects = uu___133_8714.effects; generalize = uu___133_8714.generalize; letrecs = uu___133_8714.letrecs; top_level = uu___133_8714.top_level; check_uvars = uu___133_8714.check_uvars; use_eq = uu___133_8714.use_eq; is_iface = uu___133_8714.is_iface; admit = uu___133_8714.admit; lax = uu___133_8714.lax; lax_universes = uu___133_8714.lax_universes; type_of = uu___133_8714.type_of; universe_of = uu___133_8714.universe_of; use_bv_sorts = uu___133_8714.use_bv_sorts; qname_and_index = uu___133_8714.qname_and_index; proof_ns = uu___133_8714.proof_ns; synth = uu___133_8714.synth; is_native_tactic = uu___133_8714.is_native_tactic});
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
| (Binding_univ (uu____8765))::tl1 -> begin
(aux out tl1)
end
| (Binding_lid (uu____8768, (uu____8769, t)))::tl1 -> begin
(

let uu____8778 = (

let uu____8782 = (FStar_Syntax_Free.uvars t)
in (ext out uu____8782))
in (aux uu____8778 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____8786; FStar_Syntax_Syntax.index = uu____8787; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____8793 = (

let uu____8797 = (FStar_Syntax_Free.uvars t)
in (ext out uu____8797))
in (aux uu____8793 tl1))
end
| (Binding_sig (uu____8801))::uu____8802 -> begin
out
end
| (Binding_sig_inst (uu____8807))::uu____8808 -> begin
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
| (Binding_sig_inst (uu____8846))::tl1 -> begin
(aux out tl1)
end
| (Binding_univ (uu____8853))::tl1 -> begin
(aux out tl1)
end
| (Binding_lid (uu____8856, (uu____8857, t)))::tl1 -> begin
(

let uu____8866 = (

let uu____8868 = (FStar_Syntax_Free.univs t)
in (ext out uu____8868))
in (aux uu____8866 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____8870; FStar_Syntax_Syntax.index = uu____8871; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____8877 = (

let uu____8879 = (FStar_Syntax_Free.univs t)
in (ext out uu____8879))
in (aux uu____8877 tl1))
end
| (Binding_sig (uu____8881))::uu____8882 -> begin
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
| (Binding_sig_inst (uu____8920))::tl1 -> begin
(aux out tl1)
end
| (Binding_univ (uname))::tl1 -> begin
(

let uu____8930 = (FStar_Util.set_add uname out)
in (aux uu____8930 tl1))
end
| (Binding_lid (uu____8932, (uu____8933, t)))::tl1 -> begin
(

let uu____8942 = (

let uu____8944 = (FStar_Syntax_Free.univnames t)
in (ext out uu____8944))
in (aux uu____8942 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____8946; FStar_Syntax_Syntax.index = uu____8947; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____8953 = (

let uu____8955 = (FStar_Syntax_Free.univnames t)
in (ext out uu____8955))
in (aux uu____8953 tl1))
end
| (Binding_sig (uu____8957))::uu____8958 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu___112_8977 -> (match (uu___112_8977) with
| Binding_var (x) -> begin
(x)::[]
end
| Binding_lid (uu____8980) -> begin
[]
end
| Binding_sig (uu____8983) -> begin
[]
end
| Binding_univ (uu____8987) -> begin
[]
end
| Binding_sig_inst (uu____8988) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____8999 = (

let uu____9001 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right uu____9001 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right uu____8999 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let print_gamma : env  ->  Prims.unit = (fun env -> (

let uu____9020 = (

let uu____9021 = (FStar_All.pipe_right env.gamma (FStar_List.map (fun uu___113_9028 -> (match (uu___113_9028) with
| Binding_var (x) -> begin
(

let uu____9030 = (FStar_Syntax_Print.bv_to_string x)
in (Prims.strcat "Binding_var " uu____9030))
end
| Binding_univ (u) -> begin
(Prims.strcat "Binding_univ " u.FStar_Ident.idText)
end
| Binding_lid (l, uu____9033) -> begin
(

let uu____9034 = (FStar_Ident.string_of_lid l)
in (Prims.strcat "Binding_lid " uu____9034))
end
| Binding_sig (ls, uu____9036) -> begin
(

let uu____9039 = (

let uu____9040 = (FStar_All.pipe_right ls (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____9040 (FStar_String.concat ", ")))
in (Prims.strcat "Binding_sig " uu____9039))
end
| Binding_sig_inst (ls, uu____9046, uu____9047) -> begin
(

let uu____9050 = (

let uu____9051 = (FStar_All.pipe_right ls (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____9051 (FStar_String.concat ", ")))
in (Prims.strcat "Binding_sig_inst " uu____9050))
end))))
in (FStar_All.pipe_right uu____9021 (FStar_String.concat "::\n")))
in (FStar_All.pipe_right uu____9020 (FStar_Util.print1 "%s\n"))))


let eq_gamma : env  ->  env  ->  Prims.bool = (fun env env' -> (

let uu____9065 = (FStar_Util.physical_equality env.gamma env'.gamma)
in (match (uu____9065) with
| true -> begin
true
end
| uu____9067 -> begin
(

let g = (all_binders env)
in (

let g' = (all_binders env')
in (((FStar_List.length g) = (FStar_List.length g')) && (FStar_List.forall2 (fun uu____9092 uu____9093 -> (match (((uu____9092), (uu____9093))) with
| ((b1, uu____9103), (b2, uu____9105)) -> begin
(FStar_Syntax_Syntax.bv_eq b1 b2)
end)) g g'))))
end)))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a1 -> (f a1 e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys uu___114_9159 -> (match (uu___114_9159) with
| Binding_sig (lids, uu____9163) -> begin
(FStar_List.append lids keys)
end
| uu____9166 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun uu____9171 v1 keys1 -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)) keys)))


let should_enc_path : env  ->  Prims.string Prims.list  ->  Prims.bool = (fun env path -> (

let rec list_prefix = (fun xs ys -> (match (((xs), (ys))) with
| ([], uu____9198) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((x = y) && (list_prefix xs1 ys1))
end
| (uu____9210, uu____9211) -> begin
false
end))
in (

let rec should_enc_path' = (fun pns path1 -> (match (pns) with
| [] -> begin
true
end
| ((p, b))::pns1 -> begin
(

let uu____9235 = (list_prefix p path1)
in (match (uu____9235) with
| true -> begin
b
end
| uu____9236 -> begin
(should_enc_path' pns1 path1)
end))
end))
in (should_enc_path' (FStar_List.flatten env.proof_ns) path))))


let should_enc_lid : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____9247 = (FStar_Ident.path_of_lid lid)
in (should_enc_path env uu____9247)))


let cons_proof_ns : Prims.bool  ->  env  ->  name_prefix  ->  env = (fun b e path -> (match (e.proof_ns) with
| [] -> begin
(failwith "empty proof_ns stack!")
end
| (pns)::rest -> begin
(

let pns' = (((path), (b)))::pns
in (

let uu___134_9270 = e
in {solver = uu___134_9270.solver; range = uu___134_9270.range; curmodule = uu___134_9270.curmodule; gamma = uu___134_9270.gamma; gamma_cache = uu___134_9270.gamma_cache; modules = uu___134_9270.modules; expected_typ = uu___134_9270.expected_typ; sigtab = uu___134_9270.sigtab; is_pattern = uu___134_9270.is_pattern; instantiate_imp = uu___134_9270.instantiate_imp; effects = uu___134_9270.effects; generalize = uu___134_9270.generalize; letrecs = uu___134_9270.letrecs; top_level = uu___134_9270.top_level; check_uvars = uu___134_9270.check_uvars; use_eq = uu___134_9270.use_eq; is_iface = uu___134_9270.is_iface; admit = uu___134_9270.admit; lax = uu___134_9270.lax; lax_universes = uu___134_9270.lax_universes; type_of = uu___134_9270.type_of; universe_of = uu___134_9270.universe_of; use_bv_sorts = uu___134_9270.use_bv_sorts; qname_and_index = uu___134_9270.qname_and_index; proof_ns = (pns')::rest; synth = uu___134_9270.synth; is_native_tactic = uu___134_9270.is_native_tactic}))
end))


let add_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns true e path))


let rem_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns false e path))


let push_proof_ns : env  ->  env = (fun e -> (

let uu___135_9294 = e
in {solver = uu___135_9294.solver; range = uu___135_9294.range; curmodule = uu___135_9294.curmodule; gamma = uu___135_9294.gamma; gamma_cache = uu___135_9294.gamma_cache; modules = uu___135_9294.modules; expected_typ = uu___135_9294.expected_typ; sigtab = uu___135_9294.sigtab; is_pattern = uu___135_9294.is_pattern; instantiate_imp = uu___135_9294.instantiate_imp; effects = uu___135_9294.effects; generalize = uu___135_9294.generalize; letrecs = uu___135_9294.letrecs; top_level = uu___135_9294.top_level; check_uvars = uu___135_9294.check_uvars; use_eq = uu___135_9294.use_eq; is_iface = uu___135_9294.is_iface; admit = uu___135_9294.admit; lax = uu___135_9294.lax; lax_universes = uu___135_9294.lax_universes; type_of = uu___135_9294.type_of; universe_of = uu___135_9294.universe_of; use_bv_sorts = uu___135_9294.use_bv_sorts; qname_and_index = uu___135_9294.qname_and_index; proof_ns = ([])::e.proof_ns; synth = uu___135_9294.synth; is_native_tactic = uu___135_9294.is_native_tactic}))


let pop_proof_ns : env  ->  env = (fun e -> (match (e.proof_ns) with
| [] -> begin
(failwith "empty proof_ns stack!")
end
| (uu____9304)::rest -> begin
(

let uu___136_9307 = e
in {solver = uu___136_9307.solver; range = uu___136_9307.range; curmodule = uu___136_9307.curmodule; gamma = uu___136_9307.gamma; gamma_cache = uu___136_9307.gamma_cache; modules = uu___136_9307.modules; expected_typ = uu___136_9307.expected_typ; sigtab = uu___136_9307.sigtab; is_pattern = uu___136_9307.is_pattern; instantiate_imp = uu___136_9307.instantiate_imp; effects = uu___136_9307.effects; generalize = uu___136_9307.generalize; letrecs = uu___136_9307.letrecs; top_level = uu___136_9307.top_level; check_uvars = uu___136_9307.check_uvars; use_eq = uu___136_9307.use_eq; is_iface = uu___136_9307.is_iface; admit = uu___136_9307.admit; lax = uu___136_9307.lax; lax_universes = uu___136_9307.lax_universes; type_of = uu___136_9307.type_of; universe_of = uu___136_9307.universe_of; use_bv_sorts = uu___136_9307.use_bv_sorts; qname_and_index = uu___136_9307.qname_and_index; proof_ns = rest; synth = uu___136_9307.synth; is_native_tactic = uu___136_9307.is_native_tactic})
end))


let get_proof_ns : env  ->  proof_namespace = (fun e -> e.proof_ns)


let set_proof_ns : proof_namespace  ->  env  ->  env = (fun ns e -> (

let uu___137_9320 = e
in {solver = uu___137_9320.solver; range = uu___137_9320.range; curmodule = uu___137_9320.curmodule; gamma = uu___137_9320.gamma; gamma_cache = uu___137_9320.gamma_cache; modules = uu___137_9320.modules; expected_typ = uu___137_9320.expected_typ; sigtab = uu___137_9320.sigtab; is_pattern = uu___137_9320.is_pattern; instantiate_imp = uu___137_9320.instantiate_imp; effects = uu___137_9320.effects; generalize = uu___137_9320.generalize; letrecs = uu___137_9320.letrecs; top_level = uu___137_9320.top_level; check_uvars = uu___137_9320.check_uvars; use_eq = uu___137_9320.use_eq; is_iface = uu___137_9320.is_iface; admit = uu___137_9320.admit; lax = uu___137_9320.lax; lax_universes = uu___137_9320.lax_universes; type_of = uu___137_9320.type_of; universe_of = uu___137_9320.universe_of; use_bv_sorts = uu___137_9320.use_bv_sorts; qname_and_index = uu___137_9320.qname_and_index; proof_ns = ns; synth = uu___137_9320.synth; is_native_tactic = uu___137_9320.is_native_tactic}))


let string_of_proof_ns : env  ->  Prims.string = (fun env -> (

let string_of_proof_ns' = (fun pns -> (

let uu____9339 = (FStar_List.map (fun fpns -> (

let uu____9352 = (

let uu____9353 = (

let uu____9354 = (FStar_List.map (fun uu____9362 -> (match (uu____9362) with
| (p, b) -> begin
(Prims.strcat (match (b) with
| true -> begin
"+"
end
| uu____9370 -> begin
"-"
end) (FStar_String.concat "." p))
end)) fpns)
in (FStar_String.concat "," uu____9354))
in (Prims.strcat uu____9353 "]"))
in (Prims.strcat "[" uu____9352))) pns)
in (FStar_String.concat ";" uu____9339)))
in (string_of_proof_ns' env.proof_ns)))


let dummy_solver : solver_t = {init = (fun uu____9373 -> ()); push = (fun uu____9375 -> ()); pop = (fun uu____9377 -> ()); mark = (fun uu____9379 -> ()); reset_mark = (fun uu____9381 -> ()); commit_mark = (fun uu____9383 -> ()); encode_modul = (fun uu____9386 uu____9387 -> ()); encode_sig = (fun uu____9390 uu____9391 -> ()); preprocess = (fun e g -> (

let uu____9397 = (

let uu____9401 = (FStar_Options.peek ())
in ((e), (g), (uu____9401)))
in (uu____9397)::[])); solve = (fun uu____9411 uu____9412 uu____9413 -> ()); is_trivial = (fun uu____9419 uu____9420 -> false); finish = (fun uu____9422 -> ()); refresh = (fun uu____9424 -> ())}





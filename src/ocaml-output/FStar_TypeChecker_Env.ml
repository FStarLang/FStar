
open Prims
open FStar_Pervasives
type step =
| Beta
| Iota
| Zeta
| Exclude of step
| Weak
| HNF
| Primops
| Eager_unfolding
| Inlining
| DoNotUnfoldPureLets
| UnfoldUntil of FStar_Syntax_Syntax.delta_depth
| UnfoldOnly of FStar_Ident.lid Prims.list
| UnfoldFully of FStar_Ident.lid Prims.list
| UnfoldAttr of FStar_Ident.lid Prims.list
| UnfoldTac
| PureSubtermsWithinComputations
| Simplify
| EraseUniverses
| AllowUnboundUniverses
| Reify
| CompressUvars
| NoFullNorm
| CheckNoUvars
| Unmeta
| Unascribe
| NBE
| ForExtraction


let uu___is_Beta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Beta -> begin
true
end
| uu____103 -> begin
false
end))


let uu___is_Iota : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iota -> begin
true
end
| uu____114 -> begin
false
end))


let uu___is_Zeta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Zeta -> begin
true
end
| uu____125 -> begin
false
end))


let uu___is_Exclude : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exclude (_0) -> begin
true
end
| uu____137 -> begin
false
end))


let __proj__Exclude__item___0 : step  ->  step = (fun projectee -> (match (projectee) with
| Exclude (_0) -> begin
_0
end))


let uu___is_Weak : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Weak -> begin
true
end
| uu____155 -> begin
false
end))


let uu___is_HNF : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HNF -> begin
true
end
| uu____166 -> begin
false
end))


let uu___is_Primops : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____177 -> begin
false
end))


let uu___is_Eager_unfolding : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding -> begin
true
end
| uu____188 -> begin
false
end))


let uu___is_Inlining : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____199 -> begin
false
end))


let uu___is_DoNotUnfoldPureLets : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DoNotUnfoldPureLets -> begin
true
end
| uu____210 -> begin
false
end))


let uu___is_UnfoldUntil : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
true
end
| uu____222 -> begin
false
end))


let __proj__UnfoldUntil__item___0 : step  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
_0
end))


let uu___is_UnfoldOnly : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
true
end
| uu____243 -> begin
false
end))


let __proj__UnfoldOnly__item___0 : step  ->  FStar_Ident.lid Prims.list = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
_0
end))


let uu___is_UnfoldFully : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldFully (_0) -> begin
true
end
| uu____270 -> begin
false
end))


let __proj__UnfoldFully__item___0 : step  ->  FStar_Ident.lid Prims.list = (fun projectee -> (match (projectee) with
| UnfoldFully (_0) -> begin
_0
end))


let uu___is_UnfoldAttr : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldAttr (_0) -> begin
true
end
| uu____297 -> begin
false
end))


let __proj__UnfoldAttr__item___0 : step  ->  FStar_Ident.lid Prims.list = (fun projectee -> (match (projectee) with
| UnfoldAttr (_0) -> begin
_0
end))


let uu___is_UnfoldTac : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldTac -> begin
true
end
| uu____321 -> begin
false
end))


let uu___is_PureSubtermsWithinComputations : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PureSubtermsWithinComputations -> begin
true
end
| uu____332 -> begin
false
end))


let uu___is_Simplify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simplify -> begin
true
end
| uu____343 -> begin
false
end))


let uu___is_EraseUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EraseUniverses -> begin
true
end
| uu____354 -> begin
false
end))


let uu___is_AllowUnboundUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AllowUnboundUniverses -> begin
true
end
| uu____365 -> begin
false
end))


let uu___is_Reify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____376 -> begin
false
end))


let uu___is_CompressUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CompressUvars -> begin
true
end
| uu____387 -> begin
false
end))


let uu___is_NoFullNorm : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoFullNorm -> begin
true
end
| uu____398 -> begin
false
end))


let uu___is_CheckNoUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckNoUvars -> begin
true
end
| uu____409 -> begin
false
end))


let uu___is_Unmeta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unmeta -> begin
true
end
| uu____420 -> begin
false
end))


let uu___is_Unascribe : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unascribe -> begin
true
end
| uu____431 -> begin
false
end))


let uu___is_NBE : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NBE -> begin
true
end
| uu____442 -> begin
false
end))


let uu___is_ForExtraction : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ForExtraction -> begin
true
end
| uu____453 -> begin
false
end))


type steps =
step Prims.list


let rec eq_step : step  ->  step  ->  Prims.bool = (fun s1 s2 -> (match (((s1), (s2))) with
| (Beta, Beta) -> begin
true
end
| (Iota, Iota) -> begin
true
end
| (Zeta, Zeta) -> begin
true
end
| (Weak, Weak) -> begin
true
end
| (HNF, HNF) -> begin
true
end
| (Primops, Primops) -> begin
true
end
| (Eager_unfolding, Eager_unfolding) -> begin
true
end
| (Inlining, Inlining) -> begin
true
end
| (DoNotUnfoldPureLets, DoNotUnfoldPureLets) -> begin
true
end
| (UnfoldTac, UnfoldTac) -> begin
true
end
| (PureSubtermsWithinComputations, PureSubtermsWithinComputations) -> begin
true
end
| (Simplify, Simplify) -> begin
true
end
| (EraseUniverses, EraseUniverses) -> begin
true
end
| (AllowUnboundUniverses, AllowUnboundUniverses) -> begin
true
end
| (Reify, Reify) -> begin
true
end
| (CompressUvars, CompressUvars) -> begin
true
end
| (NoFullNorm, NoFullNorm) -> begin
true
end
| (CheckNoUvars, CheckNoUvars) -> begin
true
end
| (Unmeta, Unmeta) -> begin
true
end
| (Unascribe, Unascribe) -> begin
true
end
| (NBE, NBE) -> begin
true
end
| (Exclude (s11), Exclude (s21)) -> begin
(eq_step s11 s21)
end
| (UnfoldUntil (s11), UnfoldUntil (s21)) -> begin
(Prims.op_Equality s11 s21)
end
| (UnfoldOnly (lids1), UnfoldOnly (lids2)) -> begin
((Prims.op_Equality (FStar_List.length lids1) (FStar_List.length lids2)) && (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2))
end
| (UnfoldFully (lids1), UnfoldFully (lids2)) -> begin
((Prims.op_Equality (FStar_List.length lids1) (FStar_List.length lids2)) && (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2))
end
| (UnfoldAttr (lids1), UnfoldAttr (lids2)) -> begin
((Prims.op_Equality (FStar_List.length lids1) (FStar_List.length lids2)) && (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2))
end
| uu____513 -> begin
false
end))


type sig_binding =
(FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)

type delta_level =
| NoDelta
| InliningDelta
| Eager_unfolding_only
| Unfold of FStar_Syntax_Syntax.delta_depth


let uu___is_NoDelta : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoDelta -> begin
true
end
| uu____539 -> begin
false
end))


let uu___is_InliningDelta : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InliningDelta -> begin
true
end
| uu____550 -> begin
false
end))


let uu___is_Eager_unfolding_only : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding_only -> begin
true
end
| uu____561 -> begin
false
end))


let uu___is_Unfold : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unfold (_0) -> begin
true
end
| uu____573 -> begin
false
end))


let __proj__Unfold__item___0 : delta_level  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| Unfold (_0) -> begin
_0
end))


type name_prefix =
Prims.string Prims.list


type proof_namespace =
(name_prefix * Prims.bool) Prims.list


type cached_elt =
(((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option)) FStar_Util.either * FStar_Range.range)


type goal =
FStar_Syntax_Syntax.term

type mlift =
{mlift_wp : env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t); mlift_term : (FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option} 
 and edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : mlift} 
 and effects =
{decls : (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list} 
 and env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : FStar_Syntax_Syntax.binding Prims.list; gamma_sig : sig_binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; attrtab : FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.univ_names) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; lax : Prims.bool; lax_universes : Prims.bool; phase1 : Prims.bool; failhard : Prims.bool; nosynth : Prims.bool; uvar_subtyping : Prims.bool; tc_term : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp * FStar_TypeChecker_Common.guard_t); type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Common.guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; check_type_of : Prims.bool  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.guard_t; use_bv_sorts : Prims.bool; qtbl_name_and_index : (Prims.int FStar_Util.smap * (FStar_Ident.lident * Prims.int) FStar_Pervasives_Native.option); normalized_eff_names : FStar_Ident.lident FStar_Util.smap; fv_delta_depths : FStar_Syntax_Syntax.delta_depth FStar_Util.smap; proof_ns : proof_namespace; synth_hook : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term; splice : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list; mpreprocess : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term; postprocess : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term; is_native_tactic : FStar_Ident.lid  ->  Prims.bool; identifier_info : FStar_TypeChecker_Common.id_info_table FStar_ST.ref; tc_hooks : tcenv_hooks; dsenv : FStar_Syntax_DsEnv.env; nbe : step Prims.list  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term; strict_args_tab : Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap; erasable_types_tab : Prims.bool FStar_Util.smap} 
 and solver_t =
{init : env  ->  unit; push : Prims.string  ->  unit; pop : Prims.string  ->  unit; snapshot : Prims.string  ->  ((Prims.int * Prims.int * Prims.int) * unit); rollback : Prims.string  ->  (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  unit; preprocess : env  ->  goal  ->  (env * goal * FStar_Options.optionstate) Prims.list; solve : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  unit; finish : unit  ->  unit; refresh : unit  ->  unit} 
 and tcenv_hooks =
{tc_push_in_gamma_hook : env  ->  (FStar_Syntax_Syntax.binding, sig_binding) FStar_Util.either  ->  unit}


let __proj__Mkmlift__item__mlift_wp : mlift  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t) = (fun projectee -> (match (projectee) with
| {mlift_wp = mlift_wp; mlift_term = mlift_term} -> begin
mlift_wp
end))


let __proj__Mkmlift__item__mlift_term : mlift  ->  (FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {mlift_wp = mlift_wp; mlift_term = mlift_term} -> begin
mlift_term
end))


let __proj__Mkedge__item__msource : edge  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {msource = msource; mtarget = mtarget; mlift = mlift} -> begin
msource
end))


let __proj__Mkedge__item__mtarget : edge  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {msource = msource; mtarget = mtarget; mlift = mlift} -> begin
mtarget
end))


let __proj__Mkedge__item__mlift : edge  ->  mlift = (fun projectee -> (match (projectee) with
| {msource = msource; mtarget = mtarget; mlift = mlift} -> begin
mlift
end))


let __proj__Mkeffects__item__decls : effects  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) Prims.list = (fun projectee -> (match (projectee) with
| {decls = decls; order = order; joins = joins} -> begin
decls
end))


let __proj__Mkeffects__item__order : effects  ->  edge Prims.list = (fun projectee -> (match (projectee) with
| {decls = decls; order = order; joins = joins} -> begin
order
end))


let __proj__Mkeffects__item__joins : effects  ->  (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list = (fun projectee -> (match (projectee) with
| {decls = decls; order = order; joins = joins} -> begin
joins
end))


let __proj__Mkenv__item__solver : env  ->  solver_t = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
solver
end))


let __proj__Mkenv__item__range : env  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
range
end))


let __proj__Mkenv__item__curmodule : env  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
curmodule
end))


let __proj__Mkenv__item__gamma : env  ->  FStar_Syntax_Syntax.binding Prims.list = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
gamma
end))


let __proj__Mkenv__item__gamma_sig : env  ->  sig_binding Prims.list = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
gamma_sig
end))


let __proj__Mkenv__item__gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
gamma_cache
end))


let __proj__Mkenv__item__modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
modules
end))


let __proj__Mkenv__item__expected_typ : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
expected_typ
end))


let __proj__Mkenv__item__sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
sigtab
end))


let __proj__Mkenv__item__attrtab : env  ->  FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
attrtab
end))


let __proj__Mkenv__item__instantiate_imp : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
instantiate_imp
end))


let __proj__Mkenv__item__effects : env  ->  effects = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
effects
end))


let __proj__Mkenv__item__generalize : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
generalize
end))


let __proj__Mkenv__item__letrecs : env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.univ_names) Prims.list = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
letrecs
end))


let __proj__Mkenv__item__top_level : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
top_level
end))


let __proj__Mkenv__item__check_uvars : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
check_uvars
end))


let __proj__Mkenv__item__use_eq : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
use_eq
end))


let __proj__Mkenv__item__is_iface : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
is_iface
end))


let __proj__Mkenv__item__admit : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
admit1
end))


let __proj__Mkenv__item__lax : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
lax1
end))


let __proj__Mkenv__item__lax_universes : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
lax_universes
end))


let __proj__Mkenv__item__phase1 : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
phase1
end))


let __proj__Mkenv__item__failhard : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
failhard
end))


let __proj__Mkenv__item__nosynth : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
nosynth
end))


let __proj__Mkenv__item__uvar_subtyping : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
uvar_subtyping
end))


let __proj__Mkenv__item__tc_term : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp * FStar_TypeChecker_Common.guard_t) = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
tc_term
end))


let __proj__Mkenv__item__type_of : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Common.guard_t) = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
type_of
end))


let __proj__Mkenv__item__universe_of : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
universe_of
end))


let __proj__Mkenv__item__check_type_of : env  ->  Prims.bool  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.guard_t = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
check_type_of
end))


let __proj__Mkenv__item__use_bv_sorts : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
use_bv_sorts
end))


let __proj__Mkenv__item__qtbl_name_and_index : env  ->  (Prims.int FStar_Util.smap * (FStar_Ident.lident * Prims.int) FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
qtbl_name_and_index
end))


let __proj__Mkenv__item__normalized_eff_names : env  ->  FStar_Ident.lident FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
normalized_eff_names
end))


let __proj__Mkenv__item__fv_delta_depths : env  ->  FStar_Syntax_Syntax.delta_depth FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
fv_delta_depths
end))


let __proj__Mkenv__item__proof_ns : env  ->  proof_namespace = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
proof_ns
end))


let __proj__Mkenv__item__synth_hook : env  ->  env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
synth_hook
end))


let __proj__Mkenv__item__splice : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
splice1
end))


let __proj__Mkenv__item__mpreprocess : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
mpreprocess
end))


let __proj__Mkenv__item__postprocess : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
postprocess
end))


let __proj__Mkenv__item__is_native_tactic : env  ->  FStar_Ident.lid  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
is_native_tactic
end))


let __proj__Mkenv__item__identifier_info : env  ->  FStar_TypeChecker_Common.id_info_table FStar_ST.ref = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
identifier_info
end))


let __proj__Mkenv__item__tc_hooks : env  ->  tcenv_hooks = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
tc_hooks
end))


let __proj__Mkenv__item__dsenv : env  ->  FStar_Syntax_DsEnv.env = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
dsenv
end))


let __proj__Mkenv__item__nbe : env  ->  step Prims.list  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
nbe1
end))


let __proj__Mkenv__item__strict_args_tab : env  ->  Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
strict_args_tab
end))


let __proj__Mkenv__item__erasable_types_tab : env  ->  Prims.bool FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; mpreprocess = mpreprocess; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1; strict_args_tab = strict_args_tab; erasable_types_tab = erasable_types_tab} -> begin
erasable_types_tab
end))


let __proj__Mksolver_t__item__init : solver_t  ->  env  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
init1
end))


let __proj__Mksolver_t__item__push : solver_t  ->  Prims.string  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
push1
end))


let __proj__Mksolver_t__item__pop : solver_t  ->  Prims.string  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
pop1
end))


let __proj__Mksolver_t__item__snapshot : solver_t  ->  Prims.string  ->  ((Prims.int * Prims.int * Prims.int) * unit) = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
snapshot1
end))


let __proj__Mksolver_t__item__rollback : solver_t  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
rollback1
end))


let __proj__Mksolver_t__item__encode_sig : solver_t  ->  env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
encode_sig
end))


let __proj__Mksolver_t__item__preprocess : solver_t  ->  env  ->  goal  ->  (env * goal * FStar_Options.optionstate) Prims.list = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
preprocess
end))


let __proj__Mksolver_t__item__solve : solver_t  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
solve
end))


let __proj__Mksolver_t__item__finish : solver_t  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
finish1
end))


let __proj__Mksolver_t__item__refresh : solver_t  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
refresh
end))


let __proj__Mktcenv_hooks__item__tc_push_in_gamma_hook : tcenv_hooks  ->  env  ->  (FStar_Syntax_Syntax.binding, sig_binding) FStar_Util.either  ->  unit = (fun projectee -> (match (projectee) with
| {tc_push_in_gamma_hook = tc_push_in_gamma_hook} -> begin
tc_push_in_gamma_hook
end))


type lift_comp_t =
env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t)


type solver_depth_t =
(Prims.int * Prims.int * Prims.int)


type implicit =
FStar_TypeChecker_Common.implicit


type implicits =
FStar_TypeChecker_Common.implicits


type guard_t =
FStar_TypeChecker_Common.guard_t


let preprocess : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env tau tm -> (env.mpreprocess env tau tm))


let postprocess : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env tau ty tm -> (env.postprocess env tau ty tm))


let rename_gamma : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.gamma  ->  FStar_Syntax_Syntax.gamma = (fun subst1 gamma -> (FStar_All.pipe_right gamma (FStar_List.map (fun uu___0_12966 -> (match (uu___0_12966) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let y = (

let uu____12969 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Subst.subst subst1 uu____12969))
in (

let uu____12970 = (

let uu____12971 = (FStar_Syntax_Subst.compress y)
in uu____12971.FStar_Syntax_Syntax.n)
in (match (uu____12970) with
| FStar_Syntax_Syntax.Tm_name (y1) -> begin
(

let uu____12975 = (

let uu___315_12976 = y1
in (

let uu____12977 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___315_12976.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___315_12976.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____12977}))
in FStar_Syntax_Syntax.Binding_var (uu____12975))
end
| uu____12980 -> begin
(failwith "Not a renaming")
end)))
end
| b -> begin
b
end)))))


let rename_env : FStar_Syntax_Syntax.subst_t  ->  env  ->  env = (fun subst1 env -> (

let uu___321_12994 = env
in (

let uu____12995 = (rename_gamma subst1 env.gamma)
in {solver = uu___321_12994.solver; range = uu___321_12994.range; curmodule = uu___321_12994.curmodule; gamma = uu____12995; gamma_sig = uu___321_12994.gamma_sig; gamma_cache = uu___321_12994.gamma_cache; modules = uu___321_12994.modules; expected_typ = uu___321_12994.expected_typ; sigtab = uu___321_12994.sigtab; attrtab = uu___321_12994.attrtab; instantiate_imp = uu___321_12994.instantiate_imp; effects = uu___321_12994.effects; generalize = uu___321_12994.generalize; letrecs = uu___321_12994.letrecs; top_level = uu___321_12994.top_level; check_uvars = uu___321_12994.check_uvars; use_eq = uu___321_12994.use_eq; is_iface = uu___321_12994.is_iface; admit = uu___321_12994.admit; lax = uu___321_12994.lax; lax_universes = uu___321_12994.lax_universes; phase1 = uu___321_12994.phase1; failhard = uu___321_12994.failhard; nosynth = uu___321_12994.nosynth; uvar_subtyping = uu___321_12994.uvar_subtyping; tc_term = uu___321_12994.tc_term; type_of = uu___321_12994.type_of; universe_of = uu___321_12994.universe_of; check_type_of = uu___321_12994.check_type_of; use_bv_sorts = uu___321_12994.use_bv_sorts; qtbl_name_and_index = uu___321_12994.qtbl_name_and_index; normalized_eff_names = uu___321_12994.normalized_eff_names; fv_delta_depths = uu___321_12994.fv_delta_depths; proof_ns = uu___321_12994.proof_ns; synth_hook = uu___321_12994.synth_hook; splice = uu___321_12994.splice; mpreprocess = uu___321_12994.mpreprocess; postprocess = uu___321_12994.postprocess; is_native_tactic = uu___321_12994.is_native_tactic; identifier_info = uu___321_12994.identifier_info; tc_hooks = uu___321_12994.tc_hooks; dsenv = uu___321_12994.dsenv; nbe = uu___321_12994.nbe; strict_args_tab = uu___321_12994.strict_args_tab; erasable_types_tab = uu___321_12994.erasable_types_tab})))


let default_tc_hooks : tcenv_hooks = {tc_push_in_gamma_hook = (fun uu____13003 uu____13004 -> ())}


let tc_hooks : env  ->  tcenv_hooks = (fun env -> env.tc_hooks)


let set_tc_hooks : env  ->  tcenv_hooks  ->  env = (fun env hooks -> (

let uu___328_13026 = env
in {solver = uu___328_13026.solver; range = uu___328_13026.range; curmodule = uu___328_13026.curmodule; gamma = uu___328_13026.gamma; gamma_sig = uu___328_13026.gamma_sig; gamma_cache = uu___328_13026.gamma_cache; modules = uu___328_13026.modules; expected_typ = uu___328_13026.expected_typ; sigtab = uu___328_13026.sigtab; attrtab = uu___328_13026.attrtab; instantiate_imp = uu___328_13026.instantiate_imp; effects = uu___328_13026.effects; generalize = uu___328_13026.generalize; letrecs = uu___328_13026.letrecs; top_level = uu___328_13026.top_level; check_uvars = uu___328_13026.check_uvars; use_eq = uu___328_13026.use_eq; is_iface = uu___328_13026.is_iface; admit = uu___328_13026.admit; lax = uu___328_13026.lax; lax_universes = uu___328_13026.lax_universes; phase1 = uu___328_13026.phase1; failhard = uu___328_13026.failhard; nosynth = uu___328_13026.nosynth; uvar_subtyping = uu___328_13026.uvar_subtyping; tc_term = uu___328_13026.tc_term; type_of = uu___328_13026.type_of; universe_of = uu___328_13026.universe_of; check_type_of = uu___328_13026.check_type_of; use_bv_sorts = uu___328_13026.use_bv_sorts; qtbl_name_and_index = uu___328_13026.qtbl_name_and_index; normalized_eff_names = uu___328_13026.normalized_eff_names; fv_delta_depths = uu___328_13026.fv_delta_depths; proof_ns = uu___328_13026.proof_ns; synth_hook = uu___328_13026.synth_hook; splice = uu___328_13026.splice; mpreprocess = uu___328_13026.mpreprocess; postprocess = uu___328_13026.postprocess; is_native_tactic = uu___328_13026.is_native_tactic; identifier_info = uu___328_13026.identifier_info; tc_hooks = hooks; dsenv = uu___328_13026.dsenv; nbe = uu___328_13026.nbe; strict_args_tab = uu___328_13026.strict_args_tab; erasable_types_tab = uu___328_13026.erasable_types_tab}))


let set_dep_graph : env  ->  FStar_Parser_Dep.deps  ->  env = (fun e g -> (

let uu___332_13038 = e
in (

let uu____13039 = (FStar_Syntax_DsEnv.set_dep_graph e.dsenv g)
in {solver = uu___332_13038.solver; range = uu___332_13038.range; curmodule = uu___332_13038.curmodule; gamma = uu___332_13038.gamma; gamma_sig = uu___332_13038.gamma_sig; gamma_cache = uu___332_13038.gamma_cache; modules = uu___332_13038.modules; expected_typ = uu___332_13038.expected_typ; sigtab = uu___332_13038.sigtab; attrtab = uu___332_13038.attrtab; instantiate_imp = uu___332_13038.instantiate_imp; effects = uu___332_13038.effects; generalize = uu___332_13038.generalize; letrecs = uu___332_13038.letrecs; top_level = uu___332_13038.top_level; check_uvars = uu___332_13038.check_uvars; use_eq = uu___332_13038.use_eq; is_iface = uu___332_13038.is_iface; admit = uu___332_13038.admit; lax = uu___332_13038.lax; lax_universes = uu___332_13038.lax_universes; phase1 = uu___332_13038.phase1; failhard = uu___332_13038.failhard; nosynth = uu___332_13038.nosynth; uvar_subtyping = uu___332_13038.uvar_subtyping; tc_term = uu___332_13038.tc_term; type_of = uu___332_13038.type_of; universe_of = uu___332_13038.universe_of; check_type_of = uu___332_13038.check_type_of; use_bv_sorts = uu___332_13038.use_bv_sorts; qtbl_name_and_index = uu___332_13038.qtbl_name_and_index; normalized_eff_names = uu___332_13038.normalized_eff_names; fv_delta_depths = uu___332_13038.fv_delta_depths; proof_ns = uu___332_13038.proof_ns; synth_hook = uu___332_13038.synth_hook; splice = uu___332_13038.splice; mpreprocess = uu___332_13038.mpreprocess; postprocess = uu___332_13038.postprocess; is_native_tactic = uu___332_13038.is_native_tactic; identifier_info = uu___332_13038.identifier_info; tc_hooks = uu___332_13038.tc_hooks; dsenv = uu____13039; nbe = uu___332_13038.nbe; strict_args_tab = uu___332_13038.strict_args_tab; erasable_types_tab = uu___332_13038.erasable_types_tab})))


let dep_graph : env  ->  FStar_Parser_Dep.deps = (fun e -> (FStar_Syntax_DsEnv.dep_graph e.dsenv))


type env_t =
env


type sigtable =
FStar_Syntax_Syntax.sigelt FStar_Util.smap


let should_verify : env  ->  Prims.bool = (fun env -> (((not (env.lax)) && (not (env.admit))) && (FStar_Options.should_verify env.curmodule.FStar_Ident.str)))


let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match (((d), (q))) with
| (NoDelta, uu____13068) -> begin
true
end
| (Eager_unfolding_only, FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____13071), FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____13073), FStar_Syntax_Syntax.Visible_default) -> begin
true
end
| (InliningDelta, FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| uu____13076 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab : 'Auu____13090 . unit  ->  'Auu____13090 FStar_Util.smap = (fun uu____13097 -> (FStar_Util.smap_create default_table_size))


let new_gamma_cache : 'Auu____13103 . unit  ->  'Auu____13103 FStar_Util.smap = (fun uu____13110 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let initial_env : FStar_Parser_Dep.deps  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  (Prims.bool  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  guard_t)  ->  solver_t  ->  FStar_Ident.lident  ->  (step Prims.list  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  env = (fun deps tc_term type_of universe_of check_type_of solver module_lid nbe1 -> (

let uu____13248 = (new_gamma_cache ())
in (

let uu____13251 = (new_sigtab ())
in (

let uu____13254 = (new_sigtab ())
in (

let uu____13261 = (

let uu____13276 = (FStar_Util.smap_create (Prims.parse_int "10"))
in ((uu____13276), (FStar_Pervasives_Native.None)))
in (

let uu____13297 = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let uu____13301 = (FStar_Util.smap_create (Prims.parse_int "50"))
in (

let uu____13305 = (FStar_Options.using_facts_from ())
in (

let uu____13306 = (FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty)
in (

let uu____13309 = (FStar_Syntax_DsEnv.empty_env deps)
in (

let uu____13310 = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let uu____13324 = (FStar_Util.smap_create (Prims.parse_int "20"))
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_sig = []; gamma_cache = uu____13248; modules = []; expected_typ = FStar_Pervasives_Native.None; sigtab = uu____13251; attrtab = uu____13254; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; phase1 = false; failhard = false; nosynth = false; uvar_subtyping = true; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = false; qtbl_name_and_index = uu____13261; normalized_eff_names = uu____13297; fv_delta_depths = uu____13301; proof_ns = uu____13305; synth_hook = (fun e g tau -> (failwith "no synthesizer available")); splice = (fun e tau -> (failwith "no splicer available")); mpreprocess = (fun e tau tm -> (failwith "no preprocessor available")); postprocess = (fun e tau typ tm -> (failwith "no postprocessor available")); is_native_tactic = (fun uu____13397 -> false); identifier_info = uu____13306; tc_hooks = default_tc_hooks; dsenv = uu____13309; nbe = nbe1; strict_args_tab = uu____13310; erasable_types_tab = uu____13324}))))))))))))


let dsenv : env  ->  FStar_Syntax_DsEnv.env = (fun env -> env.dsenv)


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let attrtab : env  ->  FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap = (fun env -> env.attrtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


let query_indices : (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let push_query_indices : unit  ->  unit = (fun uu____13476 -> (

let uu____13477 = (FStar_ST.op_Bang query_indices)
in (match (uu____13477) with
| [] -> begin
(failwith "Empty query indices!")
end
| uu____13532 -> begin
(

let uu____13542 = (

let uu____13552 = (

let uu____13560 = (FStar_ST.op_Bang query_indices)
in (FStar_List.hd uu____13560))
in (

let uu____13614 = (FStar_ST.op_Bang query_indices)
in (uu____13552)::uu____13614))
in (FStar_ST.op_Colon_Equals query_indices uu____13542))
end)))


let pop_query_indices : unit  ->  unit = (fun uu____13710 -> (

let uu____13711 = (FStar_ST.op_Bang query_indices)
in (match (uu____13711) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals query_indices tl1)
end)))


let snapshot_query_indices : unit  ->  (Prims.int * unit) = (fun uu____13838 -> (FStar_Common.snapshot push_query_indices query_indices ()))


let rollback_query_indices : Prims.int FStar_Pervasives_Native.option  ->  unit = (fun depth -> (FStar_Common.rollback pop_query_indices query_indices depth))


let add_query_index : (FStar_Ident.lident * Prims.int)  ->  unit = (fun uu____13875 -> (match (uu____13875) with
| (l, n1) -> begin
(

let uu____13885 = (FStar_ST.op_Bang query_indices)
in (match (uu____13885) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals query_indices (((((l), (n1)))::hd1)::tl1))
end
| uu____14007 -> begin
(failwith "Empty query indices")
end))
end))


let peek_query_indices : unit  ->  (FStar_Ident.lident * Prims.int) Prims.list = (fun uu____14030 -> (

let uu____14031 = (FStar_ST.op_Bang query_indices)
in (FStar_List.hd uu____14031)))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push_stack : env  ->  env = (fun env -> ((

let uu____14099 = (

let uu____14102 = (FStar_ST.op_Bang stack)
in (env)::uu____14102)
in (FStar_ST.op_Colon_Equals stack uu____14099));
(

let uu___403_14151 = env
in (

let uu____14152 = (FStar_Util.smap_copy (gamma_cache env))
in (

let uu____14155 = (FStar_Util.smap_copy (sigtab env))
in (

let uu____14158 = (FStar_Util.smap_copy (attrtab env))
in (

let uu____14165 = (

let uu____14180 = (

let uu____14184 = (FStar_All.pipe_right env.qtbl_name_and_index FStar_Pervasives_Native.fst)
in (FStar_Util.smap_copy uu____14184))
in (

let uu____14216 = (FStar_All.pipe_right env.qtbl_name_and_index FStar_Pervasives_Native.snd)
in ((uu____14180), (uu____14216))))
in (

let uu____14265 = (FStar_Util.smap_copy env.normalized_eff_names)
in (

let uu____14268 = (FStar_Util.smap_copy env.fv_delta_depths)
in (

let uu____14271 = (

let uu____14274 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_Util.mk_ref uu____14274))
in (

let uu____14294 = (FStar_Util.smap_copy env.strict_args_tab)
in (

let uu____14307 = (FStar_Util.smap_copy env.erasable_types_tab)
in {solver = uu___403_14151.solver; range = uu___403_14151.range; curmodule = uu___403_14151.curmodule; gamma = uu___403_14151.gamma; gamma_sig = uu___403_14151.gamma_sig; gamma_cache = uu____14152; modules = uu___403_14151.modules; expected_typ = uu___403_14151.expected_typ; sigtab = uu____14155; attrtab = uu____14158; instantiate_imp = uu___403_14151.instantiate_imp; effects = uu___403_14151.effects; generalize = uu___403_14151.generalize; letrecs = uu___403_14151.letrecs; top_level = uu___403_14151.top_level; check_uvars = uu___403_14151.check_uvars; use_eq = uu___403_14151.use_eq; is_iface = uu___403_14151.is_iface; admit = uu___403_14151.admit; lax = uu___403_14151.lax; lax_universes = uu___403_14151.lax_universes; phase1 = uu___403_14151.phase1; failhard = uu___403_14151.failhard; nosynth = uu___403_14151.nosynth; uvar_subtyping = uu___403_14151.uvar_subtyping; tc_term = uu___403_14151.tc_term; type_of = uu___403_14151.type_of; universe_of = uu___403_14151.universe_of; check_type_of = uu___403_14151.check_type_of; use_bv_sorts = uu___403_14151.use_bv_sorts; qtbl_name_and_index = uu____14165; normalized_eff_names = uu____14265; fv_delta_depths = uu____14268; proof_ns = uu___403_14151.proof_ns; synth_hook = uu___403_14151.synth_hook; splice = uu___403_14151.splice; mpreprocess = uu___403_14151.mpreprocess; postprocess = uu___403_14151.postprocess; is_native_tactic = uu___403_14151.is_native_tactic; identifier_info = uu____14271; tc_hooks = uu___403_14151.tc_hooks; dsenv = uu___403_14151.dsenv; nbe = uu___403_14151.nbe; strict_args_tab = uu____14294; erasable_types_tab = uu____14307}))))))))));
))


let pop_stack : unit  ->  env = (fun uu____14317 -> (

let uu____14318 = (FStar_ST.op_Bang stack)
in (match (uu____14318) with
| (env)::tl1 -> begin
((FStar_ST.op_Colon_Equals stack tl1);
env;
)
end
| uu____14372 -> begin
(failwith "Impossible: Too many pops")
end)))


let snapshot_stack : env  ->  (Prims.int * env) = (fun env -> (FStar_Common.snapshot push_stack stack env))


let rollback_stack : Prims.int FStar_Pervasives_Native.option  ->  env = (fun depth -> (FStar_Common.rollback pop_stack stack depth))


type tcenv_depth_t =
(Prims.int * Prims.int * solver_depth_t * Prims.int)


let snapshot : env  ->  Prims.string  ->  (tcenv_depth_t * env) = (fun env msg -> (FStar_Util.atomically (fun uu____14462 -> (

let uu____14463 = (snapshot_stack env)
in (match (uu____14463) with
| (stack_depth, env1) -> begin
(

let uu____14497 = (snapshot_query_indices ())
in (match (uu____14497) with
| (query_indices_depth, ()) -> begin
(

let uu____14530 = (env1.solver.snapshot msg)
in (match (uu____14530) with
| (solver_depth, ()) -> begin
(

let uu____14587 = (FStar_Syntax_DsEnv.snapshot env1.dsenv)
in (match (uu____14587) with
| (dsenv_depth, dsenv1) -> begin
((((stack_depth), (query_indices_depth), (solver_depth), (dsenv_depth))), ((

let uu___428_14654 = env1
in {solver = uu___428_14654.solver; range = uu___428_14654.range; curmodule = uu___428_14654.curmodule; gamma = uu___428_14654.gamma; gamma_sig = uu___428_14654.gamma_sig; gamma_cache = uu___428_14654.gamma_cache; modules = uu___428_14654.modules; expected_typ = uu___428_14654.expected_typ; sigtab = uu___428_14654.sigtab; attrtab = uu___428_14654.attrtab; instantiate_imp = uu___428_14654.instantiate_imp; effects = uu___428_14654.effects; generalize = uu___428_14654.generalize; letrecs = uu___428_14654.letrecs; top_level = uu___428_14654.top_level; check_uvars = uu___428_14654.check_uvars; use_eq = uu___428_14654.use_eq; is_iface = uu___428_14654.is_iface; admit = uu___428_14654.admit; lax = uu___428_14654.lax; lax_universes = uu___428_14654.lax_universes; phase1 = uu___428_14654.phase1; failhard = uu___428_14654.failhard; nosynth = uu___428_14654.nosynth; uvar_subtyping = uu___428_14654.uvar_subtyping; tc_term = uu___428_14654.tc_term; type_of = uu___428_14654.type_of; universe_of = uu___428_14654.universe_of; check_type_of = uu___428_14654.check_type_of; use_bv_sorts = uu___428_14654.use_bv_sorts; qtbl_name_and_index = uu___428_14654.qtbl_name_and_index; normalized_eff_names = uu___428_14654.normalized_eff_names; fv_delta_depths = uu___428_14654.fv_delta_depths; proof_ns = uu___428_14654.proof_ns; synth_hook = uu___428_14654.synth_hook; splice = uu___428_14654.splice; mpreprocess = uu___428_14654.mpreprocess; postprocess = uu___428_14654.postprocess; is_native_tactic = uu___428_14654.is_native_tactic; identifier_info = uu___428_14654.identifier_info; tc_hooks = uu___428_14654.tc_hooks; dsenv = dsenv1; nbe = uu___428_14654.nbe; strict_args_tab = uu___428_14654.strict_args_tab; erasable_types_tab = uu___428_14654.erasable_types_tab})))
end))
end))
end))
end)))))


let rollback : solver_t  ->  Prims.string  ->  tcenv_depth_t FStar_Pervasives_Native.option  ->  env = (fun solver msg depth -> (FStar_Util.atomically (fun uu____14688 -> (

let uu____14689 = (match (depth) with
| FStar_Pervasives_Native.Some (s1, s2, s3, s4) -> begin
((FStar_Pervasives_Native.Some (s1)), (FStar_Pervasives_Native.Some (s2)), (FStar_Pervasives_Native.Some (s3)), (FStar_Pervasives_Native.Some (s4)))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
in (match (uu____14689) with
| (stack_depth, query_indices_depth, solver_depth, dsenv_depth) -> begin
((solver.rollback msg solver_depth);
(match (()) with
| () -> begin
((rollback_query_indices query_indices_depth);
(match (()) with
| () -> begin
(

let tcenv = (rollback_stack stack_depth)
in (

let dsenv1 = (FStar_Syntax_DsEnv.rollback dsenv_depth)
in ((

let uu____14869 = (FStar_Util.physical_equality tcenv.dsenv dsenv1)
in (FStar_Common.runtime_assert uu____14869 "Inconsistent stack state"));
tcenv;
)))
end);
)
end);
)
end)))))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let uu____14885 = (snapshot env msg)
in (FStar_Pervasives_Native.snd uu____14885)))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (rollback env.solver msg FStar_Pervasives_Native.None))


let incr_query_index : env  ->  env = (fun env -> (

let qix = (peek_query_indices ())
in (match (env.qtbl_name_and_index) with
| (uu____14917, FStar_Pervasives_Native.None) -> begin
env
end
| (tbl, FStar_Pervasives_Native.Some (l, n1)) -> begin
(

let uu____14959 = (FStar_All.pipe_right qix (FStar_List.tryFind (fun uu____14989 -> (match (uu____14989) with
| (m, uu____14997) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____14959) with
| FStar_Pervasives_Native.None -> begin
(

let next = (n1 + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(FStar_Util.smap_add tbl l.FStar_Ident.str next);
(

let uu___473_15012 = env
in {solver = uu___473_15012.solver; range = uu___473_15012.range; curmodule = uu___473_15012.curmodule; gamma = uu___473_15012.gamma; gamma_sig = uu___473_15012.gamma_sig; gamma_cache = uu___473_15012.gamma_cache; modules = uu___473_15012.modules; expected_typ = uu___473_15012.expected_typ; sigtab = uu___473_15012.sigtab; attrtab = uu___473_15012.attrtab; instantiate_imp = uu___473_15012.instantiate_imp; effects = uu___473_15012.effects; generalize = uu___473_15012.generalize; letrecs = uu___473_15012.letrecs; top_level = uu___473_15012.top_level; check_uvars = uu___473_15012.check_uvars; use_eq = uu___473_15012.use_eq; is_iface = uu___473_15012.is_iface; admit = uu___473_15012.admit; lax = uu___473_15012.lax; lax_universes = uu___473_15012.lax_universes; phase1 = uu___473_15012.phase1; failhard = uu___473_15012.failhard; nosynth = uu___473_15012.nosynth; uvar_subtyping = uu___473_15012.uvar_subtyping; tc_term = uu___473_15012.tc_term; type_of = uu___473_15012.type_of; universe_of = uu___473_15012.universe_of; check_type_of = uu___473_15012.check_type_of; use_bv_sorts = uu___473_15012.use_bv_sorts; qtbl_name_and_index = ((tbl), (FStar_Pervasives_Native.Some (((l), (next))))); normalized_eff_names = uu___473_15012.normalized_eff_names; fv_delta_depths = uu___473_15012.fv_delta_depths; proof_ns = uu___473_15012.proof_ns; synth_hook = uu___473_15012.synth_hook; splice = uu___473_15012.splice; mpreprocess = uu___473_15012.mpreprocess; postprocess = uu___473_15012.postprocess; is_native_tactic = uu___473_15012.is_native_tactic; identifier_info = uu___473_15012.identifier_info; tc_hooks = uu___473_15012.tc_hooks; dsenv = uu___473_15012.dsenv; nbe = uu___473_15012.nbe; strict_args_tab = uu___473_15012.strict_args_tab; erasable_types_tab = uu___473_15012.erasable_types_tab});
))
end
| FStar_Pervasives_Native.Some (uu____15029, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(FStar_Util.smap_add tbl l.FStar_Ident.str next);
(

let uu___482_15045 = env
in {solver = uu___482_15045.solver; range = uu___482_15045.range; curmodule = uu___482_15045.curmodule; gamma = uu___482_15045.gamma; gamma_sig = uu___482_15045.gamma_sig; gamma_cache = uu___482_15045.gamma_cache; modules = uu___482_15045.modules; expected_typ = uu___482_15045.expected_typ; sigtab = uu___482_15045.sigtab; attrtab = uu___482_15045.attrtab; instantiate_imp = uu___482_15045.instantiate_imp; effects = uu___482_15045.effects; generalize = uu___482_15045.generalize; letrecs = uu___482_15045.letrecs; top_level = uu___482_15045.top_level; check_uvars = uu___482_15045.check_uvars; use_eq = uu___482_15045.use_eq; is_iface = uu___482_15045.is_iface; admit = uu___482_15045.admit; lax = uu___482_15045.lax; lax_universes = uu___482_15045.lax_universes; phase1 = uu___482_15045.phase1; failhard = uu___482_15045.failhard; nosynth = uu___482_15045.nosynth; uvar_subtyping = uu___482_15045.uvar_subtyping; tc_term = uu___482_15045.tc_term; type_of = uu___482_15045.type_of; universe_of = uu___482_15045.universe_of; check_type_of = uu___482_15045.check_type_of; use_bv_sorts = uu___482_15045.use_bv_sorts; qtbl_name_and_index = ((tbl), (FStar_Pervasives_Native.Some (((l), (next))))); normalized_eff_names = uu___482_15045.normalized_eff_names; fv_delta_depths = uu___482_15045.fv_delta_depths; proof_ns = uu___482_15045.proof_ns; synth_hook = uu___482_15045.synth_hook; splice = uu___482_15045.splice; mpreprocess = uu___482_15045.mpreprocess; postprocess = uu___482_15045.postprocess; is_native_tactic = uu___482_15045.is_native_tactic; identifier_info = uu___482_15045.identifier_info; tc_hooks = uu___482_15045.tc_hooks; dsenv = uu___482_15045.dsenv; nbe = uu___482_15045.nbe; strict_args_tab = uu___482_15045.strict_args_tab; erasable_types_tab = uu___482_15045.erasable_types_tab});
))
end))
end)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> (match ((Prims.op_Equality r FStar_Range.dummyRange)) with
| true -> begin
e
end
| uu____15086 -> begin
(

let uu___489_15088 = e
in {solver = uu___489_15088.solver; range = r; curmodule = uu___489_15088.curmodule; gamma = uu___489_15088.gamma; gamma_sig = uu___489_15088.gamma_sig; gamma_cache = uu___489_15088.gamma_cache; modules = uu___489_15088.modules; expected_typ = uu___489_15088.expected_typ; sigtab = uu___489_15088.sigtab; attrtab = uu___489_15088.attrtab; instantiate_imp = uu___489_15088.instantiate_imp; effects = uu___489_15088.effects; generalize = uu___489_15088.generalize; letrecs = uu___489_15088.letrecs; top_level = uu___489_15088.top_level; check_uvars = uu___489_15088.check_uvars; use_eq = uu___489_15088.use_eq; is_iface = uu___489_15088.is_iface; admit = uu___489_15088.admit; lax = uu___489_15088.lax; lax_universes = uu___489_15088.lax_universes; phase1 = uu___489_15088.phase1; failhard = uu___489_15088.failhard; nosynth = uu___489_15088.nosynth; uvar_subtyping = uu___489_15088.uvar_subtyping; tc_term = uu___489_15088.tc_term; type_of = uu___489_15088.type_of; universe_of = uu___489_15088.universe_of; check_type_of = uu___489_15088.check_type_of; use_bv_sorts = uu___489_15088.use_bv_sorts; qtbl_name_and_index = uu___489_15088.qtbl_name_and_index; normalized_eff_names = uu___489_15088.normalized_eff_names; fv_delta_depths = uu___489_15088.fv_delta_depths; proof_ns = uu___489_15088.proof_ns; synth_hook = uu___489_15088.synth_hook; splice = uu___489_15088.splice; mpreprocess = uu___489_15088.mpreprocess; postprocess = uu___489_15088.postprocess; is_native_tactic = uu___489_15088.is_native_tactic; identifier_info = uu___489_15088.identifier_info; tc_hooks = uu___489_15088.tc_hooks; dsenv = uu___489_15088.dsenv; nbe = uu___489_15088.nbe; strict_args_tab = uu___489_15088.strict_args_tab; erasable_types_tab = uu___489_15088.erasable_types_tab})
end))


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let toggle_id_info : env  ->  Prims.bool  ->  unit = (fun env enabled -> (

let uu____15108 = (

let uu____15109 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_toggle uu____15109 enabled))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____15108)))


let insert_bv_info : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun env bv ty -> (

let uu____15164 = (

let uu____15165 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_insert_bv uu____15165 bv ty))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____15164)))


let insert_fv_info : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun env fv ty -> (

let uu____15220 = (

let uu____15221 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_insert_fv uu____15221 fv ty))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____15220)))


let promote_id_info : env  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  unit = (fun env ty_map -> (

let uu____15276 = (

let uu____15277 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_promote uu____15277 ty_map))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____15276)))


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let uu___506_15341 = env
in {solver = uu___506_15341.solver; range = uu___506_15341.range; curmodule = lid; gamma = uu___506_15341.gamma; gamma_sig = uu___506_15341.gamma_sig; gamma_cache = uu___506_15341.gamma_cache; modules = uu___506_15341.modules; expected_typ = uu___506_15341.expected_typ; sigtab = uu___506_15341.sigtab; attrtab = uu___506_15341.attrtab; instantiate_imp = uu___506_15341.instantiate_imp; effects = uu___506_15341.effects; generalize = uu___506_15341.generalize; letrecs = uu___506_15341.letrecs; top_level = uu___506_15341.top_level; check_uvars = uu___506_15341.check_uvars; use_eq = uu___506_15341.use_eq; is_iface = uu___506_15341.is_iface; admit = uu___506_15341.admit; lax = uu___506_15341.lax; lax_universes = uu___506_15341.lax_universes; phase1 = uu___506_15341.phase1; failhard = uu___506_15341.failhard; nosynth = uu___506_15341.nosynth; uvar_subtyping = uu___506_15341.uvar_subtyping; tc_term = uu___506_15341.tc_term; type_of = uu___506_15341.type_of; universe_of = uu___506_15341.universe_of; check_type_of = uu___506_15341.check_type_of; use_bv_sorts = uu___506_15341.use_bv_sorts; qtbl_name_and_index = uu___506_15341.qtbl_name_and_index; normalized_eff_names = uu___506_15341.normalized_eff_names; fv_delta_depths = uu___506_15341.fv_delta_depths; proof_ns = uu___506_15341.proof_ns; synth_hook = uu___506_15341.synth_hook; splice = uu___506_15341.splice; mpreprocess = uu___506_15341.mpreprocess; postprocess = uu___506_15341.postprocess; is_native_tactic = uu___506_15341.is_native_tactic; identifier_info = uu___506_15341.identifier_info; tc_hooks = uu___506_15341.tc_hooks; dsenv = uu___506_15341.dsenv; nbe = uu___506_15341.nbe; strict_args_tab = uu___506_15341.strict_args_tab; erasable_types_tab = uu___506_15341.erasable_types_tab}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun env lid -> (

let uu____15372 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.smap_try_find (sigtab env) uu____15372)))


let name_not_found : FStar_Ident.lid  ->  (FStar_Errors.raw_error * Prims.string) = (fun l -> (

let uu____15385 = (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_NameNotFound), (uu____15385))))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  (FStar_Errors.raw_error * Prims.string) = (fun v1 -> (

let uu____15400 = (

let uu____15402 = (FStar_Syntax_Print.bv_to_string v1)
in (FStar_Util.format1 "Variable \"%s\" not found" uu____15402))
in ((FStar_Errors.Fatal_VariableNotFound), (uu____15400))))


let new_u_univ : unit  ->  FStar_Syntax_Syntax.universe = (fun uu____15411 -> (

let uu____15412 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____15412)))


let mk_univ_subst : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun formals us -> (

let n1 = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n1 - i)), (u))))))))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), uu____15512) -> begin
(

let vs = (mk_univ_subst formals us)
in (

let uu____15536 = (FStar_Syntax_Subst.subst vs t)
in ((us), (uu____15536))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun uu___1_15553 -> (match (uu___1_15553) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun uu____15579 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let uu____15599 = (inst_tscheme t)
in (match (uu____15599) with
| (us, t1) -> begin
(

let uu____15610 = (FStar_Syntax_Subst.set_use_range r t1)
in ((us), (uu____15610)))
end)))


let check_effect_is_not_a_template : FStar_Syntax_Syntax.eff_decl  ->  FStar_Range.range  ->  unit = (fun ed rng -> (match (((Prims.op_disEquality (FStar_List.length ed.FStar_Syntax_Syntax.univs) (Prims.parse_int "0")) || (Prims.op_disEquality (FStar_List.length ed.FStar_Syntax_Syntax.binders) (Prims.parse_int "0")))) with
| true -> begin
(

let msg = (

let uu____15635 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____15637 = (FStar_Syntax_Print.binders_to_string ", " ed.FStar_Syntax_Syntax.binders)
in (FStar_Util.format2 "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position" uu____15635 uu____15637)))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NotEnoughArgumentsForEffect), (msg)) rng))
end
| uu____15642 -> begin
()
end))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed uu____15664 -> (match (uu____15664) with
| (us, t) -> begin
((check_effect_is_not_a_template ed env.range);
(match ((Prims.op_disEquality (FStar_List.length insts) (FStar_List.length us))) with
| true -> begin
(

let uu____15678 = (

let uu____15680 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length us))
in (

let uu____15684 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (

let uu____15688 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____15690 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" uu____15680 uu____15684 uu____15688 uu____15690)))))
in (failwith uu____15678))
end
| uu____15693 -> begin
()
end);
(

let uu____15695 = (inst_tscheme_with ((us), (t)) insts)
in (FStar_Pervasives_Native.snd uu____15695));
)
end))

type tri =
| Yes
| No
| Maybe


let uu___is_Yes : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Yes -> begin
true
end
| uu____15713 -> begin
false
end))


let uu___is_No : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____15724 -> begin
false
end))


let uu___is_Maybe : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____15735 -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in (match ((Prims.op_Equality l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
Yes
end
| uu____15751 -> begin
(match ((FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur1 = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l1 -> (match (((c), (l1))) with
| ([], uu____15783) -> begin
Maybe
end
| (uu____15790, []) -> begin
No
end
| ((hd1)::tl1, (hd')::tl') when (Prims.op_Equality hd1.FStar_Ident.idText hd'.FStar_Ident.idText) -> begin
(aux tl1 tl')
end
| uu____15810 -> begin
No
end))
in (aux cur1 lns))))
end
| uu____15819 -> begin
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

let uu____15904 = (FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)
in (match (uu____15904) with
| FStar_Pervasives_Native.None -> begin
(

let uu____15927 = (FStar_Util.find_map env.gamma (fun uu___2_15971 -> (match (uu___2_15971) with
| FStar_Syntax_Syntax.Binding_lid (l, t) -> begin
(

let uu____16010 = (FStar_Ident.lid_equals lid l)
in (match (uu____16010) with
| true -> begin
(

let uu____16033 = (

let uu____16052 = (

let uu____16067 = (inst_tscheme t)
in FStar_Util.Inl (uu____16067))
in (

let uu____16082 = (FStar_Ident.range_of_lid l)
in ((uu____16052), (uu____16082))))
in FStar_Pervasives_Native.Some (uu____16033))
end
| uu____16115 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____16135 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_Util.catch_opt uu____15927 (fun uu____16173 -> (FStar_Util.find_map env.gamma_sig (fun uu___3_16183 -> (match (uu___3_16183) with
| (uu____16186, {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (ses, uu____16188); FStar_Syntax_Syntax.sigrng = uu____16189; FStar_Syntax_Syntax.sigquals = uu____16190; FStar_Syntax_Syntax.sigmeta = uu____16191; FStar_Syntax_Syntax.sigattrs = uu____16192; FStar_Syntax_Syntax.sigopts = uu____16193}) -> begin
(FStar_Util.find_map ses (fun se -> (

let uu____16215 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____16215) with
| true -> begin
(cache ((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| uu____16249 -> begin
FStar_Pervasives_Native.None
end))))
end
| (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____16267) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____16274 -> begin
(cache t)
end))
in (

let uu____16275 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____16275) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____16281 = (

let uu____16282 = (FStar_Ident.range_of_lid l)
in ((FStar_Util.Inr (((s), (FStar_Pervasives_Native.None)))), (uu____16282)))
in (maybe_cache uu____16281))
end)))
end))))))
end
| se -> begin
se
end))
end
| uu____16312 -> begin
FStar_Pervasives_Native.None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| uu____16351 -> begin
(

let uu____16353 = (find_in_sigtab env lid)
in (match (uu____16353) with
| FStar_Pervasives_Native.Some (se) -> begin
FStar_Pervasives_Native.Some (((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end)))))


let lookup_sigelt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun env lid -> (

let uu____16434 = (lookup_qname env lid)
in (match (uu____16434) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (uu____16455), rng) -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, us), rng) -> begin
FStar_Pervasives_Native.Some (se)
end)))


let lookup_attr : env  ->  Prims.string  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env attr -> (

let uu____16569 = (FStar_Util.smap_try_find (attrtab env) attr)
in (match (uu____16569) with
| FStar_Pervasives_Native.Some (ses) -> begin
ses
end
| FStar_Pervasives_Native.None -> begin
[]
end)))


let add_se_to_attrtab : env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun env se -> (

let add_one1 = (fun env1 se1 attr -> (

let uu____16614 = (

let uu____16617 = (lookup_attr env1 attr)
in (se1)::uu____16617)
in (FStar_Util.smap_add (attrtab env1) attr uu____16614)))
in (FStar_List.iter (fun attr -> (

let uu____16627 = (

let uu____16628 = (FStar_Syntax_Subst.compress attr)
in uu____16628.FStar_Syntax_Syntax.n)
in (match (uu____16627) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____16632 = (

let uu____16634 = (FStar_Syntax_Syntax.lid_of_fv fv)
in uu____16634.FStar_Ident.str)
in (add_one1 env se uu____16632))
end
| uu____16635 -> begin
()
end))) se.FStar_Syntax_Syntax.sigattrs)))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____16658) -> begin
(add_sigelts env ses)
end
| uu____16667 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids);
(add_se_to_attrtab env se);
))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) FStar_Pervasives_Native.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun uu___4_16705 -> (match (uu___4_16705) with
| FStar_Syntax_Syntax.Binding_var (id1) when (FStar_Syntax_Syntax.bv_eq id1 bv) -> begin
FStar_Pervasives_Native.Some (((id1.FStar_Syntax_Syntax.sort), (id1.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
end
| uu____16723 -> begin
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
| FStar_Syntax_Syntax.Sig_let ((uu____16785, (lb)::[]), uu____16787) -> begin
(

let uu____16796 = (

let uu____16805 = (inst_tscheme1 ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____16814 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in ((uu____16805), (uu____16814))))
in FStar_Pervasives_Native.Some (uu____16796))
end
| FStar_Syntax_Syntax.Sig_let ((uu____16827, lbs), uu____16829) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____16861) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
(

let uu____16874 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____16874) with
| true -> begin
(

let uu____16887 = (

let uu____16896 = (inst_tscheme1 ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____16905 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____16896), (uu____16905))))
in FStar_Pervasives_Native.Some (uu____16887))
end
| uu____16918 -> begin
FStar_Pervasives_Native.None
end))
end)))
end
| uu____16928 -> begin
FStar_Pervasives_Native.None
end)))


let effect_signature : FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) FStar_Pervasives_Native.option = (fun us_opt se rng -> (

let inst_ts = (fun us_opt1 ts -> (match (us_opt1) with
| FStar_Pervasives_Native.None -> begin
(inst_tscheme ts)
end
| FStar_Pervasives_Native.Some (us) -> begin
(inst_tscheme_with ts us)
end))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
((check_effect_is_not_a_template ne rng);
(match (us_opt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (us) -> begin
(match ((Prims.op_disEquality (FStar_List.length us) (FStar_List.length (FStar_Pervasives_Native.fst ne.FStar_Syntax_Syntax.signature)))) with
| true -> begin
(

let uu____17020 = (

let uu____17022 = (

let uu____17024 = (

let uu____17026 = (

let uu____17028 = (FStar_Util.string_of_int (FStar_List.length (FStar_Pervasives_Native.fst ne.FStar_Syntax_Syntax.signature)))
in (

let uu____17034 = (

let uu____17036 = (FStar_Util.string_of_int (FStar_List.length us))
in (Prims.op_Hat ", got " uu____17036))
in (Prims.op_Hat uu____17028 uu____17034)))
in (Prims.op_Hat ", expected " uu____17026))
in (Prims.op_Hat ne.FStar_Syntax_Syntax.mname.FStar_Ident.str uu____17024))
in (Prims.op_Hat "effect_signature: incorrect number of universes for the signature of " uu____17022))
in (failwith uu____17020))
end
| uu____17041 -> begin
()
end)
end);
(

let uu____17043 = (

let uu____17052 = (inst_ts us_opt ne.FStar_Syntax_Syntax.signature)
in ((uu____17052), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____17043));
)
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, uu____17072, uu____17073) -> begin
(

let uu____17078 = (

let uu____17087 = (

let uu____17092 = (

let uu____17093 = (

let uu____17096 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders uu____17096))
in ((us), (uu____17093)))
in (inst_ts us_opt uu____17092))
in ((uu____17087), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____17078))
end
| uu____17115 -> begin
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

let mapper = (fun uu____17204 -> (match (uu____17204) with
| (lr, rng) -> begin
(match (lr) with
| FStar_Util.Inl (t) -> begin
FStar_Pervasives_Native.Some (((t), (rng)))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____17300, uvs, t, uu____17303, uu____17304, uu____17305); FStar_Syntax_Syntax.sigrng = uu____17306; FStar_Syntax_Syntax.sigquals = uu____17307; FStar_Syntax_Syntax.sigmeta = uu____17308; FStar_Syntax_Syntax.sigattrs = uu____17309; FStar_Syntax_Syntax.sigopts = uu____17310}, FStar_Pervasives_Native.None) -> begin
(

let uu____17335 = (

let uu____17344 = (inst_tscheme1 ((uvs), (t)))
in ((uu____17344), (rng)))
in FStar_Pervasives_Native.Some (uu____17335))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t); FStar_Syntax_Syntax.sigrng = uu____17368; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____17370; FStar_Syntax_Syntax.sigattrs = uu____17371; FStar_Syntax_Syntax.sigopts = uu____17372}, FStar_Pervasives_Native.None) -> begin
(

let uu____17391 = (

let uu____17393 = (in_cur_mod env l)
in (Prims.op_Equality uu____17393 Yes))
in (match (uu____17391) with
| true -> begin
(

let uu____17405 = ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface)
in (match (uu____17405) with
| true -> begin
(

let uu____17421 = (

let uu____17430 = (inst_tscheme1 ((uvs), (t)))
in ((uu____17430), (rng)))
in FStar_Pervasives_Native.Some (uu____17421))
end
| uu____17451 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____17461 -> begin
(

let uu____17463 = (

let uu____17472 = (inst_tscheme1 ((uvs), (t)))
in ((uu____17472), (rng)))
in FStar_Pervasives_Native.Some (uu____17463))
end))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____17497, uu____17498); FStar_Syntax_Syntax.sigrng = uu____17499; FStar_Syntax_Syntax.sigquals = uu____17500; FStar_Syntax_Syntax.sigmeta = uu____17501; FStar_Syntax_Syntax.sigattrs = uu____17502; FStar_Syntax_Syntax.sigopts = uu____17503}, FStar_Pervasives_Native.None) -> begin
(match (tps) with
| [] -> begin
(

let uu____17546 = (

let uu____17555 = (inst_tscheme1 ((uvs), (k)))
in ((uu____17555), (rng)))
in FStar_Pervasives_Native.Some (uu____17546))
end
| uu____17576 -> begin
(

let uu____17577 = (

let uu____17586 = (

let uu____17591 = (

let uu____17592 = (

let uu____17595 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____17595))
in ((uvs), (uu____17592)))
in (inst_tscheme1 uu____17591))
in ((uu____17586), (rng)))
in FStar_Pervasives_Native.Some (uu____17577))
end)
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____17618, uu____17619); FStar_Syntax_Syntax.sigrng = uu____17620; FStar_Syntax_Syntax.sigquals = uu____17621; FStar_Syntax_Syntax.sigmeta = uu____17622; FStar_Syntax_Syntax.sigattrs = uu____17623; FStar_Syntax_Syntax.sigopts = uu____17624}, FStar_Pervasives_Native.Some (us)) -> begin
(match (tps) with
| [] -> begin
(

let uu____17668 = (

let uu____17677 = (inst_tscheme_with ((uvs), (k)) us)
in ((uu____17677), (rng)))
in FStar_Pervasives_Native.Some (uu____17668))
end
| uu____17698 -> begin
(

let uu____17699 = (

let uu____17708 = (

let uu____17713 = (

let uu____17714 = (

let uu____17717 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____17717))
in ((uvs), (uu____17714)))
in (inst_tscheme_with uu____17713 us))
in ((uu____17708), (rng)))
in FStar_Pervasives_Native.Some (uu____17699))
end)
end
| FStar_Util.Inr (se) -> begin
(

let uu____17753 = (match (se) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____17774); FStar_Syntax_Syntax.sigrng = uu____17775; FStar_Syntax_Syntax.sigquals = uu____17776; FStar_Syntax_Syntax.sigmeta = uu____17777; FStar_Syntax_Syntax.sigattrs = uu____17778; FStar_Syntax_Syntax.sigopts = uu____17779}, FStar_Pervasives_Native.None) -> begin
(lookup_type_of_let us_opt (FStar_Pervasives_Native.fst se) lid)
end
| uu____17796 -> begin
(effect_signature us_opt (FStar_Pervasives_Native.fst se) env.range)
end)
in (FStar_All.pipe_right uu____17753 (FStar_Util.map_option (fun uu____17844 -> (match (uu____17844) with
| (us_t, rng1) -> begin
((us_t), (rng1))
end)))))
end)
end))
in (

let uu____17875 = (

let uu____17886 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____17886 mapper))
in (match (uu____17875) with
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
(

let uu____17960 = (

let uu____17971 = (

let uu____17978 = (

let uu___843_17981 = t
in (

let uu____17982 = (FStar_Ident.range_of_lid lid)
in {FStar_Syntax_Syntax.n = uu___843_17981.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = uu____17982; FStar_Syntax_Syntax.vars = uu___843_17981.FStar_Syntax_Syntax.vars}))
in ((us), (uu____17978)))
in ((uu____17971), (r)))
in FStar_Pervasives_Native.Some (uu____17960))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____18031 = (lookup_qname env l)
in (match (uu____18031) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____18052) -> begin
true
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) = (fun env bv -> (

let bvr = (FStar_Syntax_Syntax.range_of_bv bv)
in (

let uu____18106 = (try_lookup_bv env bv)
in (match (uu____18106) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18121 = (variable_not_found bv)
in (FStar_Errors.raise_error uu____18121 bvr))
end
| FStar_Pervasives_Native.Some (t, r) -> begin
(

let uu____18137 = (FStar_Syntax_Subst.set_use_range bvr t)
in (

let uu____18138 = (

let uu____18139 = (FStar_Range.use_range bvr)
in (FStar_Range.set_use_range r uu____18139))
in ((uu____18137), (uu____18138))))
end))))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) FStar_Pervasives_Native.option = (fun env l -> (

let uu____18161 = (try_lookup_lid_aux FStar_Pervasives_Native.None env l)
in (match (uu____18161) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
(

let use_range1 = (FStar_Ident.range_of_lid l)
in (

let r1 = (

let uu____18227 = (FStar_Range.use_range use_range1)
in (FStar_Range.set_use_range r uu____18227))
in (

let uu____18228 = (

let uu____18237 = (

let uu____18242 = (FStar_Syntax_Subst.set_use_range use_range1 t)
in ((us), (uu____18242)))
in ((uu____18237), (r1)))
in FStar_Pervasives_Native.Some (uu____18228))))
end)))


let try_lookup_and_inst_lid : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) FStar_Pervasives_Native.option = (fun env us l -> (

let uu____18277 = (try_lookup_lid_aux (FStar_Pervasives_Native.Some (us)) env l)
in (match (uu____18277) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((uu____18310, t), r) -> begin
(

let use_range1 = (FStar_Ident.range_of_lid l)
in (

let r1 = (

let uu____18335 = (FStar_Range.use_range use_range1)
in (FStar_Range.set_use_range r uu____18335))
in (

let uu____18336 = (

let uu____18341 = (FStar_Syntax_Subst.set_use_range use_range1 t)
in ((uu____18341), (r1)))
in FStar_Pervasives_Native.Some (uu____18336))))
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) = (fun env l -> (

let uu____18365 = (try_lookup_lid env l)
in (match (uu____18365) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18392 = (name_not_found l)
in (

let uu____18398 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____18392 uu____18398)))
end
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end)))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun uu___5_18441 -> (match (uu___5_18441) with
| FStar_Syntax_Syntax.Binding_univ (y) -> begin
(Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)
end
| uu____18445 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env lid -> (

let uu____18466 = (lookup_qname env lid)
in (match (uu____18466) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____18475, uvs, t); FStar_Syntax_Syntax.sigrng = uu____18478; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____18480; FStar_Syntax_Syntax.sigattrs = uu____18481; FStar_Syntax_Syntax.sigopts = uu____18482}, FStar_Pervasives_Native.None), uu____18483) -> begin
(

let uu____18534 = (

let uu____18541 = (

let uu____18542 = (

let uu____18545 = (FStar_Ident.range_of_lid lid)
in (FStar_Syntax_Subst.set_use_range uu____18545 t))
in ((uvs), (uu____18542)))
in ((uu____18541), (q)))
in FStar_Pervasives_Native.Some (uu____18534))
end
| uu____18558 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____18580 = (lookup_qname env lid)
in (match (uu____18580) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____18585, uvs, t); FStar_Syntax_Syntax.sigrng = uu____18588; FStar_Syntax_Syntax.sigquals = uu____18589; FStar_Syntax_Syntax.sigmeta = uu____18590; FStar_Syntax_Syntax.sigattrs = uu____18591; FStar_Syntax_Syntax.sigopts = uu____18592}, FStar_Pervasives_Native.None), uu____18593) -> begin
(

let uu____18644 = (FStar_Ident.range_of_lid lid)
in (inst_tscheme_with_range uu____18644 ((uvs), (t))))
end
| uu____18649 -> begin
(

let uu____18650 = (name_not_found lid)
in (

let uu____18656 = (FStar_Ident.range_of_lid lid)
in (FStar_Errors.raise_error uu____18650 uu____18656)))
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____18676 = (lookup_qname env lid)
in (match (uu____18676) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____18681, uvs, t, uu____18684, uu____18685, uu____18686); FStar_Syntax_Syntax.sigrng = uu____18687; FStar_Syntax_Syntax.sigquals = uu____18688; FStar_Syntax_Syntax.sigmeta = uu____18689; FStar_Syntax_Syntax.sigattrs = uu____18690; FStar_Syntax_Syntax.sigopts = uu____18691}, FStar_Pervasives_Native.None), uu____18692) -> begin
(

let uu____18749 = (FStar_Ident.range_of_lid lid)
in (inst_tscheme_with_range uu____18749 ((uvs), (t))))
end
| uu____18754 -> begin
(

let uu____18755 = (name_not_found lid)
in (

let uu____18761 = (FStar_Ident.range_of_lid lid)
in (FStar_Errors.raise_error uu____18755 uu____18761)))
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  (Prims.bool * FStar_Ident.lident Prims.list) = (fun env lid -> (

let uu____18784 = (lookup_qname env lid)
in (match (uu____18784) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____18792, uu____18793, uu____18794, uu____18795, uu____18796, dcs); FStar_Syntax_Syntax.sigrng = uu____18798; FStar_Syntax_Syntax.sigquals = uu____18799; FStar_Syntax_Syntax.sigmeta = uu____18800; FStar_Syntax_Syntax.sigattrs = uu____18801; FStar_Syntax_Syntax.sigopts = uu____18802}, uu____18803), uu____18804) -> begin
((true), (dcs))
end
| uu____18869 -> begin
((false), ([]))
end)))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____18885 = (lookup_qname env lid)
in (match (uu____18885) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____18886, uu____18887, uu____18888, l, uu____18890, uu____18891); FStar_Syntax_Syntax.sigrng = uu____18892; FStar_Syntax_Syntax.sigquals = uu____18893; FStar_Syntax_Syntax.sigmeta = uu____18894; FStar_Syntax_Syntax.sigattrs = uu____18895; FStar_Syntax_Syntax.sigopts = uu____18896}, uu____18897), uu____18898) -> begin
l
end
| uu____18957 -> begin
(

let uu____18958 = (

let uu____18960 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" uu____18960))
in (failwith uu____18958))
end)))


let lookup_definition_qninfo_aux : Prims.bool  ->  delta_level Prims.list  ->  FStar_Ident.lident  ->  qninfo  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option = (fun rec_ok delta_levels lid qninfo -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____19030) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, lbs), uu____19087) when ((visible se.FStar_Syntax_Syntax.sigquals) && ((not (is_rec)) || rec_ok)) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____19111 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____19111) with
| true -> begin
FStar_Pervasives_Native.Some (((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbdef)))
end
| uu____19136 -> begin
FStar_Pervasives_Native.None
end)))))
end
| uu____19146 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____19155 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_definition_qninfo : delta_level Prims.list  ->  FStar_Ident.lident  ->  qninfo  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun delta_levels lid qninfo -> (lookup_definition_qninfo_aux true delta_levels lid qninfo))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun delta_levels env lid -> (

let uu____19217 = (lookup_qname env lid)
in (FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid) uu____19217)))


let lookup_nonrec_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun delta_levels env lid -> (

let uu____19250 = (lookup_qname env lid)
in (FStar_All.pipe_left (lookup_definition_qninfo_aux false delta_levels lid) uu____19250)))


let delta_depth_of_qninfo : FStar_Syntax_Syntax.fv  ->  qninfo  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun fv qn -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((Prims.op_Equality lid.FStar_Ident.nsstr "Prims")) with
| true -> begin
FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
end
| uu____19279 -> begin
(match (qn) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "0")))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (uu____19302), uu____19303) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "0")))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, uu____19352), uu____19353) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____19402) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.Sig_bundle (uu____19420) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____19430) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____19447) -> begin
(

let uu____19454 = (FStar_Syntax_DsEnv.delta_depth_of_declaration lid se.FStar_Syntax_Syntax.sigquals)
in FStar_Pervasives_Native.Some (uu____19454))
end
| FStar_Syntax_Syntax.Sig_let ((uu____19455, lbs), uu____19457) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv1 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____19473 = (FStar_Syntax_Syntax.fv_eq_lid fv1 lid)
in (match (uu____19473) with
| true -> begin
FStar_Pervasives_Native.Some (fv1.FStar_Syntax_Syntax.fv_delta)
end
| uu____19478 -> begin
FStar_Pervasives_Native.None
end)))))
end
| FStar_Syntax_Syntax.Sig_splice (uu____19480) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1")))
end
| FStar_Syntax_Syntax.Sig_main (uu____19488) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_assume (uu____19489) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____19496) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____19497) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____19498) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_pragma (uu____19511) -> begin
FStar_Pervasives_Native.None
end)
end)
end)))


let delta_depth_of_fv : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.delta_depth = (fun env fv -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((Prims.op_Equality lid.FStar_Ident.nsstr "Prims")) with
| true -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| uu____19527 -> begin
(

let uu____19529 = (FStar_All.pipe_right lid.FStar_Ident.str (FStar_Util.smap_try_find env.fv_delta_depths))
in (FStar_All.pipe_right uu____19529 (fun d_opt -> (

let uu____19542 = (FStar_All.pipe_right d_opt FStar_Util.is_some)
in (match (uu____19542) with
| true -> begin
(FStar_All.pipe_right d_opt FStar_Util.must)
end
| uu____19550 -> begin
(

let uu____19552 = (

let uu____19555 = (lookup_qname env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (delta_depth_of_qninfo fv uu____19555))
in (match (uu____19552) with
| FStar_Pervasives_Native.None -> begin
(

let uu____19556 = (

let uu____19558 = (FStar_Syntax_Print.fv_to_string fv)
in (FStar_Util.format1 "Delta depth not found for %s" uu____19558))
in (failwith uu____19556))
end
| FStar_Pervasives_Native.Some (d) -> begin
((

let uu____19563 = ((Prims.op_disEquality d fv.FStar_Syntax_Syntax.fv_delta) && (FStar_Options.debug_any ()))
in (match (uu____19563) with
| true -> begin
(

let uu____19566 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____19568 = (FStar_Syntax_Print.delta_depth_to_string fv.FStar_Syntax_Syntax.fv_delta)
in (

let uu____19570 = (FStar_Syntax_Print.delta_depth_to_string d)
in (FStar_Util.print3 "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n" uu____19566 uu____19568 uu____19570))))
end
| uu____19573 -> begin
()
end));
(FStar_Util.smap_add env.fv_delta_depths lid.FStar_Ident.str d);
d;
)
end))
end)))))
end)))


let quals_of_qninfo : qninfo  ->  FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option = (fun qninfo -> (match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, uu____19595), uu____19596) -> begin
FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
end
| uu____19645 -> begin
FStar_Pervasives_Native.None
end))


let attrs_of_qninfo : qninfo  ->  FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option = (fun qninfo -> (match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, uu____19667), uu____19668) -> begin
FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
end
| uu____19717 -> begin
FStar_Pervasives_Native.None
end))


let lookup_attrs_of_lid : env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option = (fun env lid -> (

let uu____19739 = (lookup_qname env lid)
in (FStar_All.pipe_left attrs_of_qninfo uu____19739)))


let fv_exists_and_has_attr : env  ->  FStar_Ident.lid  ->  FStar_Ident.lident  ->  (Prims.bool * Prims.bool) = (fun env fv_lid1 attr_lid -> (

let uu____19772 = (lookup_attrs_of_lid env fv_lid1)
in (match (uu____19772) with
| FStar_Pervasives_Native.None -> begin
((false), (false))
end
| FStar_Pervasives_Native.Some (attrs) -> begin
(

let uu____19794 = (FStar_All.pipe_right attrs (FStar_Util.for_some (fun tm -> (

let uu____19803 = (

let uu____19804 = (FStar_Syntax_Util.un_uinst tm)
in uu____19804.FStar_Syntax_Syntax.n)
in (match (uu____19803) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv attr_lid)
end
| uu____19809 -> begin
false
end)))))
in ((true), (uu____19794)))
end)))


let fv_with_lid_has_attr : env  ->  FStar_Ident.lid  ->  FStar_Ident.lid  ->  Prims.bool = (fun env fv_lid1 attr_lid -> (

let uu____19832 = (fv_exists_and_has_attr env fv_lid1 attr_lid)
in (FStar_Pervasives_Native.snd uu____19832)))


let fv_has_attr : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Ident.lid  ->  Prims.bool = (fun env fv attr_lid -> (fv_with_lid_has_attr env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v attr_lid))


let cache_in_fv_tab : 'a . 'a FStar_Util.smap  ->  FStar_Syntax_Syntax.fv  ->  (unit  ->  (Prims.bool * 'a))  ->  'a = (fun tab fv f -> (

let s = (

let uu____19904 = (FStar_Syntax_Syntax.lid_of_fv fv)
in uu____19904.FStar_Ident.str)
in (

let uu____19905 = (FStar_Util.smap_try_find tab s)
in (match (uu____19905) with
| FStar_Pervasives_Native.None -> begin
(

let uu____19908 = (f ())
in (match (uu____19908) with
| (should_cache, res) -> begin
((match (should_cache) with
| true -> begin
(FStar_Util.smap_add tab s res)
end
| uu____19920 -> begin
()
end);
res;
)
end))
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end))))


let type_is_erasable : env  ->  FStar_Syntax_Syntax.fv  ->  Prims.bool = (fun env fv -> (

let f = (fun uu____19946 -> (

let uu____19947 = (fv_exists_and_has_attr env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.erasable_attr)
in (match (uu____19947) with
| (ex, erasable1) -> begin
((ex), (erasable1))
end)))
in (cache_in_fv_tab env.erasable_types_tab fv f)))


let rec non_informative : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t -> (

let uu____19981 = (

let uu____19982 = (FStar_Syntax_Util.unrefine t)
in uu____19982.FStar_Syntax_Syntax.n)
in (match (uu____19981) with
| FStar_Syntax_Syntax.Tm_type (uu____19986) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)) || (type_is_erasable env fv))
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____19990) -> begin
(non_informative env head1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____20016) -> begin
(non_informative env t1)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____20021, c) -> begin
((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (non_informative env (FStar_Syntax_Util.comp_result c)))
end
| uu____20043 -> begin
false
end)))


let fv_has_strict_args : env  ->  FStar_Syntax_Syntax.fv  ->  Prims.int Prims.list FStar_Pervasives_Native.option = (fun env fv -> (

let f = (fun uu____20076 -> (

let attrs = (

let uu____20082 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (lookup_attrs_of_lid env uu____20082))
in (match (attrs) with
| FStar_Pervasives_Native.None -> begin
((false), (FStar_Pervasives_Native.None))
end
| FStar_Pervasives_Native.Some (attrs1) -> begin
(

let res = (FStar_Util.find_map attrs1 (fun x -> (

let uu____20122 = (FStar_ToSyntax_ToSyntax.parse_attr_with_list false x FStar_Parser_Const.strict_on_arguments_attr)
in (FStar_Pervasives_Native.fst uu____20122))))
in ((true), (res)))
end)))
in (cache_in_fv_tab env.strict_args_tab fv f)))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env ftv -> (

let uu____20167 = (lookup_qname env ftv)
in (match (uu____20167) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____20171) -> begin
(

let uu____20216 = (effect_signature FStar_Pervasives_Native.None se env.range)
in (match (uu____20216) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((uu____20237, t), r) -> begin
(

let uu____20252 = (

let uu____20253 = (FStar_Ident.range_of_lid ftv)
in (FStar_Syntax_Subst.set_use_range uu____20253 t))
in FStar_Pervasives_Native.Some (uu____20252))
end))
end
| uu____20254 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (

let uu____20266 = (try_lookup_effect_lid env ftv)
in (match (uu____20266) with
| FStar_Pervasives_Native.None -> begin
(

let uu____20269 = (name_not_found ftv)
in (

let uu____20275 = (FStar_Ident.range_of_lid ftv)
in (FStar_Errors.raise_error uu____20269 uu____20275)))
end
| FStar_Pervasives_Native.Some (k) -> begin
k
end)))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun env univ_insts lid0 -> (

let uu____20299 = (lookup_qname env lid0)
in (match (uu____20299) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs1, binders, c, uu____20310); FStar_Syntax_Syntax.sigrng = uu____20311; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____20313; FStar_Syntax_Syntax.sigattrs = uu____20314; FStar_Syntax_Syntax.sigopts = uu____20315}, FStar_Pervasives_Native.None), uu____20316) -> begin
(

let lid1 = (

let uu____20372 = (

let uu____20373 = (FStar_Ident.range_of_lid lid)
in (

let uu____20374 = (

let uu____20375 = (FStar_Ident.range_of_lid lid0)
in (FStar_Range.use_range uu____20375))
in (FStar_Range.set_use_range uu____20373 uu____20374)))
in (FStar_Ident.set_lid_range lid uu____20372))
in (

let uu____20376 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___6_20382 -> (match (uu___6_20382) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____20385 -> begin
false
end))))
in (match (uu____20376) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____20398 -> begin
(

let insts = (match ((Prims.op_Equality (FStar_List.length univ_insts) (FStar_List.length univs1))) with
| true -> begin
univ_insts
end
| uu____20402 -> begin
(

let uu____20404 = (

let uu____20406 = (

let uu____20408 = (get_range env)
in (FStar_Range.string_of_range uu____20408))
in (

let uu____20409 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____20411 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format3 "(%s) Unexpected instantiation of effect %s with %s universes" uu____20406 uu____20409 uu____20411))))
in (failwith uu____20404))
end)
in (match (((binders), (univs1))) with
| ([], uu____20432) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (uu____20458, (uu____20459)::(uu____20460)::uu____20461) -> begin
(

let uu____20482 = (

let uu____20484 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____20486 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" uu____20484 uu____20486)))
in (failwith uu____20482))
end
| uu____20497 -> begin
(

let uu____20512 = (

let uu____20517 = (

let uu____20518 = (FStar_Syntax_Util.arrow binders c)
in ((univs1), (uu____20518)))
in (inst_tscheme_with uu____20517 insts))
in (match (uu____20512) with
| (uu____20531, t) -> begin
(

let t1 = (

let uu____20534 = (FStar_Ident.range_of_lid lid1)
in (FStar_Syntax_Subst.set_use_range uu____20534 t))
in (

let uu____20535 = (

let uu____20536 = (FStar_Syntax_Subst.compress t1)
in uu____20536.FStar_Syntax_Syntax.n)
in (match (uu____20535) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
FStar_Pervasives_Native.Some (((binders1), (c1)))
end
| uu____20571 -> begin
(failwith "Impossible")
end)))
end))
end))
end)))
end
| uu____20579 -> begin
FStar_Pervasives_Native.None
end)))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l -> (

let rec find1 = (fun l1 -> (

let uu____20603 = (lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l1)
in (match (uu____20603) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____20616, c) -> begin
(

let l2 = (FStar_Syntax_Util.comp_effect_name c)
in (

let uu____20623 = (find1 l2)
in (match (uu____20623) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (l2)
end
| FStar_Pervasives_Native.Some (l') -> begin
FStar_Pervasives_Native.Some (l')
end)))
end)))
in (

let res = (

let uu____20630 = (FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str)
in (match (uu____20630) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____20634 = (find1 l)
in (match (uu____20634) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (m) -> begin
((FStar_Util.smap_add env.normalized_eff_names l.FStar_Ident.str m);
m;
)
end))
end))
in (

let uu____20639 = (FStar_Ident.range_of_lid l)
in (FStar_Ident.set_lid_range res uu____20639)))))


let num_effect_indices : env  ->  FStar_Ident.lident  ->  FStar_Range.range  ->  Prims.int = (fun env name r -> (

let sig_t = (

let uu____20660 = (FStar_All.pipe_right name (lookup_effect_lid env))
in (FStar_All.pipe_right uu____20660 FStar_Syntax_Subst.compress))
in (match (sig_t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow ((_a)::bs, uu____20666) -> begin
(FStar_List.length bs)
end
| uu____20705 -> begin
(

let uu____20706 = (

let uu____20712 = (

let uu____20714 = (FStar_Ident.string_of_lid name)
in (

let uu____20716 = (FStar_Syntax_Print.term_to_string sig_t)
in (FStar_Util.format2 "Signature for %s not an arrow (%s)" uu____20714 uu____20716)))
in ((FStar_Errors.Fatal_UnexpectedSignatureForMonad), (uu____20712)))
in (FStar_Errors.raise_error uu____20706 r))
end)))


let lookup_effect_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env l -> (

let l1 = (norm_eff_name env l)
in (

let uu____20735 = (lookup_qname env l1)
in (match (uu____20735) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (uu____20738); FStar_Syntax_Syntax.sigrng = uu____20739; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____20741; FStar_Syntax_Syntax.sigattrs = uu____20742; FStar_Syntax_Syntax.sigopts = uu____20743}, uu____20744), uu____20745) -> begin
q
end
| uu____20798 -> begin
[]
end))))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail1 = (fun uu____20822 -> (

let uu____20823 = (

let uu____20825 = (FStar_Util.string_of_int i)
in (

let uu____20827 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" uu____20825 uu____20827)))
in (failwith uu____20823)))
in (

let uu____20830 = (lookup_datacon env lid)
in (match (uu____20830) with
| (uu____20835, t) -> begin
(

let uu____20837 = (

let uu____20838 = (FStar_Syntax_Subst.compress t)
in uu____20838.FStar_Syntax_Syntax.n)
in (match (uu____20837) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____20842) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail1 ())
end
| uu____20871 -> begin
(

let b = (FStar_List.nth binders i)
in (

let uu____20886 = (FStar_Syntax_Util.mk_field_projector_name lid (FStar_Pervasives_Native.fst b) i)
in (FStar_All.pipe_right uu____20886 FStar_Pervasives_Native.fst)))
end)
end
| uu____20897 -> begin
(fail1 ())
end))
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____20911 = (lookup_qname env l)
in (match (uu____20911) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____20913, uu____20914, uu____20915); FStar_Syntax_Syntax.sigrng = uu____20916; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____20918; FStar_Syntax_Syntax.sigattrs = uu____20919; FStar_Syntax_Syntax.sigopts = uu____20920}, uu____20921), uu____20922) -> begin
(FStar_Util.for_some (fun uu___7_20977 -> (match (uu___7_20977) with
| FStar_Syntax_Syntax.Projector (uu____20979) -> begin
true
end
| uu____20985 -> begin
false
end)) quals)
end
| uu____20987 -> begin
false
end)))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____21001 = (lookup_qname env lid)
in (match (uu____21001) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____21003, uu____21004, uu____21005, uu____21006, uu____21007, uu____21008); FStar_Syntax_Syntax.sigrng = uu____21009; FStar_Syntax_Syntax.sigquals = uu____21010; FStar_Syntax_Syntax.sigmeta = uu____21011; FStar_Syntax_Syntax.sigattrs = uu____21012; FStar_Syntax_Syntax.sigopts = uu____21013}, uu____21014), uu____21015) -> begin
true
end
| uu____21075 -> begin
false
end)))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____21089 = (lookup_qname env lid)
in (match (uu____21089) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____21091, uu____21092, uu____21093, uu____21094, uu____21095, uu____21096); FStar_Syntax_Syntax.sigrng = uu____21097; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____21099; FStar_Syntax_Syntax.sigattrs = uu____21100; FStar_Syntax_Syntax.sigopts = uu____21101}, uu____21102), uu____21103) -> begin
(FStar_Util.for_some (fun uu___8_21166 -> (match (uu___8_21166) with
| FStar_Syntax_Syntax.RecordType (uu____21168) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____21178) -> begin
true
end
| uu____21188 -> begin
false
end)) quals)
end
| uu____21190 -> begin
false
end)))


let qninfo_is_action : qninfo  ->  Prims.bool = (fun qninfo -> (match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____21200, uu____21201); FStar_Syntax_Syntax.sigrng = uu____21202; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____21204; FStar_Syntax_Syntax.sigattrs = uu____21205; FStar_Syntax_Syntax.sigopts = uu____21206}, uu____21207), uu____21208) -> begin
(FStar_Util.for_some (fun uu___9_21267 -> (match (uu___9_21267) with
| FStar_Syntax_Syntax.Action (uu____21269) -> begin
true
end
| uu____21271 -> begin
false
end)) quals)
end
| uu____21273 -> begin
false
end))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____21287 = (lookup_qname env lid)
in (FStar_All.pipe_left qninfo_is_action uu____21287)))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (fun env head1 -> (

let uu____21304 = (

let uu____21305 = (FStar_Syntax_Util.un_uinst head1)
in uu____21305.FStar_Syntax_Syntax.n)
in (match (uu____21304) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(match (fv.FStar_Syntax_Syntax.fv_delta) with
| FStar_Syntax_Syntax.Delta_equational_at_level (uu____21311) -> begin
true
end
| uu____21314 -> begin
false
end)
end
| uu____21316 -> begin
false
end))))


let is_irreducible : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____21330 = (lookup_qname env l)
in (match (uu____21330) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, uu____21333), uu____21334) -> begin
(FStar_Util.for_some (fun uu___10_21382 -> (match (uu___10_21382) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____21385 -> begin
false
end)) se.FStar_Syntax_Syntax.sigquals)
end
| uu____21387 -> begin
false
end)))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun x -> (match ((FStar_Pervasives_Native.fst x)) with
| FStar_Util.Inl (uu____21463) -> begin
FStar_Pervasives_Native.Some (false)
end
| FStar_Util.Inr (se, uu____21481) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____21499) -> begin
FStar_Pervasives_Native.Some ((FStar_List.contains FStar_Syntax_Syntax.New se.FStar_Syntax_Syntax.sigquals))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____21507) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____21526 -> begin
FStar_Pervasives_Native.Some (false)
end)
end))
in (

let uu____21529 = (

let uu____21533 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____21533 mapper))
in (match (uu____21529) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
false
end))))


let num_inductive_ty_params : env  ->  FStar_Ident.lident  ->  Prims.int FStar_Pervasives_Native.option = (fun env lid -> (

let uu____21593 = (lookup_qname env lid)
in (match (uu____21593) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____21597, uu____21598, tps, uu____21600, uu____21601, uu____21602); FStar_Syntax_Syntax.sigrng = uu____21603; FStar_Syntax_Syntax.sigquals = uu____21604; FStar_Syntax_Syntax.sigmeta = uu____21605; FStar_Syntax_Syntax.sigattrs = uu____21606; FStar_Syntax_Syntax.sigopts = uu____21607}, uu____21608), uu____21609) -> begin
FStar_Pervasives_Native.Some ((FStar_List.length tps))
end
| uu____21677 -> begin
FStar_Pervasives_Native.None
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun uu____21723 -> (match (uu____21723) with
| (d, uu____21732) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)
end)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (

let uu____21748 = (effect_decl_opt env l)
in (match (uu____21748) with
| FStar_Pervasives_Native.None -> begin
(

let uu____21763 = (name_not_found l)
in (

let uu____21769 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____21763 uu____21769)))
end
| FStar_Pervasives_Native.Some (md) -> begin
(FStar_Pervasives_Native.fst md)
end)))


let is_layered_effect : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____21797 = (FStar_All.pipe_right l (get_effect_decl env))
in (FStar_All.pipe_right uu____21797 FStar_Syntax_Util.is_layered)))


let identity_mlift : mlift = {mlift_wp = (fun uu____21804 c -> ((c), (FStar_TypeChecker_Common.trivial_guard))); mlift_term = FStar_Pervasives_Native.Some ((fun uu____21818 uu____21819 e -> (FStar_Util.return_all e)))}


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> (

let uu____21849 = (FStar_Ident.lid_equals l1 l2)
in (match (uu____21849) with
| true -> begin
((l1), (identity_mlift), (identity_mlift))
end
| uu____21858 -> begin
(

let uu____21860 = (((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid)))
in (match (uu____21860) with
| true -> begin
((FStar_Parser_Const.effect_GTot_lid), (identity_mlift), (identity_mlift))
end
| uu____21869 -> begin
(

let uu____21871 = (FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun uu____21924 -> (match (uu____21924) with
| (m1, m2, uu____21938, uu____21939, uu____21940) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))
in (match (uu____21871) with
| FStar_Pervasives_Native.None -> begin
(

let uu____21957 = (

let uu____21963 = (

let uu____21965 = (FStar_Syntax_Print.lid_to_string l1)
in (

let uu____21967 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" uu____21965 uu____21967)))
in ((FStar_Errors.Fatal_EffectsCannotBeComposed), (uu____21963)))
in (FStar_Errors.raise_error uu____21957 env.range))
end
| FStar_Pervasives_Native.Some (uu____21977, uu____21978, m3, j1, j2) -> begin
((m3), (j1), (j2))
end))
end))
end)))


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge FStar_Pervasives_Native.option = (fun env l1 l2 -> (

let uu____22012 = ((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)))
in (match (uu____22012) with
| true -> begin
FStar_Pervasives_Native.Some ({msource = l1; mtarget = l2; mlift = identity_mlift})
end
| uu____22017 -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)))


let wp_sig_aux : 'Auu____22032 . (FStar_Syntax_Syntax.eff_decl * 'Auu____22032) Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun decls m -> (

let uu____22061 = (FStar_All.pipe_right decls (FStar_Util.find_opt (fun uu____22087 -> (match (uu____22087) with
| (d, uu____22094) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)
end))))
in (match (uu____22061) with
| FStar_Pervasives_Native.None -> begin
(

let uu____22105 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith uu____22105))
end
| FStar_Pervasives_Native.Some (md, _q) -> begin
(

let uu____22120 = (inst_tscheme md.FStar_Syntax_Syntax.signature)
in (match (uu____22120) with
| (uu____22131, s) -> begin
(

let s1 = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s1.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, uu____22149))::((wp, uu____22151))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____22207 -> begin
(failwith "Impossible")
end))
end))
end)))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


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
| uu____22272 -> begin
c
end)
in (FStar_Syntax_Util.comp_to_comp_typ c1)))


let rec unfold_effect_abbrev : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (comp_to_comp_typ env comp)
in (

let uu____22285 = (lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name)
in (match (uu____22285) with
| FStar_Pervasives_Native.None -> begin
c
end
| FStar_Pervasives_Native.Some (binders, cdef) -> begin
(

let uu____22302 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (uu____22302) with
| (binders1, cdef1) -> begin
((match ((Prims.op_disEquality (FStar_List.length binders1) ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))) with
| true -> begin
(

let uu____22327 = (

let uu____22333 = (

let uu____22335 = (FStar_Util.string_of_int (FStar_List.length binders1))
in (

let uu____22343 = (FStar_Util.string_of_int ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))
in (

let uu____22354 = (

let uu____22356 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Print.comp_to_string uu____22356))
in (FStar_Util.format3 "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s" uu____22335 uu____22343 uu____22354))))
in ((FStar_Errors.Fatal_ConstructorArgLengthMismatch), (uu____22333)))
in (FStar_Errors.raise_error uu____22327 comp.FStar_Syntax_Syntax.pos))
end
| uu____22359 -> begin
()
end);
(

let inst1 = (

let uu____22364 = (

let uu____22375 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (uu____22375)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun uu____22412 uu____22413 -> (match (((uu____22412), (uu____22413))) with
| ((x, uu____22443), (t, uu____22445)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders1 uu____22364))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst1 cdef1)
in (

let c2 = (

let uu____22476 = (

let uu___1589_22477 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = uu___1589_22477.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___1589_22477.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___1589_22477.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___1589_22477.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right uu____22476 FStar_Syntax_Syntax.mk_Comp))
in (unfold_effect_abbrev env c2))));
)
end))
end))))


let effect_repr_aux : 'Auu____22489 . 'Auu____22489  ->  env  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun only_reifiable env c u_res -> (

let check_partial_application = (fun eff_name args -> (

let r = (get_range env)
in (

let uu____22530 = (

let uu____22537 = (num_effect_indices env eff_name r)
in (((FStar_List.length args)), (uu____22537)))
in (match (uu____22530) with
| (given, expected) -> begin
(match ((Prims.op_Equality given expected)) with
| true -> begin
()
end
| uu____22557 -> begin
(

let message = (

let uu____22561 = (FStar_Ident.string_of_lid eff_name)
in (

let uu____22563 = (FStar_Util.string_of_int given)
in (

let uu____22565 = (FStar_Util.string_of_int expected)
in (FStar_Util.format3 "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)." uu____22561 uu____22563 uu____22565))))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NotEnoughArgumentsForEffect), (message)) r))
end)
end))))
in (

let effect_name = (norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (

let uu____22570 = (effect_decl_opt env effect_name)
in (match (uu____22570) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (ed, uu____22592) -> begin
(

let uu____22603 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr)
in (match (uu____22603) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (ts) -> begin
(

let c1 = (unfold_effect_abbrev env c)
in (

let res_typ = c1.FStar_Syntax_Syntax.result_typ
in (

let repr = (inst_effect_fun_with ((u_res)::[]) env ed ts)
in ((check_partial_application effect_name c1.FStar_Syntax_Syntax.effect_args);
(

let uu____22621 = (

let uu____22624 = (get_range env)
in (

let uu____22625 = (

let uu____22632 = (

let uu____22633 = (

let uu____22650 = (

let uu____22661 = (FStar_All.pipe_right res_typ FStar_Syntax_Syntax.as_arg)
in (uu____22661)::c1.FStar_Syntax_Syntax.effect_args)
in ((repr), (uu____22650)))
in FStar_Syntax_Syntax.Tm_app (uu____22633))
in (FStar_Syntax_Syntax.mk uu____22632))
in (uu____22625 FStar_Pervasives_Native.None uu____22624)))
in FStar_Pervasives_Native.Some (uu____22621));
))))
end))
end)))))


let effect_repr : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env c u_res -> (effect_repr_aux false env c u_res))


let is_user_reifiable_effect : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env effect_lid -> (

let effect_lid1 = (norm_eff_name env effect_lid)
in (

let quals = (lookup_effect_quals env effect_lid1)
in (FStar_List.contains FStar_Syntax_Syntax.Reifiable quals))))


let is_user_reflectable_effect : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env effect_lid -> (

let effect_lid1 = (norm_eff_name env effect_lid)
in (

let quals = (lookup_effect_quals env effect_lid1)
in (FStar_All.pipe_right quals (FStar_List.existsb (fun uu___11_22761 -> (match (uu___11_22761) with
| FStar_Syntax_Syntax.Reflectable (uu____22763) -> begin
true
end
| uu____22765 -> begin
false
end)))))))


let is_total_effect : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env effect_lid -> (

let effect_lid1 = (norm_eff_name env effect_lid)
in (

let quals = (lookup_effect_quals env effect_lid1)
in (FStar_List.contains FStar_Syntax_Syntax.TotalEffect quals))))


let is_reifiable_effect : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env effect_lid -> (

let effect_lid1 = (norm_eff_name env effect_lid)
in ((is_user_reifiable_effect env effect_lid1) || (FStar_Ident.lid_equals effect_lid1 FStar_Parser_Const.effect_TAC_lid))))


let is_reifiable_rc : env  ->  FStar_Syntax_Syntax.residual_comp  ->  Prims.bool = (fun env c -> (is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect))


let is_reifiable_comp : env  ->  FStar_Syntax_Syntax.comp  ->  Prims.bool = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name)
end
| uu____22825 -> begin
false
end))


let is_reifiable_function : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____22840 = (

let uu____22841 = (FStar_Syntax_Subst.compress t)
in uu____22841.FStar_Syntax_Syntax.n)
in (match (uu____22840) with
| FStar_Syntax_Syntax.Tm_arrow (uu____22845, c) -> begin
(is_reifiable_comp env c)
end
| uu____22867 -> begin
false
end)))


let reify_comp : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let l = (FStar_Syntax_Util.comp_effect_name c)
in ((

let uu____22887 = (

let uu____22889 = (is_reifiable_effect env l)
in (not (uu____22889)))
in (match (uu____22887) with
| true -> begin
(

let uu____22892 = (

let uu____22898 = (

let uu____22900 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format1 "Effect %s cannot be reified" uu____22900))
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____22898)))
in (

let uu____22904 = (get_range env)
in (FStar_Errors.raise_error uu____22892 uu____22904)))
end
| uu____22905 -> begin
()
end));
(

let uu____22907 = (effect_repr_aux true env c u_c)
in (match (uu____22907) with
| FStar_Pervasives_Native.None -> begin
(failwith "internal error: reifiable effect has no repr?")
end
| FStar_Pervasives_Native.Some (tm) -> begin
tm
end));
)))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let sb = (((FStar_Syntax_Util.lids_of_sigelt s)), (s))
in (

let env1 = (

let uu___1666_22943 = env
in {solver = uu___1666_22943.solver; range = uu___1666_22943.range; curmodule = uu___1666_22943.curmodule; gamma = uu___1666_22943.gamma; gamma_sig = (sb)::env.gamma_sig; gamma_cache = uu___1666_22943.gamma_cache; modules = uu___1666_22943.modules; expected_typ = uu___1666_22943.expected_typ; sigtab = uu___1666_22943.sigtab; attrtab = uu___1666_22943.attrtab; instantiate_imp = uu___1666_22943.instantiate_imp; effects = uu___1666_22943.effects; generalize = uu___1666_22943.generalize; letrecs = uu___1666_22943.letrecs; top_level = uu___1666_22943.top_level; check_uvars = uu___1666_22943.check_uvars; use_eq = uu___1666_22943.use_eq; is_iface = uu___1666_22943.is_iface; admit = uu___1666_22943.admit; lax = uu___1666_22943.lax; lax_universes = uu___1666_22943.lax_universes; phase1 = uu___1666_22943.phase1; failhard = uu___1666_22943.failhard; nosynth = uu___1666_22943.nosynth; uvar_subtyping = uu___1666_22943.uvar_subtyping; tc_term = uu___1666_22943.tc_term; type_of = uu___1666_22943.type_of; universe_of = uu___1666_22943.universe_of; check_type_of = uu___1666_22943.check_type_of; use_bv_sorts = uu___1666_22943.use_bv_sorts; qtbl_name_and_index = uu___1666_22943.qtbl_name_and_index; normalized_eff_names = uu___1666_22943.normalized_eff_names; fv_delta_depths = uu___1666_22943.fv_delta_depths; proof_ns = uu___1666_22943.proof_ns; synth_hook = uu___1666_22943.synth_hook; splice = uu___1666_22943.splice; mpreprocess = uu___1666_22943.mpreprocess; postprocess = uu___1666_22943.postprocess; is_native_tactic = uu___1666_22943.is_native_tactic; identifier_info = uu___1666_22943.identifier_info; tc_hooks = uu___1666_22943.tc_hooks; dsenv = uu___1666_22943.dsenv; nbe = uu___1666_22943.nbe; strict_args_tab = uu___1666_22943.strict_args_tab; erasable_types_tab = uu___1666_22943.erasable_types_tab})
in ((add_sigelt env1 s);
(env1.tc_hooks.tc_push_in_gamma_hook env1 (FStar_Util.Inr (sb)));
env1;
))))


let push_new_effect : env  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)  ->  env = (fun env uu____22962 -> (match (uu____22962) with
| (ed, quals) -> begin
(

let effects = (

let uu___1675_22976 = env.effects
in {decls = (((ed), (quals)))::env.effects.decls; order = uu___1675_22976.order; joins = uu___1675_22976.joins})
in (

let uu___1678_22985 = env
in {solver = uu___1678_22985.solver; range = uu___1678_22985.range; curmodule = uu___1678_22985.curmodule; gamma = uu___1678_22985.gamma; gamma_sig = uu___1678_22985.gamma_sig; gamma_cache = uu___1678_22985.gamma_cache; modules = uu___1678_22985.modules; expected_typ = uu___1678_22985.expected_typ; sigtab = uu___1678_22985.sigtab; attrtab = uu___1678_22985.attrtab; instantiate_imp = uu___1678_22985.instantiate_imp; effects = effects; generalize = uu___1678_22985.generalize; letrecs = uu___1678_22985.letrecs; top_level = uu___1678_22985.top_level; check_uvars = uu___1678_22985.check_uvars; use_eq = uu___1678_22985.use_eq; is_iface = uu___1678_22985.is_iface; admit = uu___1678_22985.admit; lax = uu___1678_22985.lax; lax_universes = uu___1678_22985.lax_universes; phase1 = uu___1678_22985.phase1; failhard = uu___1678_22985.failhard; nosynth = uu___1678_22985.nosynth; uvar_subtyping = uu___1678_22985.uvar_subtyping; tc_term = uu___1678_22985.tc_term; type_of = uu___1678_22985.type_of; universe_of = uu___1678_22985.universe_of; check_type_of = uu___1678_22985.check_type_of; use_bv_sorts = uu___1678_22985.use_bv_sorts; qtbl_name_and_index = uu___1678_22985.qtbl_name_and_index; normalized_eff_names = uu___1678_22985.normalized_eff_names; fv_delta_depths = uu___1678_22985.fv_delta_depths; proof_ns = uu___1678_22985.proof_ns; synth_hook = uu___1678_22985.synth_hook; splice = uu___1678_22985.splice; mpreprocess = uu___1678_22985.mpreprocess; postprocess = uu___1678_22985.postprocess; is_native_tactic = uu___1678_22985.is_native_tactic; identifier_info = uu___1678_22985.identifier_info; tc_hooks = uu___1678_22985.tc_hooks; dsenv = uu___1678_22985.dsenv; nbe = uu___1678_22985.nbe; strict_args_tab = uu___1678_22985.strict_args_tab; erasable_types_tab = uu___1678_22985.erasable_types_tab}))
end))


let update_effect_lattice : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  mlift  ->  env = (fun env src tgt st_mlift -> (

let compose_edges = (fun e1 e2 -> (

let composed_lift = (

let mlift_wp = (fun env1 c -> (

let uu____23034 = (FStar_All.pipe_right c (e1.mlift.mlift_wp env1))
in (FStar_All.pipe_right uu____23034 (fun uu____23055 -> (match (uu____23055) with
| (c1, g1) -> begin
(

let uu____23066 = (FStar_All.pipe_right c1 (e2.mlift.mlift_wp env1))
in (FStar_All.pipe_right uu____23066 (fun uu____23087 -> (match (uu____23087) with
| (c2, g2) -> begin
(

let uu____23098 = (FStar_TypeChecker_Common.conj_guard g1 g2)
in ((c2), (uu____23098)))
end))))
end)))))
in (

let mlift_term = (match (((e1.mlift.mlift_term), (e2.mlift.mlift_term))) with
| (FStar_Pervasives_Native.Some (l1), FStar_Pervasives_Native.Some (l2)) -> begin
FStar_Pervasives_Native.Some ((fun u t e -> (

let uu____23220 = (l1 u t e)
in (l2 u t uu____23220))))
end
| uu____23221 -> begin
FStar_Pervasives_Native.None
end)
in {mlift_wp = mlift_wp; mlift_term = mlift_term}))
in {msource = e1.msource; mtarget = e2.mtarget; mlift = composed_lift}))
in (

let edge = {msource = src; mtarget = tgt; mlift = st_mlift}
in (

let id_edge = (fun l -> {msource = src; mtarget = tgt; mlift = identity_mlift})
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun uu____23289 -> (match (uu____23289) with
| (e, uu____23297) -> begin
e.FStar_Syntax_Syntax.mname
end))))
in (

let find_edge = (fun order1 uu____23320 -> (match (uu____23320) with
| (i, j) -> begin
(

let uu____23331 = (FStar_Ident.lid_equals i j)
in (match (uu____23331) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _23338 -> FStar_Pervasives_Native.Some (_23338)))
end
| uu____23339 -> begin
(FStar_All.pipe_right order1 (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end))
end))
in (

let order1 = (

let fold_fun = (fun order1 k -> (

let uu____23367 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (

let uu____23377 = (FStar_Ident.lid_equals i k)
in (match (uu____23377) with
| true -> begin
[]
end
| uu____23382 -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let uu____23391 = (FStar_Ident.lid_equals j k)
in (match (uu____23391) with
| true -> begin
[]
end
| uu____23396 -> begin
(

let uu____23398 = (

let uu____23407 = (find_edge order1 ((i), (k)))
in (

let uu____23410 = (find_edge order1 ((k), (j)))
in ((uu____23407), (uu____23410))))
in (match (uu____23398) with
| (FStar_Pervasives_Native.Some (e1), FStar_Pervasives_Native.Some (e2)) -> begin
(

let uu____23425 = (compose_edges e1 e2)
in (uu____23425)::[])
end
| uu____23426 -> begin
[]
end))
end)))))
end)))))
in (FStar_List.append order1 uu____23367)))
in (FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)))
in (

let order2 = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order1)
in ((FStar_All.pipe_right order2 (FStar_List.iter (fun edge1 -> (

let uu____23456 = ((FStar_Ident.lid_equals edge1.msource FStar_Parser_Const.effect_DIV_lid) && (

let uu____23459 = (lookup_effect_quals env edge1.mtarget)
in (FStar_All.pipe_right uu____23459 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))))
in (match (uu____23456) with
| true -> begin
(

let uu____23466 = (

let uu____23472 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge1.mtarget.FStar_Ident.str)
in ((FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal), (uu____23472)))
in (

let uu____23476 = (get_range env)
in (FStar_Errors.raise_error uu____23466 uu____23476)))
end
| uu____23477 -> begin
()
end)))));
(

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (

let uu____23554 = (FStar_Ident.lid_equals i j)
in (match (uu____23554) with
| true -> begin
FStar_Pervasives_Native.Some (((i), ((id_edge i)), ((id_edge i))))
end
| uu____23571 -> begin
(FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (

let uu____23606 = (

let uu____23615 = (find_edge order2 ((i), (k)))
in (

let uu____23618 = (find_edge order2 ((j), (k)))
in ((uu____23615), (uu____23618))))
in (match (uu____23606) with
| (FStar_Pervasives_Native.Some (ik), FStar_Pervasives_Native.Some (jk)) -> begin
(match (bopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((k), (ik), (jk)))
end
| FStar_Pervasives_Native.Some (ub, uu____23660, uu____23661) -> begin
(

let uu____23668 = (

let uu____23675 = (

let uu____23677 = (find_edge order2 ((k), (ub)))
in (FStar_Util.is_some uu____23677))
in (

let uu____23680 = (

let uu____23682 = (find_edge order2 ((ub), (k)))
in (FStar_Util.is_some uu____23682))
in ((uu____23675), (uu____23680))))
in (match (uu____23668) with
| (true, true) -> begin
(

let uu____23699 = (FStar_Ident.lid_equals k ub)
in (match (uu____23699) with
| true -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Warning_UpperBoundCandidateAlreadyVisited), ("Looking multiple times at the same upper bound candidate")));
bopt;
)
end
| uu____23713 -> begin
(failwith "Found a cycle in the lattice")
end))
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
| uu____23742 -> begin
bopt
end))) FStar_Pervasives_Native.None))
end))
in (match (join_opt) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (k, e1, e2) -> begin
(((i), (j), (k), (e1.mlift), (e2.mlift)))::[]
end))))))))
in (

let effects = (

let uu___1783_23815 = env.effects
in {decls = uu___1783_23815.decls; order = order2; joins = joins})
in (

let uu___1786_23816 = env
in {solver = uu___1786_23816.solver; range = uu___1786_23816.range; curmodule = uu___1786_23816.curmodule; gamma = uu___1786_23816.gamma; gamma_sig = uu___1786_23816.gamma_sig; gamma_cache = uu___1786_23816.gamma_cache; modules = uu___1786_23816.modules; expected_typ = uu___1786_23816.expected_typ; sigtab = uu___1786_23816.sigtab; attrtab = uu___1786_23816.attrtab; instantiate_imp = uu___1786_23816.instantiate_imp; effects = effects; generalize = uu___1786_23816.generalize; letrecs = uu___1786_23816.letrecs; top_level = uu___1786_23816.top_level; check_uvars = uu___1786_23816.check_uvars; use_eq = uu___1786_23816.use_eq; is_iface = uu___1786_23816.is_iface; admit = uu___1786_23816.admit; lax = uu___1786_23816.lax; lax_universes = uu___1786_23816.lax_universes; phase1 = uu___1786_23816.phase1; failhard = uu___1786_23816.failhard; nosynth = uu___1786_23816.nosynth; uvar_subtyping = uu___1786_23816.uvar_subtyping; tc_term = uu___1786_23816.tc_term; type_of = uu___1786_23816.type_of; universe_of = uu___1786_23816.universe_of; check_type_of = uu___1786_23816.check_type_of; use_bv_sorts = uu___1786_23816.use_bv_sorts; qtbl_name_and_index = uu___1786_23816.qtbl_name_and_index; normalized_eff_names = uu___1786_23816.normalized_eff_names; fv_delta_depths = uu___1786_23816.fv_delta_depths; proof_ns = uu___1786_23816.proof_ns; synth_hook = uu___1786_23816.synth_hook; splice = uu___1786_23816.splice; mpreprocess = uu___1786_23816.mpreprocess; postprocess = uu___1786_23816.postprocess; is_native_tactic = uu___1786_23816.is_native_tactic; identifier_info = uu___1786_23816.identifier_info; tc_hooks = uu___1786_23816.tc_hooks; dsenv = uu___1786_23816.dsenv; nbe = uu___1786_23816.nbe; strict_args_tab = uu___1786_23816.strict_args_tab; erasable_types_tab = uu___1786_23816.erasable_types_tab})));
))))))))))


let push_local_binding : env  ->  FStar_Syntax_Syntax.binding  ->  env = (fun env b -> (

let uu___1790_23828 = env
in {solver = uu___1790_23828.solver; range = uu___1790_23828.range; curmodule = uu___1790_23828.curmodule; gamma = (b)::env.gamma; gamma_sig = uu___1790_23828.gamma_sig; gamma_cache = uu___1790_23828.gamma_cache; modules = uu___1790_23828.modules; expected_typ = uu___1790_23828.expected_typ; sigtab = uu___1790_23828.sigtab; attrtab = uu___1790_23828.attrtab; instantiate_imp = uu___1790_23828.instantiate_imp; effects = uu___1790_23828.effects; generalize = uu___1790_23828.generalize; letrecs = uu___1790_23828.letrecs; top_level = uu___1790_23828.top_level; check_uvars = uu___1790_23828.check_uvars; use_eq = uu___1790_23828.use_eq; is_iface = uu___1790_23828.is_iface; admit = uu___1790_23828.admit; lax = uu___1790_23828.lax; lax_universes = uu___1790_23828.lax_universes; phase1 = uu___1790_23828.phase1; failhard = uu___1790_23828.failhard; nosynth = uu___1790_23828.nosynth; uvar_subtyping = uu___1790_23828.uvar_subtyping; tc_term = uu___1790_23828.tc_term; type_of = uu___1790_23828.type_of; universe_of = uu___1790_23828.universe_of; check_type_of = uu___1790_23828.check_type_of; use_bv_sorts = uu___1790_23828.use_bv_sorts; qtbl_name_and_index = uu___1790_23828.qtbl_name_and_index; normalized_eff_names = uu___1790_23828.normalized_eff_names; fv_delta_depths = uu___1790_23828.fv_delta_depths; proof_ns = uu___1790_23828.proof_ns; synth_hook = uu___1790_23828.synth_hook; splice = uu___1790_23828.splice; mpreprocess = uu___1790_23828.mpreprocess; postprocess = uu___1790_23828.postprocess; is_native_tactic = uu___1790_23828.is_native_tactic; identifier_info = uu___1790_23828.identifier_info; tc_hooks = uu___1790_23828.tc_hooks; dsenv = uu___1790_23828.dsenv; nbe = uu___1790_23828.nbe; strict_args_tab = uu___1790_23828.strict_args_tab; erasable_types_tab = uu___1790_23828.erasable_types_tab}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (FStar_Syntax_Syntax.Binding_var (x))))


let push_bvs : env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  env = (fun env bvs -> (FStar_List.fold_left (fun env1 bv -> (push_bv env1 bv)) env bvs))


let pop_bv : env  ->  (FStar_Syntax_Syntax.bv * env) FStar_Pervasives_Native.option = (fun env -> (match (env.gamma) with
| (FStar_Syntax_Syntax.Binding_var (x))::rest -> begin
FStar_Pervasives_Native.Some (((x), ((

let uu___1803_23886 = env
in {solver = uu___1803_23886.solver; range = uu___1803_23886.range; curmodule = uu___1803_23886.curmodule; gamma = rest; gamma_sig = uu___1803_23886.gamma_sig; gamma_cache = uu___1803_23886.gamma_cache; modules = uu___1803_23886.modules; expected_typ = uu___1803_23886.expected_typ; sigtab = uu___1803_23886.sigtab; attrtab = uu___1803_23886.attrtab; instantiate_imp = uu___1803_23886.instantiate_imp; effects = uu___1803_23886.effects; generalize = uu___1803_23886.generalize; letrecs = uu___1803_23886.letrecs; top_level = uu___1803_23886.top_level; check_uvars = uu___1803_23886.check_uvars; use_eq = uu___1803_23886.use_eq; is_iface = uu___1803_23886.is_iface; admit = uu___1803_23886.admit; lax = uu___1803_23886.lax; lax_universes = uu___1803_23886.lax_universes; phase1 = uu___1803_23886.phase1; failhard = uu___1803_23886.failhard; nosynth = uu___1803_23886.nosynth; uvar_subtyping = uu___1803_23886.uvar_subtyping; tc_term = uu___1803_23886.tc_term; type_of = uu___1803_23886.type_of; universe_of = uu___1803_23886.universe_of; check_type_of = uu___1803_23886.check_type_of; use_bv_sorts = uu___1803_23886.use_bv_sorts; qtbl_name_and_index = uu___1803_23886.qtbl_name_and_index; normalized_eff_names = uu___1803_23886.normalized_eff_names; fv_delta_depths = uu___1803_23886.fv_delta_depths; proof_ns = uu___1803_23886.proof_ns; synth_hook = uu___1803_23886.synth_hook; splice = uu___1803_23886.splice; mpreprocess = uu___1803_23886.mpreprocess; postprocess = uu___1803_23886.postprocess; is_native_tactic = uu___1803_23886.is_native_tactic; identifier_info = uu___1803_23886.identifier_info; tc_hooks = uu___1803_23886.tc_hooks; dsenv = uu___1803_23886.dsenv; nbe = uu___1803_23886.nbe; strict_args_tab = uu___1803_23886.strict_args_tab; erasable_types_tab = uu___1803_23886.erasable_types_tab}))))
end
| uu____23887 -> begin
FStar_Pervasives_Native.None
end))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env1 uu____23916 -> (match (uu____23916) with
| (x, uu____23924) -> begin
(push_bv env1 x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x1) -> begin
(

let x2 = (

let uu___1817_23959 = x1
in {FStar_Syntax_Syntax.ppname = uu___1817_23959.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1817_23959.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)})
in FStar_Syntax_Syntax.Binding_var (x2))
end
| FStar_Util.Inr (fv) -> begin
FStar_Syntax_Syntax.Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env1 x -> (push_local_binding env1 (FStar_Syntax_Syntax.Binding_univ (x)))) env xs))


let open_universes_in : env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term Prims.list  ->  (env * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term Prims.list) = (fun env uvs terms -> (

let uu____24032 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____24032) with
| (univ_subst, univ_vars) -> begin
(

let env' = (push_univ_vars env univ_vars)
in (

let uu____24060 = (FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms)
in ((env'), (univ_vars), (uu____24060))))
end)))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let uu___1838_24076 = env
in {solver = uu___1838_24076.solver; range = uu___1838_24076.range; curmodule = uu___1838_24076.curmodule; gamma = uu___1838_24076.gamma; gamma_sig = uu___1838_24076.gamma_sig; gamma_cache = uu___1838_24076.gamma_cache; modules = uu___1838_24076.modules; expected_typ = FStar_Pervasives_Native.Some (t); sigtab = uu___1838_24076.sigtab; attrtab = uu___1838_24076.attrtab; instantiate_imp = uu___1838_24076.instantiate_imp; effects = uu___1838_24076.effects; generalize = uu___1838_24076.generalize; letrecs = uu___1838_24076.letrecs; top_level = uu___1838_24076.top_level; check_uvars = uu___1838_24076.check_uvars; use_eq = false; is_iface = uu___1838_24076.is_iface; admit = uu___1838_24076.admit; lax = uu___1838_24076.lax; lax_universes = uu___1838_24076.lax_universes; phase1 = uu___1838_24076.phase1; failhard = uu___1838_24076.failhard; nosynth = uu___1838_24076.nosynth; uvar_subtyping = uu___1838_24076.uvar_subtyping; tc_term = uu___1838_24076.tc_term; type_of = uu___1838_24076.type_of; universe_of = uu___1838_24076.universe_of; check_type_of = uu___1838_24076.check_type_of; use_bv_sorts = uu___1838_24076.use_bv_sorts; qtbl_name_and_index = uu___1838_24076.qtbl_name_and_index; normalized_eff_names = uu___1838_24076.normalized_eff_names; fv_delta_depths = uu___1838_24076.fv_delta_depths; proof_ns = uu___1838_24076.proof_ns; synth_hook = uu___1838_24076.synth_hook; splice = uu___1838_24076.splice; mpreprocess = uu___1838_24076.mpreprocess; postprocess = uu___1838_24076.postprocess; is_native_tactic = uu___1838_24076.is_native_tactic; identifier_info = uu___1838_24076.identifier_info; tc_hooks = uu___1838_24076.tc_hooks; dsenv = uu___1838_24076.dsenv; nbe = uu___1838_24076.nbe; strict_args_tab = uu___1838_24076.strict_args_tab; erasable_types_tab = uu___1838_24076.erasable_types_tab}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun env -> (match (env.expected_typ) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) = (fun env_ -> (

let uu____24107 = (expected_typ env_)
in (((

let uu___1845_24113 = env_
in {solver = uu___1845_24113.solver; range = uu___1845_24113.range; curmodule = uu___1845_24113.curmodule; gamma = uu___1845_24113.gamma; gamma_sig = uu___1845_24113.gamma_sig; gamma_cache = uu___1845_24113.gamma_cache; modules = uu___1845_24113.modules; expected_typ = FStar_Pervasives_Native.None; sigtab = uu___1845_24113.sigtab; attrtab = uu___1845_24113.attrtab; instantiate_imp = uu___1845_24113.instantiate_imp; effects = uu___1845_24113.effects; generalize = uu___1845_24113.generalize; letrecs = uu___1845_24113.letrecs; top_level = uu___1845_24113.top_level; check_uvars = uu___1845_24113.check_uvars; use_eq = false; is_iface = uu___1845_24113.is_iface; admit = uu___1845_24113.admit; lax = uu___1845_24113.lax; lax_universes = uu___1845_24113.lax_universes; phase1 = uu___1845_24113.phase1; failhard = uu___1845_24113.failhard; nosynth = uu___1845_24113.nosynth; uvar_subtyping = uu___1845_24113.uvar_subtyping; tc_term = uu___1845_24113.tc_term; type_of = uu___1845_24113.type_of; universe_of = uu___1845_24113.universe_of; check_type_of = uu___1845_24113.check_type_of; use_bv_sorts = uu___1845_24113.use_bv_sorts; qtbl_name_and_index = uu___1845_24113.qtbl_name_and_index; normalized_eff_names = uu___1845_24113.normalized_eff_names; fv_delta_depths = uu___1845_24113.fv_delta_depths; proof_ns = uu___1845_24113.proof_ns; synth_hook = uu___1845_24113.synth_hook; splice = uu___1845_24113.splice; mpreprocess = uu___1845_24113.mpreprocess; postprocess = uu___1845_24113.postprocess; is_native_tactic = uu___1845_24113.is_native_tactic; identifier_info = uu___1845_24113.identifier_info; tc_hooks = uu___1845_24113.tc_hooks; dsenv = uu___1845_24113.dsenv; nbe = uu___1845_24113.nbe; strict_args_tab = uu___1845_24113.strict_args_tab; erasable_types_tab = uu___1845_24113.erasable_types_tab})), (uu____24107))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (

let uu____24125 = (

let uu____24128 = (FStar_Ident.id_of_text "")
in (uu____24128)::[])
in (FStar_Ident.lid_of_ids uu____24125))
in (fun env m -> (

let sigs = (

let uu____24135 = (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Parser_Const.prims_lid)
in (match (uu____24135) with
| true -> begin
(

let uu____24140 = (FStar_All.pipe_right env.gamma_sig (FStar_List.map FStar_Pervasives_Native.snd))
in (FStar_All.pipe_right uu____24140 FStar_List.rev))
end
| uu____24165 -> begin
m.FStar_Syntax_Syntax.exports
end))
in ((add_sigelts env sigs);
(

let uu___1853_24168 = env
in {solver = uu___1853_24168.solver; range = uu___1853_24168.range; curmodule = empty_lid; gamma = []; gamma_sig = []; gamma_cache = uu___1853_24168.gamma_cache; modules = (m)::env.modules; expected_typ = uu___1853_24168.expected_typ; sigtab = uu___1853_24168.sigtab; attrtab = uu___1853_24168.attrtab; instantiate_imp = uu___1853_24168.instantiate_imp; effects = uu___1853_24168.effects; generalize = uu___1853_24168.generalize; letrecs = uu___1853_24168.letrecs; top_level = uu___1853_24168.top_level; check_uvars = uu___1853_24168.check_uvars; use_eq = uu___1853_24168.use_eq; is_iface = uu___1853_24168.is_iface; admit = uu___1853_24168.admit; lax = uu___1853_24168.lax; lax_universes = uu___1853_24168.lax_universes; phase1 = uu___1853_24168.phase1; failhard = uu___1853_24168.failhard; nosynth = uu___1853_24168.nosynth; uvar_subtyping = uu___1853_24168.uvar_subtyping; tc_term = uu___1853_24168.tc_term; type_of = uu___1853_24168.type_of; universe_of = uu___1853_24168.universe_of; check_type_of = uu___1853_24168.check_type_of; use_bv_sorts = uu___1853_24168.use_bv_sorts; qtbl_name_and_index = uu___1853_24168.qtbl_name_and_index; normalized_eff_names = uu___1853_24168.normalized_eff_names; fv_delta_depths = uu___1853_24168.fv_delta_depths; proof_ns = uu___1853_24168.proof_ns; synth_hook = uu___1853_24168.synth_hook; splice = uu___1853_24168.splice; mpreprocess = uu___1853_24168.mpreprocess; postprocess = uu___1853_24168.postprocess; is_native_tactic = uu___1853_24168.is_native_tactic; identifier_info = uu___1853_24168.identifier_info; tc_hooks = uu___1853_24168.tc_hooks; dsenv = uu___1853_24168.dsenv; nbe = uu___1853_24168.nbe; strict_args_tab = uu___1853_24168.strict_args_tab; erasable_types_tab = uu___1853_24168.erasable_types_tab});
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
| (FStar_Syntax_Syntax.Binding_univ (uu____24220))::tl1 -> begin
(aux out tl1)
end
| (FStar_Syntax_Syntax.Binding_lid (uu____24224, (uu____24225, t)))::tl1 -> begin
(

let uu____24246 = (

let uu____24249 = (FStar_Syntax_Free.uvars t)
in (ext out uu____24249))
in (aux uu____24246 tl1))
end
| (FStar_Syntax_Syntax.Binding_var ({FStar_Syntax_Syntax.ppname = uu____24252; FStar_Syntax_Syntax.index = uu____24253; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____24261 = (

let uu____24264 = (FStar_Syntax_Free.uvars t)
in (ext out uu____24264))
in (aux uu____24261 tl1))
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
| (FStar_Syntax_Syntax.Binding_univ (uu____24322))::tl1 -> begin
(aux out tl1)
end
| (FStar_Syntax_Syntax.Binding_lid (uu____24326, (uu____24327, t)))::tl1 -> begin
(

let uu____24348 = (

let uu____24351 = (FStar_Syntax_Free.univs t)
in (ext out uu____24351))
in (aux uu____24348 tl1))
end
| (FStar_Syntax_Syntax.Binding_var ({FStar_Syntax_Syntax.ppname = uu____24354; FStar_Syntax_Syntax.index = uu____24355; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____24363 = (

let uu____24366 = (FStar_Syntax_Free.univs t)
in (ext out uu____24366))
in (aux uu____24363 tl1))
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
| (FStar_Syntax_Syntax.Binding_univ (uname))::tl1 -> begin
(

let uu____24428 = (FStar_Util.set_add uname out)
in (aux uu____24428 tl1))
end
| (FStar_Syntax_Syntax.Binding_lid (uu____24431, (uu____24432, t)))::tl1 -> begin
(

let uu____24453 = (

let uu____24456 = (FStar_Syntax_Free.univnames t)
in (ext out uu____24456))
in (aux uu____24453 tl1))
end
| (FStar_Syntax_Syntax.Binding_var ({FStar_Syntax_Syntax.ppname = uu____24459; FStar_Syntax_Syntax.index = uu____24460; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____24468 = (

let uu____24471 = (FStar_Syntax_Free.univnames t)
in (ext out uu____24471))
in (aux uu____24468 tl1))
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : FStar_Syntax_Syntax.binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu___12_24492 -> (match (uu___12_24492) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Binding_lid (uu____24496) -> begin
[]
end
| FStar_Syntax_Syntax.Binding_univ (uu____24509) -> begin
[]
end)))))


let binders_of_bindings : FStar_Syntax_Syntax.binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____24520 = (

let uu____24529 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right uu____24529 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right uu____24520 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let print_gamma : FStar_Syntax_Syntax.gamma  ->  Prims.string = (fun gamma -> (

let uu____24577 = (FStar_All.pipe_right gamma (FStar_List.map (fun uu___13_24590 -> (match (uu___13_24590) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let uu____24593 = (FStar_Syntax_Print.bv_to_string x)
in (Prims.op_Hat "Binding_var " uu____24593))
end
| FStar_Syntax_Syntax.Binding_univ (u) -> begin
(Prims.op_Hat "Binding_univ " u.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.Binding_lid (l, uu____24599) -> begin
(

let uu____24616 = (FStar_Ident.string_of_lid l)
in (Prims.op_Hat "Binding_lid " uu____24616))
end))))
in (FStar_All.pipe_right uu____24577 (FStar_String.concat "::\n"))))


let string_of_delta_level : delta_level  ->  Prims.string = (fun uu___14_24630 -> (match (uu___14_24630) with
| NoDelta -> begin
"NoDelta"
end
| InliningDelta -> begin
"Inlining"
end
| Eager_unfolding_only -> begin
"Eager_unfolding_only"
end
| Unfold (d) -> begin
(

let uu____24636 = (FStar_Syntax_Print.delta_depth_to_string d)
in (Prims.op_Hat "Unfold " uu____24636))
end))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig)
in (FStar_Util.smap_fold (sigtab env) (fun uu____24659 v1 keys1 -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)) keys)))


let should_enc_path : env  ->  Prims.string Prims.list  ->  Prims.bool = (fun env path -> (

let rec str_i_prefix = (fun xs ys -> (match (((xs), (ys))) with
| ([], uu____24714) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((Prims.op_Equality (FStar_String.lowercase x) (FStar_String.lowercase y)) && (str_i_prefix xs1 ys1))
end
| (uu____24747, uu____24748) -> begin
false
end))
in (

let uu____24762 = (FStar_List.tryFind (fun uu____24784 -> (match (uu____24784) with
| (p, uu____24795) -> begin
(str_i_prefix p path)
end)) env.proof_ns)
in (match (uu____24762) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____24814, b) -> begin
b
end))))


let should_enc_lid : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____24844 = (FStar_Ident.path_of_lid lid)
in (should_enc_path env uu____24844)))


let cons_proof_ns : Prims.bool  ->  env  ->  name_prefix  ->  env = (fun b e path -> (

let uu___1996_24866 = e
in {solver = uu___1996_24866.solver; range = uu___1996_24866.range; curmodule = uu___1996_24866.curmodule; gamma = uu___1996_24866.gamma; gamma_sig = uu___1996_24866.gamma_sig; gamma_cache = uu___1996_24866.gamma_cache; modules = uu___1996_24866.modules; expected_typ = uu___1996_24866.expected_typ; sigtab = uu___1996_24866.sigtab; attrtab = uu___1996_24866.attrtab; instantiate_imp = uu___1996_24866.instantiate_imp; effects = uu___1996_24866.effects; generalize = uu___1996_24866.generalize; letrecs = uu___1996_24866.letrecs; top_level = uu___1996_24866.top_level; check_uvars = uu___1996_24866.check_uvars; use_eq = uu___1996_24866.use_eq; is_iface = uu___1996_24866.is_iface; admit = uu___1996_24866.admit; lax = uu___1996_24866.lax; lax_universes = uu___1996_24866.lax_universes; phase1 = uu___1996_24866.phase1; failhard = uu___1996_24866.failhard; nosynth = uu___1996_24866.nosynth; uvar_subtyping = uu___1996_24866.uvar_subtyping; tc_term = uu___1996_24866.tc_term; type_of = uu___1996_24866.type_of; universe_of = uu___1996_24866.universe_of; check_type_of = uu___1996_24866.check_type_of; use_bv_sorts = uu___1996_24866.use_bv_sorts; qtbl_name_and_index = uu___1996_24866.qtbl_name_and_index; normalized_eff_names = uu___1996_24866.normalized_eff_names; fv_delta_depths = uu___1996_24866.fv_delta_depths; proof_ns = (((path), (b)))::e.proof_ns; synth_hook = uu___1996_24866.synth_hook; splice = uu___1996_24866.splice; mpreprocess = uu___1996_24866.mpreprocess; postprocess = uu___1996_24866.postprocess; is_native_tactic = uu___1996_24866.is_native_tactic; identifier_info = uu___1996_24866.identifier_info; tc_hooks = uu___1996_24866.tc_hooks; dsenv = uu___1996_24866.dsenv; nbe = uu___1996_24866.nbe; strict_args_tab = uu___1996_24866.strict_args_tab; erasable_types_tab = uu___1996_24866.erasable_types_tab}))


let add_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns true e path))


let rem_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns false e path))


let get_proof_ns : env  ->  proof_namespace = (fun e -> e.proof_ns)


let set_proof_ns : proof_namespace  ->  env  ->  env = (fun ns e -> (

let uu___2005_24914 = e
in {solver = uu___2005_24914.solver; range = uu___2005_24914.range; curmodule = uu___2005_24914.curmodule; gamma = uu___2005_24914.gamma; gamma_sig = uu___2005_24914.gamma_sig; gamma_cache = uu___2005_24914.gamma_cache; modules = uu___2005_24914.modules; expected_typ = uu___2005_24914.expected_typ; sigtab = uu___2005_24914.sigtab; attrtab = uu___2005_24914.attrtab; instantiate_imp = uu___2005_24914.instantiate_imp; effects = uu___2005_24914.effects; generalize = uu___2005_24914.generalize; letrecs = uu___2005_24914.letrecs; top_level = uu___2005_24914.top_level; check_uvars = uu___2005_24914.check_uvars; use_eq = uu___2005_24914.use_eq; is_iface = uu___2005_24914.is_iface; admit = uu___2005_24914.admit; lax = uu___2005_24914.lax; lax_universes = uu___2005_24914.lax_universes; phase1 = uu___2005_24914.phase1; failhard = uu___2005_24914.failhard; nosynth = uu___2005_24914.nosynth; uvar_subtyping = uu___2005_24914.uvar_subtyping; tc_term = uu___2005_24914.tc_term; type_of = uu___2005_24914.type_of; universe_of = uu___2005_24914.universe_of; check_type_of = uu___2005_24914.check_type_of; use_bv_sorts = uu___2005_24914.use_bv_sorts; qtbl_name_and_index = uu___2005_24914.qtbl_name_and_index; normalized_eff_names = uu___2005_24914.normalized_eff_names; fv_delta_depths = uu___2005_24914.fv_delta_depths; proof_ns = ns; synth_hook = uu___2005_24914.synth_hook; splice = uu___2005_24914.splice; mpreprocess = uu___2005_24914.mpreprocess; postprocess = uu___2005_24914.postprocess; is_native_tactic = uu___2005_24914.is_native_tactic; identifier_info = uu___2005_24914.identifier_info; tc_hooks = uu___2005_24914.tc_hooks; dsenv = uu___2005_24914.dsenv; nbe = uu___2005_24914.nbe; strict_args_tab = uu___2005_24914.strict_args_tab; erasable_types_tab = uu___2005_24914.erasable_types_tab}))


let unbound_vars : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun e t -> (

let uu____24930 = (FStar_Syntax_Free.names t)
in (

let uu____24933 = (bound_vars e)
in (FStar_List.fold_left (fun s bv -> (FStar_Util.set_remove bv s)) uu____24930 uu____24933))))


let closed : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e t -> (

let uu____24956 = (unbound_vars e t)
in (FStar_Util.set_is_empty uu____24956)))


let closed' : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____24966 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_is_empty uu____24966)))


let string_of_proof_ns : env  ->  Prims.string = (fun env -> (

let aux = (fun uu____24987 -> (match (uu____24987) with
| (p, b) -> begin
(match (((Prims.op_Equality p []) && b)) with
| true -> begin
"*"
end
| uu____25005 -> begin
(

let uu____25007 = (FStar_Ident.text_of_path p)
in (Prims.op_Hat (match (b) with
| true -> begin
"+"
end
| uu____25012 -> begin
"-"
end) uu____25007))
end)
end))
in (

let uu____25015 = (

let uu____25019 = (FStar_List.map aux env.proof_ns)
in (FStar_All.pipe_right uu____25019 FStar_List.rev))
in (FStar_All.pipe_right uu____25015 (FStar_String.concat " ")))))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  guard_t = (fun g -> {FStar_TypeChecker_Common.guard_f = g; FStar_TypeChecker_Common.deferred = []; FStar_TypeChecker_Common.univ_ineqs = (([]), ([])); FStar_TypeChecker_Common.implicits = []})


let guard_form : guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Common.guard_f)


let is_trivial : guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Common.deferred = []; FStar_TypeChecker_Common.univ_ineqs = ([], []); FStar_TypeChecker_Common.implicits = i} -> begin
(FStar_All.pipe_right i (FStar_Util.for_all (fun imp -> ((Prims.op_Equality imp.FStar_TypeChecker_Common.imp_uvar.FStar_Syntax_Syntax.ctx_uvar_should_check FStar_Syntax_Syntax.Allow_unresolved) || (

let uu____25087 = (FStar_Syntax_Unionfind.find imp.FStar_TypeChecker_Common.imp_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____25087) with
| FStar_Pervasives_Native.Some (uu____25091) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end))))))
end
| uu____25094 -> begin
false
end))


let is_trivial_guard_formula : guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Common.deferred = uu____25104; FStar_TypeChecker_Common.univ_ineqs = uu____25105; FStar_TypeChecker_Common.implicits = uu____25106} -> begin
true
end
| uu____25116 -> begin
false
end))


let trivial_guard : guard_t = FStar_TypeChecker_Common.trivial_guard


let abstract_guard_n : FStar_Syntax_Syntax.binder Prims.list  ->  guard_t  ->  guard_t = (fun bs g -> (match (g.FStar_TypeChecker_Common.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let f' = (FStar_Syntax_Util.abs bs f (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in (

let uu___2049_25138 = g
in {FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.NonTrivial (f'); FStar_TypeChecker_Common.deferred = uu___2049_25138.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = uu___2049_25138.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu___2049_25138.FStar_TypeChecker_Common.implicits}))
end))


let abstract_guard : FStar_Syntax_Syntax.binder  ->  guard_t  ->  guard_t = (fun b g -> (abstract_guard_n ((b)::[]) g))


let def_check_vars_in_set : FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.term  ->  unit = (fun rng msg vset t -> (

let uu____25177 = (FStar_Options.defensive ())
in (match (uu____25177) with
| true -> begin
(

let s = (FStar_Syntax_Free.names t)
in (

let uu____25183 = (

let uu____25185 = (

let uu____25187 = (FStar_Util.set_difference s vset)
in (FStar_All.pipe_left FStar_Util.set_is_empty uu____25187))
in (not (uu____25185)))
in (match (uu____25183) with
| true -> begin
(

let uu____25194 = (

let uu____25200 = (

let uu____25202 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____25204 = (

let uu____25206 = (FStar_Util.set_elements s)
in (FStar_All.pipe_right uu____25206 (FStar_Syntax_Print.bvs_to_string ",\n\t")))
in (FStar_Util.format3 "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n" msg uu____25202 uu____25204)))
in ((FStar_Errors.Warning_Defensive), (uu____25200)))
in (FStar_Errors.log_issue rng uu____25194))
end
| uu____25215 -> begin
()
end)))
end
| uu____25217 -> begin
()
end)))


let def_check_closed_in : FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  unit = (fun rng msg l t -> (

let uu____25246 = (

let uu____25248 = (FStar_Options.defensive ())
in (not (uu____25248)))
in (match (uu____25246) with
| true -> begin
()
end
| uu____25251 -> begin
(

let uu____25253 = (FStar_Util.as_set l FStar_Syntax_Syntax.order_bv)
in (def_check_vars_in_set rng msg uu____25253 t))
end)))


let def_check_closed_in_env : FStar_Range.range  ->  Prims.string  ->  env  ->  FStar_Syntax_Syntax.term  ->  unit = (fun rng msg e t -> (

let uu____25279 = (

let uu____25281 = (FStar_Options.defensive ())
in (not (uu____25281)))
in (match (uu____25279) with
| true -> begin
()
end
| uu____25284 -> begin
(

let uu____25286 = (bound_vars e)
in (def_check_closed_in rng msg uu____25286 t))
end)))


let def_check_guard_wf : FStar_Range.range  ->  Prims.string  ->  env  ->  guard_t  ->  unit = (fun rng msg env g -> (match (g.FStar_TypeChecker_Common.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(def_check_closed_in_env rng msg env f)
end))


let apply_guard : guard_t  ->  FStar_Syntax_Syntax.term  ->  guard_t = (fun g e -> (match (g.FStar_TypeChecker_Common.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___2086_25325 = g
in (

let uu____25326 = (

let uu____25327 = (

let uu____25328 = (

let uu____25335 = (

let uu____25336 = (

let uu____25353 = (

let uu____25364 = (FStar_Syntax_Syntax.as_arg e)
in (uu____25364)::[])
in ((f), (uu____25353)))
in FStar_Syntax_Syntax.Tm_app (uu____25336))
in (FStar_Syntax_Syntax.mk uu____25335))
in (uu____25328 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _25401 -> FStar_TypeChecker_Common.NonTrivial (_25401)) uu____25327))
in {FStar_TypeChecker_Common.guard_f = uu____25326; FStar_TypeChecker_Common.deferred = uu___2086_25325.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = uu___2086_25325.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu___2086_25325.FStar_TypeChecker_Common.implicits}))
end))


let map_guard : guard_t  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  guard_t = (fun g map1 -> (match (g.FStar_TypeChecker_Common.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___2093_25419 = g
in (

let uu____25420 = (

let uu____25421 = (map1 f)
in FStar_TypeChecker_Common.NonTrivial (uu____25421))
in {FStar_TypeChecker_Common.guard_f = uu____25420; FStar_TypeChecker_Common.deferred = uu___2093_25419.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = uu___2093_25419.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu___2093_25419.FStar_TypeChecker_Common.implicits}))
end))


let always_map_guard : guard_t  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  guard_t = (fun g map1 -> (match (g.FStar_TypeChecker_Common.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let uu___2098_25438 = g
in (

let uu____25439 = (

let uu____25440 = (map1 FStar_Syntax_Util.t_true)
in FStar_TypeChecker_Common.NonTrivial (uu____25440))
in {FStar_TypeChecker_Common.guard_f = uu____25439; FStar_TypeChecker_Common.deferred = uu___2098_25438.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = uu___2098_25438.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu___2098_25438.FStar_TypeChecker_Common.implicits}))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___2102_25442 = g
in (

let uu____25443 = (

let uu____25444 = (map1 f)
in FStar_TypeChecker_Common.NonTrivial (uu____25444))
in {FStar_TypeChecker_Common.guard_f = uu____25443; FStar_TypeChecker_Common.deferred = uu___2102_25442.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = uu___2102_25442.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu___2102_25442.FStar_TypeChecker_Common.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____25451) -> begin
(failwith "impossible")
end))


let check_trivial : FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (FStar_TypeChecker_Common.check_trivial t))


let conj_guard : guard_t  ->  guard_t  ->  guard_t = (fun g1 g2 -> (FStar_TypeChecker_Common.conj_guard g1 g2))


let conj_guards : guard_t Prims.list  ->  guard_t = (fun gs -> (FStar_TypeChecker_Common.conj_guards gs))


let imp_guard : guard_t  ->  guard_t  ->  guard_t = (fun g1 g2 -> (FStar_TypeChecker_Common.imp_guard g1 g2))


let close_guard_univs : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.binders  ->  guard_t  ->  guard_t = (fun us bs g -> (match (g.FStar_TypeChecker_Common.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let f1 = (FStar_List.fold_right2 (fun u b f1 -> (

let uu____25528 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____25528) with
| true -> begin
f1
end
| uu____25531 -> begin
(FStar_Syntax_Util.mk_forall u (FStar_Pervasives_Native.fst b) f1)
end))) us bs f)
in (

let uu___2125_25535 = g
in {FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.NonTrivial (f1); FStar_TypeChecker_Common.deferred = uu___2125_25535.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = uu___2125_25535.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu___2125_25535.FStar_TypeChecker_Common.implicits}))
end))


let close_forall : env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____25569 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____25569) with
| true -> begin
f1
end
| uu____25572 -> begin
(

let u = (env.universe_of env (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Util.mk_forall u (FStar_Pervasives_Native.fst b) f1))
end))) bs f))


let close_guard : env  ->  FStar_Syntax_Syntax.binders  ->  guard_t  ->  guard_t = (fun env binders g -> (match (g.FStar_TypeChecker_Common.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___2140_25596 = g
in (

let uu____25597 = (

let uu____25598 = (close_forall env binders f)
in FStar_TypeChecker_Common.NonTrivial (uu____25598))
in {FStar_TypeChecker_Common.guard_f = uu____25597; FStar_TypeChecker_Common.deferred = uu___2140_25596.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = uu___2140_25596.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu___2140_25596.FStar_TypeChecker_Common.implicits}))
end))


let new_implicit_var_aux : Prims.string  ->  FStar_Range.range  ->  env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.should_check_uvar  ->  (FStar_Dyn.dyn * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar * FStar_Range.range) Prims.list * guard_t) = (fun reason r env k should_check meta -> (

let uu____25656 = (FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid)
in (match (uu____25656) with
| FStar_Pervasives_Native.Some ((uu____25681)::((tm, uu____25683))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (trivial_guard)))
end
| uu____25747 -> begin
(

let binders = (all_binders env)
in (

let gamma = env.gamma
in (

let ctx_uvar = (

let uu____25765 = (FStar_Syntax_Unionfind.fresh ())
in {FStar_Syntax_Syntax.ctx_uvar_head = uu____25765; FStar_Syntax_Syntax.ctx_uvar_gamma = gamma; FStar_Syntax_Syntax.ctx_uvar_binders = binders; FStar_Syntax_Syntax.ctx_uvar_typ = k; FStar_Syntax_Syntax.ctx_uvar_reason = reason; FStar_Syntax_Syntax.ctx_uvar_should_check = should_check; FStar_Syntax_Syntax.ctx_uvar_range = r; FStar_Syntax_Syntax.ctx_uvar_meta = meta})
in ((FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r true gamma binders);
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((ctx_uvar), ((([]), (FStar_Syntax_Syntax.NoUseRange)))))) FStar_Pervasives_Native.None r)
in (

let imp = {FStar_TypeChecker_Common.imp_reason = reason; FStar_TypeChecker_Common.imp_uvar = ctx_uvar; FStar_TypeChecker_Common.imp_tm = t; FStar_TypeChecker_Common.imp_range = r}
in (

let g = (

let uu___2162_25797 = trivial_guard
in {FStar_TypeChecker_Common.guard_f = uu___2162_25797.FStar_TypeChecker_Common.guard_f; FStar_TypeChecker_Common.deferred = uu___2162_25797.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = uu___2162_25797.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = (imp)::[]})
in ((t), ((((ctx_uvar), (r)))::[]), (g)))));
))))
end)))


let uvars_for_binders : env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t  ->  (FStar_Syntax_Syntax.binder  ->  Prims.string)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term Prims.list * guard_t) = (fun env bs substs reason r -> (

let uu____25851 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____25908 b -> (match (uu____25908) with
| (substs1, uvars1, g) -> begin
(

let sort = (FStar_Syntax_Subst.subst substs1 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (

let uu____25950 = (

let uu____25963 = (reason b)
in (new_implicit_var_aux uu____25963 r env sort FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None))
in (match (uu____25950) with
| (t, uu____25980, g_t) -> begin
(

let uu____25994 = (

let uu____25997 = (

let uu____26000 = (

let uu____26001 = (

let uu____26008 = (FStar_All.pipe_right b FStar_Pervasives_Native.fst)
in ((uu____26008), (t)))
in FStar_Syntax_Syntax.NT (uu____26001))
in (uu____26000)::[])
in (FStar_List.append substs1 uu____25997))
in (

let uu____26019 = (conj_guard g g_t)
in ((uu____25994), ((FStar_List.append uvars1 ((t)::[]))), (uu____26019))))
end)))
end)) ((substs), ([]), (trivial_guard))))
in (FStar_All.pipe_right uu____25851 (fun uu____26048 -> (match (uu____26048) with
| (uu____26065, uvars1, g) -> begin
((uvars1), (g))
end)))))


let dummy_solver : solver_t = {init = (fun uu____26081 -> ()); push = (fun uu____26083 -> ()); pop = (fun uu____26086 -> ()); snapshot = (fun uu____26089 -> (((((Prims.parse_int "0")), ((Prims.parse_int "0")), ((Prims.parse_int "0")))), (()))); rollback = (fun uu____26108 uu____26109 -> ()); encode_sig = (fun uu____26124 uu____26125 -> ()); preprocess = (fun e g -> (

let uu____26131 = (

let uu____26138 = (FStar_Options.peek ())
in ((e), (g), (uu____26138)))
in (uu____26131)::[])); solve = (fun uu____26154 uu____26155 uu____26156 -> ()); finish = (fun uu____26163 -> ()); refresh = (fun uu____26165 -> ())}





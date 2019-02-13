
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
| uu____40 -> begin
false
end))


let uu___is_Iota : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iota -> begin
true
end
| uu____51 -> begin
false
end))


let uu___is_Zeta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Zeta -> begin
true
end
| uu____62 -> begin
false
end))


let uu___is_Exclude : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exclude (_0) -> begin
true
end
| uu____74 -> begin
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
| uu____93 -> begin
false
end))


let uu___is_HNF : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HNF -> begin
true
end
| uu____104 -> begin
false
end))


let uu___is_Primops : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____115 -> begin
false
end))


let uu___is_Eager_unfolding : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding -> begin
true
end
| uu____126 -> begin
false
end))


let uu___is_Inlining : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____137 -> begin
false
end))


let uu___is_DoNotUnfoldPureLets : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DoNotUnfoldPureLets -> begin
true
end
| uu____148 -> begin
false
end))


let uu___is_UnfoldUntil : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
true
end
| uu____160 -> begin
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
| uu____182 -> begin
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
| uu____210 -> begin
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
| uu____238 -> begin
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
| uu____263 -> begin
false
end))


let uu___is_PureSubtermsWithinComputations : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PureSubtermsWithinComputations -> begin
true
end
| uu____274 -> begin
false
end))


let uu___is_Simplify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simplify -> begin
true
end
| uu____285 -> begin
false
end))


let uu___is_EraseUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EraseUniverses -> begin
true
end
| uu____296 -> begin
false
end))


let uu___is_AllowUnboundUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AllowUnboundUniverses -> begin
true
end
| uu____307 -> begin
false
end))


let uu___is_Reify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____318 -> begin
false
end))


let uu___is_CompressUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CompressUvars -> begin
true
end
| uu____329 -> begin
false
end))


let uu___is_NoFullNorm : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoFullNorm -> begin
true
end
| uu____340 -> begin
false
end))


let uu___is_CheckNoUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckNoUvars -> begin
true
end
| uu____351 -> begin
false
end))


let uu___is_Unmeta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unmeta -> begin
true
end
| uu____362 -> begin
false
end))


let uu___is_Unascribe : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unascribe -> begin
true
end
| uu____373 -> begin
false
end))


let uu___is_NBE : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NBE -> begin
true
end
| uu____384 -> begin
false
end))


let uu___is_ForExtraction : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ForExtraction -> begin
true
end
| uu____395 -> begin
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
| uu____455 -> begin
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
| uu____481 -> begin
false
end))


let uu___is_InliningDelta : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InliningDelta -> begin
true
end
| uu____492 -> begin
false
end))


let uu___is_Eager_unfolding_only : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding_only -> begin
true
end
| uu____503 -> begin
false
end))


let uu___is_Unfold : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unfold (_0) -> begin
true
end
| uu____515 -> begin
false
end))


let __proj__Unfold__item___0 : delta_level  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| Unfold (_0) -> begin
_0
end))

type mlift =
{mlift_wp : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ; mlift_term : (FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option}


let __proj__Mkmlift__item__mlift_wp : mlift  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| {mlift_wp = mlift_wp; mlift_term = mlift_term} -> begin
mlift_wp
end))


let __proj__Mkmlift__item__mlift_term : mlift  ->  (FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {mlift_wp = mlift_wp; mlift_term = mlift_term} -> begin
mlift_term
end))

type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : mlift}


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

type effects =
{decls : (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}


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


type name_prefix =
Prims.string Prims.list


type proof_namespace =
(name_prefix * Prims.bool) Prims.list


type cached_elt =
(((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option)) FStar_Util.either * FStar_Range.range)


type goal =
FStar_Syntax_Syntax.term

type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : FStar_Syntax_Syntax.binding Prims.list; gamma_sig : sig_binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; attrtab : FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.univ_names) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; lax : Prims.bool; lax_universes : Prims.bool; phase1 : Prims.bool; failhard : Prims.bool; nosynth : Prims.bool; uvar_subtyping : Prims.bool; tc_term : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t); type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; check_type_of : Prims.bool  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  guard_t; use_bv_sorts : Prims.bool; qtbl_name_and_index : (Prims.int FStar_Util.smap * (FStar_Ident.lident * Prims.int) FStar_Pervasives_Native.option); normalized_eff_names : FStar_Ident.lident FStar_Util.smap; fv_delta_depths : FStar_Syntax_Syntax.delta_depth FStar_Util.smap; proof_ns : proof_namespace; synth_hook : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term; splice : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list; postprocess : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term; is_native_tactic : FStar_Ident.lid  ->  Prims.bool; identifier_info : FStar_TypeChecker_Common.id_info_table FStar_ST.ref; tc_hooks : tcenv_hooks; dsenv : FStar_Syntax_DsEnv.env; nbe : step Prims.list  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term} 
 and solver_t =
{init : env  ->  unit; push : Prims.string  ->  unit; pop : Prims.string  ->  unit; snapshot : Prims.string  ->  ((Prims.int * Prims.int * Prims.int) * unit); rollback : Prims.string  ->  (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  unit; preprocess : env  ->  goal  ->  (env * goal * FStar_Options.optionstate) Prims.list; solve : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  unit; finish : unit  ->  unit; refresh : unit  ->  unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : (FStar_Syntax_Syntax.universe Prims.list * FStar_TypeChecker_Common.univ_ineq Prims.list); implicits : implicit Prims.list} 
 and implicit =
{imp_reason : Prims.string; imp_uvar : FStar_Syntax_Syntax.ctx_uvar; imp_tm : FStar_Syntax_Syntax.term; imp_range : FStar_Range.range} 
 and tcenv_hooks =
{tc_push_in_gamma_hook : env  ->  (FStar_Syntax_Syntax.binding, sig_binding) FStar_Util.either  ->  unit}


let __proj__Mkenv__item__solver : env  ->  solver_t = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
solver
end))


let __proj__Mkenv__item__range : env  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
range
end))


let __proj__Mkenv__item__curmodule : env  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
curmodule
end))


let __proj__Mkenv__item__gamma : env  ->  FStar_Syntax_Syntax.binding Prims.list = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
gamma
end))


let __proj__Mkenv__item__gamma_sig : env  ->  sig_binding Prims.list = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
gamma_sig
end))


let __proj__Mkenv__item__gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
gamma_cache
end))


let __proj__Mkenv__item__modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
modules
end))


let __proj__Mkenv__item__expected_typ : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
expected_typ
end))


let __proj__Mkenv__item__sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
sigtab
end))


let __proj__Mkenv__item__attrtab : env  ->  FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
attrtab
end))


let __proj__Mkenv__item__is_pattern : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
is_pattern
end))


let __proj__Mkenv__item__instantiate_imp : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
instantiate_imp
end))


let __proj__Mkenv__item__effects : env  ->  effects = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
effects
end))


let __proj__Mkenv__item__generalize : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
generalize
end))


let __proj__Mkenv__item__letrecs : env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.univ_names) Prims.list = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
letrecs
end))


let __proj__Mkenv__item__top_level : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
top_level
end))


let __proj__Mkenv__item__check_uvars : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
check_uvars
end))


let __proj__Mkenv__item__use_eq : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
use_eq
end))


let __proj__Mkenv__item__is_iface : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
is_iface
end))


let __proj__Mkenv__item__admit : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
admit1
end))


let __proj__Mkenv__item__lax : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
lax1
end))


let __proj__Mkenv__item__lax_universes : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
lax_universes
end))


let __proj__Mkenv__item__phase1 : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
phase1
end))


let __proj__Mkenv__item__failhard : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
failhard
end))


let __proj__Mkenv__item__nosynth : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
nosynth
end))


let __proj__Mkenv__item__uvar_subtyping : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
uvar_subtyping
end))


let __proj__Mkenv__item__tc_term : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t) = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
tc_term
end))


let __proj__Mkenv__item__type_of : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t) = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
type_of
end))


let __proj__Mkenv__item__universe_of : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
universe_of
end))


let __proj__Mkenv__item__check_type_of : env  ->  Prims.bool  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  guard_t = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
check_type_of
end))


let __proj__Mkenv__item__use_bv_sorts : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
use_bv_sorts
end))


let __proj__Mkenv__item__qtbl_name_and_index : env  ->  (Prims.int FStar_Util.smap * (FStar_Ident.lident * Prims.int) FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
qtbl_name_and_index
end))


let __proj__Mkenv__item__normalized_eff_names : env  ->  FStar_Ident.lident FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
normalized_eff_names
end))


let __proj__Mkenv__item__fv_delta_depths : env  ->  FStar_Syntax_Syntax.delta_depth FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
fv_delta_depths
end))


let __proj__Mkenv__item__proof_ns : env  ->  proof_namespace = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
proof_ns
end))


let __proj__Mkenv__item__synth_hook : env  ->  env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
synth_hook
end))


let __proj__Mkenv__item__splice : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
splice1
end))


let __proj__Mkenv__item__postprocess : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
postprocess
end))


let __proj__Mkenv__item__is_native_tactic : env  ->  FStar_Ident.lid  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
is_native_tactic
end))


let __proj__Mkenv__item__identifier_info : env  ->  FStar_TypeChecker_Common.id_info_table FStar_ST.ref = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
identifier_info
end))


let __proj__Mkenv__item__tc_hooks : env  ->  tcenv_hooks = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
tc_hooks
end))


let __proj__Mkenv__item__dsenv : env  ->  FStar_Syntax_DsEnv.env = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
dsenv
end))


let __proj__Mkenv__item__nbe : env  ->  step Prims.list  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {solver = solver; range = range; curmodule = curmodule; gamma = gamma; gamma_sig = gamma_sig; gamma_cache = gamma_cache; modules = modules; expected_typ = expected_typ; sigtab = sigtab; attrtab = attrtab; is_pattern = is_pattern; instantiate_imp = instantiate_imp; effects = effects; generalize = generalize; letrecs = letrecs; top_level = top_level; check_uvars = check_uvars; use_eq = use_eq; is_iface = is_iface; admit = admit1; lax = lax1; lax_universes = lax_universes; phase1 = phase1; failhard = failhard; nosynth = nosynth; uvar_subtyping = uvar_subtyping; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = use_bv_sorts; qtbl_name_and_index = qtbl_name_and_index; normalized_eff_names = normalized_eff_names; fv_delta_depths = fv_delta_depths; proof_ns = proof_ns; synth_hook = synth_hook; splice = splice1; postprocess = postprocess; is_native_tactic = is_native_tactic; identifier_info = identifier_info; tc_hooks = tc_hooks; dsenv = dsenv; nbe = nbe1} -> begin
nbe1
end))


let __proj__Mksolver_t__item__init : solver_t  ->  env  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_modul = encode_modul; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
init1
end))


let __proj__Mksolver_t__item__push : solver_t  ->  Prims.string  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_modul = encode_modul; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
push1
end))


let __proj__Mksolver_t__item__pop : solver_t  ->  Prims.string  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_modul = encode_modul; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
pop1
end))


let __proj__Mksolver_t__item__snapshot : solver_t  ->  Prims.string  ->  ((Prims.int * Prims.int * Prims.int) * unit) = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_modul = encode_modul; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
snapshot1
end))


let __proj__Mksolver_t__item__rollback : solver_t  ->  Prims.string  ->  (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_modul = encode_modul; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
rollback1
end))


let __proj__Mksolver_t__item__encode_modul : solver_t  ->  env  ->  FStar_Syntax_Syntax.modul  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_modul = encode_modul; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
encode_modul
end))


let __proj__Mksolver_t__item__encode_sig : solver_t  ->  env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_modul = encode_modul; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
encode_sig
end))


let __proj__Mksolver_t__item__preprocess : solver_t  ->  env  ->  goal  ->  (env * goal * FStar_Options.optionstate) Prims.list = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_modul = encode_modul; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
preprocess
end))


let __proj__Mksolver_t__item__solve : solver_t  ->  (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_modul = encode_modul; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
solve
end))


let __proj__Mksolver_t__item__finish : solver_t  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_modul = encode_modul; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
finish1
end))


let __proj__Mksolver_t__item__refresh : solver_t  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {init = init1; push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; encode_modul = encode_modul; encode_sig = encode_sig; preprocess = preprocess; solve = solve; finish = finish1; refresh = refresh} -> begin
refresh
end))


let __proj__Mkguard_t__item__guard_f : guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun projectee -> (match (projectee) with
| {guard_f = guard_f; deferred = deferred; univ_ineqs = univ_ineqs; implicits = implicits} -> begin
guard_f
end))


let __proj__Mkguard_t__item__deferred : guard_t  ->  FStar_TypeChecker_Common.deferred = (fun projectee -> (match (projectee) with
| {guard_f = guard_f; deferred = deferred; univ_ineqs = univ_ineqs; implicits = implicits} -> begin
deferred
end))


let __proj__Mkguard_t__item__univ_ineqs : guard_t  ->  (FStar_Syntax_Syntax.universe Prims.list * FStar_TypeChecker_Common.univ_ineq Prims.list) = (fun projectee -> (match (projectee) with
| {guard_f = guard_f; deferred = deferred; univ_ineqs = univ_ineqs; implicits = implicits} -> begin
univ_ineqs
end))


let __proj__Mkguard_t__item__implicits : guard_t  ->  implicit Prims.list = (fun projectee -> (match (projectee) with
| {guard_f = guard_f; deferred = deferred; univ_ineqs = univ_ineqs; implicits = implicits} -> begin
implicits
end))


let __proj__Mkimplicit__item__imp_reason : implicit  ->  Prims.string = (fun projectee -> (match (projectee) with
| {imp_reason = imp_reason; imp_uvar = imp_uvar; imp_tm = imp_tm; imp_range = imp_range} -> begin
imp_reason
end))


let __proj__Mkimplicit__item__imp_uvar : implicit  ->  FStar_Syntax_Syntax.ctx_uvar = (fun projectee -> (match (projectee) with
| {imp_reason = imp_reason; imp_uvar = imp_uvar; imp_tm = imp_tm; imp_range = imp_range} -> begin
imp_uvar
end))


let __proj__Mkimplicit__item__imp_tm : implicit  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {imp_reason = imp_reason; imp_uvar = imp_uvar; imp_tm = imp_tm; imp_range = imp_range} -> begin
imp_tm
end))


let __proj__Mkimplicit__item__imp_range : implicit  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {imp_reason = imp_reason; imp_uvar = imp_uvar; imp_tm = imp_tm; imp_range = imp_range} -> begin
imp_range
end))


let __proj__Mktcenv_hooks__item__tc_push_in_gamma_hook : tcenv_hooks  ->  env  ->  (FStar_Syntax_Syntax.binding, sig_binding) FStar_Util.either  ->  unit = (fun projectee -> (match (projectee) with
| {tc_push_in_gamma_hook = tc_push_in_gamma_hook} -> begin
tc_push_in_gamma_hook
end))


type solver_depth_t =
(Prims.int * Prims.int * Prims.int)


type implicits =
implicit Prims.list


let postprocess : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env tau ty tm -> (env.postprocess env tau ty tm))


let rename_gamma : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.gamma  ->  FStar_Syntax_Syntax.gamma = (fun subst1 gamma -> (FStar_All.pipe_right gamma (FStar_List.map (fun uu___234_11986 -> (match (uu___234_11986) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let y = (

let uu____11989 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Subst.subst subst1 uu____11989))
in (

let uu____11990 = (

let uu____11991 = (FStar_Syntax_Subst.compress y)
in uu____11991.FStar_Syntax_Syntax.n)
in (match (uu____11990) with
| FStar_Syntax_Syntax.Tm_name (y1) -> begin
(

let uu____11995 = (

let uu___248_11996 = y1
in (

let uu____11997 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___248_11996.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___248_11996.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____11997}))
in FStar_Syntax_Syntax.Binding_var (uu____11995))
end
| uu____12000 -> begin
(failwith "Not a renaming")
end)))
end
| b -> begin
b
end)))))


let rename_env : FStar_Syntax_Syntax.subst_t  ->  env  ->  env = (fun subst1 env -> (

let uu___249_12014 = env
in (

let uu____12015 = (rename_gamma subst1 env.gamma)
in {solver = uu___249_12014.solver; range = uu___249_12014.range; curmodule = uu___249_12014.curmodule; gamma = uu____12015; gamma_sig = uu___249_12014.gamma_sig; gamma_cache = uu___249_12014.gamma_cache; modules = uu___249_12014.modules; expected_typ = uu___249_12014.expected_typ; sigtab = uu___249_12014.sigtab; attrtab = uu___249_12014.attrtab; is_pattern = uu___249_12014.is_pattern; instantiate_imp = uu___249_12014.instantiate_imp; effects = uu___249_12014.effects; generalize = uu___249_12014.generalize; letrecs = uu___249_12014.letrecs; top_level = uu___249_12014.top_level; check_uvars = uu___249_12014.check_uvars; use_eq = uu___249_12014.use_eq; is_iface = uu___249_12014.is_iface; admit = uu___249_12014.admit; lax = uu___249_12014.lax; lax_universes = uu___249_12014.lax_universes; phase1 = uu___249_12014.phase1; failhard = uu___249_12014.failhard; nosynth = uu___249_12014.nosynth; uvar_subtyping = uu___249_12014.uvar_subtyping; tc_term = uu___249_12014.tc_term; type_of = uu___249_12014.type_of; universe_of = uu___249_12014.universe_of; check_type_of = uu___249_12014.check_type_of; use_bv_sorts = uu___249_12014.use_bv_sorts; qtbl_name_and_index = uu___249_12014.qtbl_name_and_index; normalized_eff_names = uu___249_12014.normalized_eff_names; fv_delta_depths = uu___249_12014.fv_delta_depths; proof_ns = uu___249_12014.proof_ns; synth_hook = uu___249_12014.synth_hook; splice = uu___249_12014.splice; postprocess = uu___249_12014.postprocess; is_native_tactic = uu___249_12014.is_native_tactic; identifier_info = uu___249_12014.identifier_info; tc_hooks = uu___249_12014.tc_hooks; dsenv = uu___249_12014.dsenv; nbe = uu___249_12014.nbe})))


let default_tc_hooks : tcenv_hooks = {tc_push_in_gamma_hook = (fun uu____12023 uu____12024 -> ())}


let tc_hooks : env  ->  tcenv_hooks = (fun env -> env.tc_hooks)


let set_tc_hooks : env  ->  tcenv_hooks  ->  env = (fun env hooks -> (

let uu___250_12046 = env
in {solver = uu___250_12046.solver; range = uu___250_12046.range; curmodule = uu___250_12046.curmodule; gamma = uu___250_12046.gamma; gamma_sig = uu___250_12046.gamma_sig; gamma_cache = uu___250_12046.gamma_cache; modules = uu___250_12046.modules; expected_typ = uu___250_12046.expected_typ; sigtab = uu___250_12046.sigtab; attrtab = uu___250_12046.attrtab; is_pattern = uu___250_12046.is_pattern; instantiate_imp = uu___250_12046.instantiate_imp; effects = uu___250_12046.effects; generalize = uu___250_12046.generalize; letrecs = uu___250_12046.letrecs; top_level = uu___250_12046.top_level; check_uvars = uu___250_12046.check_uvars; use_eq = uu___250_12046.use_eq; is_iface = uu___250_12046.is_iface; admit = uu___250_12046.admit; lax = uu___250_12046.lax; lax_universes = uu___250_12046.lax_universes; phase1 = uu___250_12046.phase1; failhard = uu___250_12046.failhard; nosynth = uu___250_12046.nosynth; uvar_subtyping = uu___250_12046.uvar_subtyping; tc_term = uu___250_12046.tc_term; type_of = uu___250_12046.type_of; universe_of = uu___250_12046.universe_of; check_type_of = uu___250_12046.check_type_of; use_bv_sorts = uu___250_12046.use_bv_sorts; qtbl_name_and_index = uu___250_12046.qtbl_name_and_index; normalized_eff_names = uu___250_12046.normalized_eff_names; fv_delta_depths = uu___250_12046.fv_delta_depths; proof_ns = uu___250_12046.proof_ns; synth_hook = uu___250_12046.synth_hook; splice = uu___250_12046.splice; postprocess = uu___250_12046.postprocess; is_native_tactic = uu___250_12046.is_native_tactic; identifier_info = uu___250_12046.identifier_info; tc_hooks = hooks; dsenv = uu___250_12046.dsenv; nbe = uu___250_12046.nbe}))


let set_dep_graph : env  ->  FStar_Parser_Dep.deps  ->  env = (fun e g -> (

let uu___251_12058 = e
in (

let uu____12059 = (FStar_Syntax_DsEnv.set_dep_graph e.dsenv g)
in {solver = uu___251_12058.solver; range = uu___251_12058.range; curmodule = uu___251_12058.curmodule; gamma = uu___251_12058.gamma; gamma_sig = uu___251_12058.gamma_sig; gamma_cache = uu___251_12058.gamma_cache; modules = uu___251_12058.modules; expected_typ = uu___251_12058.expected_typ; sigtab = uu___251_12058.sigtab; attrtab = uu___251_12058.attrtab; is_pattern = uu___251_12058.is_pattern; instantiate_imp = uu___251_12058.instantiate_imp; effects = uu___251_12058.effects; generalize = uu___251_12058.generalize; letrecs = uu___251_12058.letrecs; top_level = uu___251_12058.top_level; check_uvars = uu___251_12058.check_uvars; use_eq = uu___251_12058.use_eq; is_iface = uu___251_12058.is_iface; admit = uu___251_12058.admit; lax = uu___251_12058.lax; lax_universes = uu___251_12058.lax_universes; phase1 = uu___251_12058.phase1; failhard = uu___251_12058.failhard; nosynth = uu___251_12058.nosynth; uvar_subtyping = uu___251_12058.uvar_subtyping; tc_term = uu___251_12058.tc_term; type_of = uu___251_12058.type_of; universe_of = uu___251_12058.universe_of; check_type_of = uu___251_12058.check_type_of; use_bv_sorts = uu___251_12058.use_bv_sorts; qtbl_name_and_index = uu___251_12058.qtbl_name_and_index; normalized_eff_names = uu___251_12058.normalized_eff_names; fv_delta_depths = uu___251_12058.fv_delta_depths; proof_ns = uu___251_12058.proof_ns; synth_hook = uu___251_12058.synth_hook; splice = uu___251_12058.splice; postprocess = uu___251_12058.postprocess; is_native_tactic = uu___251_12058.is_native_tactic; identifier_info = uu___251_12058.identifier_info; tc_hooks = uu___251_12058.tc_hooks; dsenv = uu____12059; nbe = uu___251_12058.nbe})))


let dep_graph : env  ->  FStar_Parser_Dep.deps = (fun e -> (FStar_Syntax_DsEnv.dep_graph e.dsenv))


type env_t =
env


type sigtable =
FStar_Syntax_Syntax.sigelt FStar_Util.smap


let should_verify : env  ->  Prims.bool = (fun env -> (((not (env.lax)) && (not (env.admit))) && (FStar_Options.should_verify env.curmodule.FStar_Ident.str)))


let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match (((d), (q))) with
| (NoDelta, uu____12088) -> begin
true
end
| (Eager_unfolding_only, FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____12091), FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____12093), FStar_Syntax_Syntax.Visible_default) -> begin
true
end
| (InliningDelta, FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| uu____12096 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab : 'Auu____12110 . unit  ->  'Auu____12110 FStar_Util.smap = (fun uu____12117 -> (FStar_Util.smap_create default_table_size))


let new_gamma_cache : 'Auu____12123 . unit  ->  'Auu____12123 FStar_Util.smap = (fun uu____12130 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let initial_env : FStar_Parser_Dep.deps  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  (Prims.bool  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  guard_t)  ->  solver_t  ->  FStar_Ident.lident  ->  (step Prims.list  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  env = (fun deps tc_term type_of universe_of check_type_of solver module_lid nbe1 -> (

let uu____12268 = (new_gamma_cache ())
in (

let uu____12271 = (new_sigtab ())
in (

let uu____12274 = (new_sigtab ())
in (

let uu____12281 = (

let uu____12296 = (FStar_Util.smap_create (Prims.parse_int "10"))
in ((uu____12296), (FStar_Pervasives_Native.None)))
in (

let uu____12317 = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let uu____12321 = (FStar_Util.smap_create (Prims.parse_int "50"))
in (

let uu____12325 = (FStar_Options.using_facts_from ())
in (

let uu____12326 = (FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty)
in (

let uu____12329 = (FStar_Syntax_DsEnv.empty_env deps)
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_sig = []; gamma_cache = uu____12268; modules = []; expected_typ = FStar_Pervasives_Native.None; sigtab = uu____12271; attrtab = uu____12274; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; phase1 = false; failhard = false; nosynth = false; uvar_subtyping = true; tc_term = tc_term; type_of = type_of; universe_of = universe_of; check_type_of = check_type_of; use_bv_sorts = false; qtbl_name_and_index = uu____12281; normalized_eff_names = uu____12317; fv_delta_depths = uu____12321; proof_ns = uu____12325; synth_hook = (fun e g tau -> (failwith "no synthesizer available")); splice = (fun e tau -> (failwith "no splicer available")); postprocess = (fun e tau typ tm -> (failwith "no postprocessor available")); is_native_tactic = (fun uu____12391 -> false); identifier_info = uu____12326; tc_hooks = default_tc_hooks; dsenv = uu____12329; nbe = nbe1}))))))))))


let dsenv : env  ->  FStar_Syntax_DsEnv.env = (fun env -> env.dsenv)


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let attrtab : env  ->  FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap = (fun env -> env.attrtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


let query_indices : (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let push_query_indices : unit  ->  unit = (fun uu____12503 -> (

let uu____12504 = (FStar_ST.op_Bang query_indices)
in (match (uu____12504) with
| [] -> begin
(failwith "Empty query indices!")
end
| uu____12559 -> begin
(

let uu____12569 = (

let uu____12579 = (

let uu____12587 = (FStar_ST.op_Bang query_indices)
in (FStar_List.hd uu____12587))
in (

let uu____12641 = (FStar_ST.op_Bang query_indices)
in (uu____12579)::uu____12641))
in (FStar_ST.op_Colon_Equals query_indices uu____12569))
end)))


let pop_query_indices : unit  ->  unit = (fun uu____12737 -> (

let uu____12738 = (FStar_ST.op_Bang query_indices)
in (match (uu____12738) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals query_indices tl1)
end)))


let snapshot_query_indices : unit  ->  (Prims.int * unit) = (fun uu____12865 -> (FStar_Common.snapshot push_query_indices query_indices ()))


let rollback_query_indices : Prims.int FStar_Pervasives_Native.option  ->  unit = (fun depth -> (FStar_Common.rollback pop_query_indices query_indices depth))


let add_query_index : (FStar_Ident.lident * Prims.int)  ->  unit = (fun uu____12902 -> (match (uu____12902) with
| (l, n1) -> begin
(

let uu____12912 = (FStar_ST.op_Bang query_indices)
in (match (uu____12912) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals query_indices (((((l), (n1)))::hd1)::tl1))
end
| uu____13034 -> begin
(failwith "Empty query indices")
end))
end))


let peek_query_indices : unit  ->  (FStar_Ident.lident * Prims.int) Prims.list = (fun uu____13057 -> (

let uu____13058 = (FStar_ST.op_Bang query_indices)
in (FStar_List.hd uu____13058)))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push_stack : env  ->  env = (fun env -> ((

let uu____13137 = (

let uu____13140 = (FStar_ST.op_Bang stack)
in (env)::uu____13140)
in (FStar_ST.op_Colon_Equals stack uu____13137));
(

let uu___252_13189 = env
in (

let uu____13190 = (FStar_Util.smap_copy (gamma_cache env))
in (

let uu____13193 = (FStar_Util.smap_copy (sigtab env))
in (

let uu____13196 = (FStar_Util.smap_copy (attrtab env))
in (

let uu____13203 = (

let uu____13218 = (

let uu____13222 = (FStar_All.pipe_right env.qtbl_name_and_index FStar_Pervasives_Native.fst)
in (FStar_Util.smap_copy uu____13222))
in (

let uu____13254 = (FStar_All.pipe_right env.qtbl_name_and_index FStar_Pervasives_Native.snd)
in ((uu____13218), (uu____13254))))
in (

let uu____13303 = (FStar_Util.smap_copy env.normalized_eff_names)
in (

let uu____13306 = (FStar_Util.smap_copy env.fv_delta_depths)
in (

let uu____13309 = (

let uu____13312 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_Util.mk_ref uu____13312))
in {solver = uu___252_13189.solver; range = uu___252_13189.range; curmodule = uu___252_13189.curmodule; gamma = uu___252_13189.gamma; gamma_sig = uu___252_13189.gamma_sig; gamma_cache = uu____13190; modules = uu___252_13189.modules; expected_typ = uu___252_13189.expected_typ; sigtab = uu____13193; attrtab = uu____13196; is_pattern = uu___252_13189.is_pattern; instantiate_imp = uu___252_13189.instantiate_imp; effects = uu___252_13189.effects; generalize = uu___252_13189.generalize; letrecs = uu___252_13189.letrecs; top_level = uu___252_13189.top_level; check_uvars = uu___252_13189.check_uvars; use_eq = uu___252_13189.use_eq; is_iface = uu___252_13189.is_iface; admit = uu___252_13189.admit; lax = uu___252_13189.lax; lax_universes = uu___252_13189.lax_universes; phase1 = uu___252_13189.phase1; failhard = uu___252_13189.failhard; nosynth = uu___252_13189.nosynth; uvar_subtyping = uu___252_13189.uvar_subtyping; tc_term = uu___252_13189.tc_term; type_of = uu___252_13189.type_of; universe_of = uu___252_13189.universe_of; check_type_of = uu___252_13189.check_type_of; use_bv_sorts = uu___252_13189.use_bv_sorts; qtbl_name_and_index = uu____13203; normalized_eff_names = uu____13303; fv_delta_depths = uu____13306; proof_ns = uu___252_13189.proof_ns; synth_hook = uu___252_13189.synth_hook; splice = uu___252_13189.splice; postprocess = uu___252_13189.postprocess; is_native_tactic = uu___252_13189.is_native_tactic; identifier_info = uu____13309; tc_hooks = uu___252_13189.tc_hooks; dsenv = uu___252_13189.dsenv; nbe = uu___252_13189.nbe}))))))));
))


let pop_stack : unit  ->  env = (fun uu____13359 -> (

let uu____13360 = (FStar_ST.op_Bang stack)
in (match (uu____13360) with
| (env)::tl1 -> begin
((FStar_ST.op_Colon_Equals stack tl1);
env;
)
end
| uu____13414 -> begin
(failwith "Impossible: Too many pops")
end)))


let snapshot_stack : env  ->  (Prims.int * env) = (fun env -> (FStar_Common.snapshot push_stack stack env))


let rollback_stack : Prims.int FStar_Pervasives_Native.option  ->  env = (fun depth -> (FStar_Common.rollback pop_stack stack depth))


type tcenv_depth_t =
(Prims.int * Prims.int * solver_depth_t * Prims.int)


let snapshot : env  ->  Prims.string  ->  (tcenv_depth_t * env) = (fun env msg -> (FStar_Util.atomically (fun uu____13504 -> (

let uu____13505 = (snapshot_stack env)
in (match (uu____13505) with
| (stack_depth, env1) -> begin
(

let uu____13539 = (snapshot_query_indices ())
in (match (uu____13539) with
| (query_indices_depth, ()) -> begin
(

let uu____13572 = (env1.solver.snapshot msg)
in (match (uu____13572) with
| (solver_depth, ()) -> begin
(

let uu____13629 = (FStar_Syntax_DsEnv.snapshot env1.dsenv)
in (match (uu____13629) with
| (dsenv_depth, dsenv1) -> begin
((((stack_depth), (query_indices_depth), (solver_depth), (dsenv_depth))), ((

let uu___253_13696 = env1
in {solver = uu___253_13696.solver; range = uu___253_13696.range; curmodule = uu___253_13696.curmodule; gamma = uu___253_13696.gamma; gamma_sig = uu___253_13696.gamma_sig; gamma_cache = uu___253_13696.gamma_cache; modules = uu___253_13696.modules; expected_typ = uu___253_13696.expected_typ; sigtab = uu___253_13696.sigtab; attrtab = uu___253_13696.attrtab; is_pattern = uu___253_13696.is_pattern; instantiate_imp = uu___253_13696.instantiate_imp; effects = uu___253_13696.effects; generalize = uu___253_13696.generalize; letrecs = uu___253_13696.letrecs; top_level = uu___253_13696.top_level; check_uvars = uu___253_13696.check_uvars; use_eq = uu___253_13696.use_eq; is_iface = uu___253_13696.is_iface; admit = uu___253_13696.admit; lax = uu___253_13696.lax; lax_universes = uu___253_13696.lax_universes; phase1 = uu___253_13696.phase1; failhard = uu___253_13696.failhard; nosynth = uu___253_13696.nosynth; uvar_subtyping = uu___253_13696.uvar_subtyping; tc_term = uu___253_13696.tc_term; type_of = uu___253_13696.type_of; universe_of = uu___253_13696.universe_of; check_type_of = uu___253_13696.check_type_of; use_bv_sorts = uu___253_13696.use_bv_sorts; qtbl_name_and_index = uu___253_13696.qtbl_name_and_index; normalized_eff_names = uu___253_13696.normalized_eff_names; fv_delta_depths = uu___253_13696.fv_delta_depths; proof_ns = uu___253_13696.proof_ns; synth_hook = uu___253_13696.synth_hook; splice = uu___253_13696.splice; postprocess = uu___253_13696.postprocess; is_native_tactic = uu___253_13696.is_native_tactic; identifier_info = uu___253_13696.identifier_info; tc_hooks = uu___253_13696.tc_hooks; dsenv = dsenv1; nbe = uu___253_13696.nbe})))
end))
end))
end))
end)))))


let rollback : solver_t  ->  Prims.string  ->  tcenv_depth_t FStar_Pervasives_Native.option  ->  env = (fun solver msg depth -> (FStar_Util.atomically (fun uu____13730 -> (

let uu____13731 = (match (depth) with
| FStar_Pervasives_Native.Some (s1, s2, s3, s4) -> begin
((FStar_Pervasives_Native.Some (s1)), (FStar_Pervasives_Native.Some (s2)), (FStar_Pervasives_Native.Some (s3)), (FStar_Pervasives_Native.Some (s4)))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
in (match (uu____13731) with
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

let uu____13911 = (FStar_Util.physical_equality tcenv.dsenv dsenv1)
in (FStar_Common.runtime_assert uu____13911 "Inconsistent stack state"));
tcenv;
)))
end);
)
end);
)
end)))))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let uu____13927 = (snapshot env msg)
in (FStar_Pervasives_Native.snd uu____13927)))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (rollback env.solver msg FStar_Pervasives_Native.None))


let incr_query_index : env  ->  env = (fun env -> (

let qix = (peek_query_indices ())
in (match (env.qtbl_name_and_index) with
| (uu____13959, FStar_Pervasives_Native.None) -> begin
env
end
| (tbl, FStar_Pervasives_Native.Some (l, n1)) -> begin
(

let uu____14001 = (FStar_All.pipe_right qix (FStar_List.tryFind (fun uu____14031 -> (match (uu____14031) with
| (m, uu____14039) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____14001) with
| FStar_Pervasives_Native.None -> begin
(

let next = (n1 + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(FStar_Util.smap_add tbl l.FStar_Ident.str next);
(

let uu___254_14054 = env
in {solver = uu___254_14054.solver; range = uu___254_14054.range; curmodule = uu___254_14054.curmodule; gamma = uu___254_14054.gamma; gamma_sig = uu___254_14054.gamma_sig; gamma_cache = uu___254_14054.gamma_cache; modules = uu___254_14054.modules; expected_typ = uu___254_14054.expected_typ; sigtab = uu___254_14054.sigtab; attrtab = uu___254_14054.attrtab; is_pattern = uu___254_14054.is_pattern; instantiate_imp = uu___254_14054.instantiate_imp; effects = uu___254_14054.effects; generalize = uu___254_14054.generalize; letrecs = uu___254_14054.letrecs; top_level = uu___254_14054.top_level; check_uvars = uu___254_14054.check_uvars; use_eq = uu___254_14054.use_eq; is_iface = uu___254_14054.is_iface; admit = uu___254_14054.admit; lax = uu___254_14054.lax; lax_universes = uu___254_14054.lax_universes; phase1 = uu___254_14054.phase1; failhard = uu___254_14054.failhard; nosynth = uu___254_14054.nosynth; uvar_subtyping = uu___254_14054.uvar_subtyping; tc_term = uu___254_14054.tc_term; type_of = uu___254_14054.type_of; universe_of = uu___254_14054.universe_of; check_type_of = uu___254_14054.check_type_of; use_bv_sorts = uu___254_14054.use_bv_sorts; qtbl_name_and_index = ((tbl), (FStar_Pervasives_Native.Some (((l), (next))))); normalized_eff_names = uu___254_14054.normalized_eff_names; fv_delta_depths = uu___254_14054.fv_delta_depths; proof_ns = uu___254_14054.proof_ns; synth_hook = uu___254_14054.synth_hook; splice = uu___254_14054.splice; postprocess = uu___254_14054.postprocess; is_native_tactic = uu___254_14054.is_native_tactic; identifier_info = uu___254_14054.identifier_info; tc_hooks = uu___254_14054.tc_hooks; dsenv = uu___254_14054.dsenv; nbe = uu___254_14054.nbe});
))
end
| FStar_Pervasives_Native.Some (uu____14071, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(FStar_Util.smap_add tbl l.FStar_Ident.str next);
(

let uu___255_14087 = env
in {solver = uu___255_14087.solver; range = uu___255_14087.range; curmodule = uu___255_14087.curmodule; gamma = uu___255_14087.gamma; gamma_sig = uu___255_14087.gamma_sig; gamma_cache = uu___255_14087.gamma_cache; modules = uu___255_14087.modules; expected_typ = uu___255_14087.expected_typ; sigtab = uu___255_14087.sigtab; attrtab = uu___255_14087.attrtab; is_pattern = uu___255_14087.is_pattern; instantiate_imp = uu___255_14087.instantiate_imp; effects = uu___255_14087.effects; generalize = uu___255_14087.generalize; letrecs = uu___255_14087.letrecs; top_level = uu___255_14087.top_level; check_uvars = uu___255_14087.check_uvars; use_eq = uu___255_14087.use_eq; is_iface = uu___255_14087.is_iface; admit = uu___255_14087.admit; lax = uu___255_14087.lax; lax_universes = uu___255_14087.lax_universes; phase1 = uu___255_14087.phase1; failhard = uu___255_14087.failhard; nosynth = uu___255_14087.nosynth; uvar_subtyping = uu___255_14087.uvar_subtyping; tc_term = uu___255_14087.tc_term; type_of = uu___255_14087.type_of; universe_of = uu___255_14087.universe_of; check_type_of = uu___255_14087.check_type_of; use_bv_sorts = uu___255_14087.use_bv_sorts; qtbl_name_and_index = ((tbl), (FStar_Pervasives_Native.Some (((l), (next))))); normalized_eff_names = uu___255_14087.normalized_eff_names; fv_delta_depths = uu___255_14087.fv_delta_depths; proof_ns = uu___255_14087.proof_ns; synth_hook = uu___255_14087.synth_hook; splice = uu___255_14087.splice; postprocess = uu___255_14087.postprocess; is_native_tactic = uu___255_14087.is_native_tactic; identifier_info = uu___255_14087.identifier_info; tc_hooks = uu___255_14087.tc_hooks; dsenv = uu___255_14087.dsenv; nbe = uu___255_14087.nbe});
))
end))
end)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> (match ((Prims.op_Equality r FStar_Range.dummyRange)) with
| true -> begin
e
end
| uu____14128 -> begin
(

let uu___256_14130 = e
in {solver = uu___256_14130.solver; range = r; curmodule = uu___256_14130.curmodule; gamma = uu___256_14130.gamma; gamma_sig = uu___256_14130.gamma_sig; gamma_cache = uu___256_14130.gamma_cache; modules = uu___256_14130.modules; expected_typ = uu___256_14130.expected_typ; sigtab = uu___256_14130.sigtab; attrtab = uu___256_14130.attrtab; is_pattern = uu___256_14130.is_pattern; instantiate_imp = uu___256_14130.instantiate_imp; effects = uu___256_14130.effects; generalize = uu___256_14130.generalize; letrecs = uu___256_14130.letrecs; top_level = uu___256_14130.top_level; check_uvars = uu___256_14130.check_uvars; use_eq = uu___256_14130.use_eq; is_iface = uu___256_14130.is_iface; admit = uu___256_14130.admit; lax = uu___256_14130.lax; lax_universes = uu___256_14130.lax_universes; phase1 = uu___256_14130.phase1; failhard = uu___256_14130.failhard; nosynth = uu___256_14130.nosynth; uvar_subtyping = uu___256_14130.uvar_subtyping; tc_term = uu___256_14130.tc_term; type_of = uu___256_14130.type_of; universe_of = uu___256_14130.universe_of; check_type_of = uu___256_14130.check_type_of; use_bv_sorts = uu___256_14130.use_bv_sorts; qtbl_name_and_index = uu___256_14130.qtbl_name_and_index; normalized_eff_names = uu___256_14130.normalized_eff_names; fv_delta_depths = uu___256_14130.fv_delta_depths; proof_ns = uu___256_14130.proof_ns; synth_hook = uu___256_14130.synth_hook; splice = uu___256_14130.splice; postprocess = uu___256_14130.postprocess; is_native_tactic = uu___256_14130.is_native_tactic; identifier_info = uu___256_14130.identifier_info; tc_hooks = uu___256_14130.tc_hooks; dsenv = uu___256_14130.dsenv; nbe = uu___256_14130.nbe})
end))


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let toggle_id_info : env  ->  Prims.bool  ->  unit = (fun env enabled -> (

let uu____14150 = (

let uu____14151 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_toggle uu____14151 enabled))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____14150)))


let insert_bv_info : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun env bv ty -> (

let uu____14206 = (

let uu____14207 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_insert_bv uu____14207 bv ty))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____14206)))


let insert_fv_info : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun env fv ty -> (

let uu____14262 = (

let uu____14263 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_insert_fv uu____14263 fv ty))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____14262)))


let promote_id_info : env  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  unit = (fun env ty_map -> (

let uu____14318 = (

let uu____14319 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_promote uu____14319 ty_map))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____14318)))


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let uu___257_14383 = env
in {solver = uu___257_14383.solver; range = uu___257_14383.range; curmodule = lid; gamma = uu___257_14383.gamma; gamma_sig = uu___257_14383.gamma_sig; gamma_cache = uu___257_14383.gamma_cache; modules = uu___257_14383.modules; expected_typ = uu___257_14383.expected_typ; sigtab = uu___257_14383.sigtab; attrtab = uu___257_14383.attrtab; is_pattern = uu___257_14383.is_pattern; instantiate_imp = uu___257_14383.instantiate_imp; effects = uu___257_14383.effects; generalize = uu___257_14383.generalize; letrecs = uu___257_14383.letrecs; top_level = uu___257_14383.top_level; check_uvars = uu___257_14383.check_uvars; use_eq = uu___257_14383.use_eq; is_iface = uu___257_14383.is_iface; admit = uu___257_14383.admit; lax = uu___257_14383.lax; lax_universes = uu___257_14383.lax_universes; phase1 = uu___257_14383.phase1; failhard = uu___257_14383.failhard; nosynth = uu___257_14383.nosynth; uvar_subtyping = uu___257_14383.uvar_subtyping; tc_term = uu___257_14383.tc_term; type_of = uu___257_14383.type_of; universe_of = uu___257_14383.universe_of; check_type_of = uu___257_14383.check_type_of; use_bv_sorts = uu___257_14383.use_bv_sorts; qtbl_name_and_index = uu___257_14383.qtbl_name_and_index; normalized_eff_names = uu___257_14383.normalized_eff_names; fv_delta_depths = uu___257_14383.fv_delta_depths; proof_ns = uu___257_14383.proof_ns; synth_hook = uu___257_14383.synth_hook; splice = uu___257_14383.splice; postprocess = uu___257_14383.postprocess; is_native_tactic = uu___257_14383.is_native_tactic; identifier_info = uu___257_14383.identifier_info; tc_hooks = uu___257_14383.tc_hooks; dsenv = uu___257_14383.dsenv; nbe = uu___257_14383.nbe}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun env lid -> (

let uu____14414 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.smap_try_find (sigtab env) uu____14414)))


let name_not_found : FStar_Ident.lid  ->  (FStar_Errors.raw_error * Prims.string) = (fun l -> (

let uu____14427 = (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_NameNotFound), (uu____14427))))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  (FStar_Errors.raw_error * Prims.string) = (fun v1 -> (

let uu____14442 = (

let uu____14444 = (FStar_Syntax_Print.bv_to_string v1)
in (FStar_Util.format1 "Variable \"%s\" not found" uu____14444))
in ((FStar_Errors.Fatal_VariableNotFound), (uu____14442))))


let new_u_univ : unit  ->  FStar_Syntax_Syntax.universe = (fun uu____14453 -> (

let uu____14454 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____14454)))


let mk_univ_subst : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun formals us -> (

let n1 = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n1 - i)), (u))))))))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), uu____14554) -> begin
(

let vs = (mk_univ_subst formals us)
in (

let uu____14578 = (FStar_Syntax_Subst.subst vs t)
in ((us), (uu____14578))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun uu___235_14595 -> (match (uu___235_14595) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun uu____14621 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let uu____14641 = (inst_tscheme t)
in (match (uu____14641) with
| (us, t1) -> begin
(

let uu____14652 = (FStar_Syntax_Subst.set_use_range r t1)
in ((us), (uu____14652)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed uu____14673 -> (match (uu____14673) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs1 = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in ((match ((Prims.op_disEquality (FStar_List.length insts) (FStar_List.length univs1))) with
| true -> begin
(

let uu____14695 = (

let uu____14697 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (

let uu____14701 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (

let uu____14705 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____14707 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" uu____14697 uu____14701 uu____14705 uu____14707)))))
in (failwith uu____14695))
end
| uu____14710 -> begin
()
end);
(

let uu____14712 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (FStar_Pervasives_Native.snd uu____14712));
))
end
| uu____14721 -> begin
(

let uu____14722 = (

let uu____14724 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" uu____14724))
in (failwith uu____14722))
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
| uu____14736 -> begin
false
end))


let uu___is_No : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____14747 -> begin
false
end))


let uu___is_Maybe : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____14758 -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in (match ((Prims.op_Equality l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
Yes
end
| uu____14774 -> begin
(match ((FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur1 = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l1 -> (match (((c), (l1))) with
| ([], uu____14806) -> begin
Maybe
end
| (uu____14813, []) -> begin
No
end
| ((hd1)::tl1, (hd')::tl') when (Prims.op_Equality hd1.FStar_Ident.idText hd'.FStar_Ident.idText) -> begin
(aux tl1 tl')
end
| uu____14833 -> begin
No
end))
in (aux cur1 lns))))
end
| uu____14842 -> begin
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

let uu____14927 = (FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)
in (match (uu____14927) with
| FStar_Pervasives_Native.None -> begin
(

let uu____14950 = (FStar_Util.find_map env.gamma (fun uu___236_14994 -> (match (uu___236_14994) with
| FStar_Syntax_Syntax.Binding_lid (l, t) -> begin
(

let uu____15033 = (FStar_Ident.lid_equals lid l)
in (match (uu____15033) with
| true -> begin
(

let uu____15056 = (

let uu____15075 = (

let uu____15090 = (inst_tscheme t)
in FStar_Util.Inl (uu____15090))
in (

let uu____15105 = (FStar_Ident.range_of_lid l)
in ((uu____15075), (uu____15105))))
in FStar_Pervasives_Native.Some (uu____15056))
end
| uu____15138 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____15158 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_Util.catch_opt uu____14950 (fun uu____15196 -> (FStar_Util.find_map env.gamma_sig (fun uu___237_15205 -> (match (uu___237_15205) with
| (uu____15208, {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (ses, uu____15210); FStar_Syntax_Syntax.sigrng = uu____15211; FStar_Syntax_Syntax.sigquals = uu____15212; FStar_Syntax_Syntax.sigmeta = uu____15213; FStar_Syntax_Syntax.sigattrs = uu____15214}) -> begin
(FStar_Util.find_map ses (fun se -> (

let uu____15234 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____15234) with
| true -> begin
(cache ((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| uu____15268 -> begin
FStar_Pervasives_Native.None
end))))
end
| (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____15286) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____15293 -> begin
(cache t)
end))
in (

let uu____15294 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____15294) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____15300 = (

let uu____15301 = (FStar_Ident.range_of_lid l)
in ((FStar_Util.Inr (((s), (FStar_Pervasives_Native.None)))), (uu____15301)))
in (maybe_cache uu____15300))
end)))
end))))))
end
| se -> begin
se
end))
end
| uu____15331 -> begin
FStar_Pervasives_Native.None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| uu____15370 -> begin
(

let uu____15372 = (find_in_sigtab env lid)
in (match (uu____15372) with
| FStar_Pervasives_Native.Some (se) -> begin
FStar_Pervasives_Native.Some (((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end)))))


let lookup_sigelt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun env lid -> (

let uu____15453 = (lookup_qname env lid)
in (match (uu____15453) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (uu____15474), rng) -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, us), rng) -> begin
FStar_Pervasives_Native.Some (se)
end)))


let lookup_attr : env  ->  Prims.string  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env attr -> (

let uu____15588 = (FStar_Util.smap_try_find (attrtab env) attr)
in (match (uu____15588) with
| FStar_Pervasives_Native.Some (ses) -> begin
ses
end
| FStar_Pervasives_Native.None -> begin
[]
end)))


let add_se_to_attrtab : env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun env se -> (

let add_one1 = (fun env1 se1 attr -> (

let uu____15633 = (

let uu____15636 = (lookup_attr env1 attr)
in (se1)::uu____15636)
in (FStar_Util.smap_add (attrtab env1) attr uu____15633)))
in (FStar_List.iter (fun attr -> (

let uu____15646 = (

let uu____15647 = (FStar_Syntax_Subst.compress attr)
in uu____15647.FStar_Syntax_Syntax.n)
in (match (uu____15646) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____15651 = (

let uu____15653 = (FStar_Syntax_Syntax.lid_of_fv fv)
in uu____15653.FStar_Ident.str)
in (add_one1 env se uu____15651))
end
| uu____15654 -> begin
()
end))) se.FStar_Syntax_Syntax.sigattrs)))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____15677) -> begin
(add_sigelts env ses)
end
| uu____15686 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids);
(add_se_to_attrtab env se);
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| uu____15701 -> begin
()
end);
))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) FStar_Pervasives_Native.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun uu___238_15733 -> (match (uu___238_15733) with
| FStar_Syntax_Syntax.Binding_var (id1) when (FStar_Syntax_Syntax.bv_eq id1 bv) -> begin
FStar_Pervasives_Native.Some (((id1.FStar_Syntax_Syntax.sort), (id1.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
end
| uu____15751 -> begin
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
| FStar_Syntax_Syntax.Sig_let ((uu____15813, (lb)::[]), uu____15815) -> begin
(

let uu____15824 = (

let uu____15833 = (inst_tscheme1 ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____15842 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in ((uu____15833), (uu____15842))))
in FStar_Pervasives_Native.Some (uu____15824))
end
| FStar_Syntax_Syntax.Sig_let ((uu____15855, lbs), uu____15857) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____15889) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
(

let uu____15902 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____15902) with
| true -> begin
(

let uu____15915 = (

let uu____15924 = (inst_tscheme1 ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____15933 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____15924), (uu____15933))))
in FStar_Pervasives_Native.Some (uu____15915))
end
| uu____15946 -> begin
FStar_Pervasives_Native.None
end))
end)))
end
| uu____15956 -> begin
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

let uu____16016 = (

let uu____16025 = (

let uu____16030 = (

let uu____16031 = (

let uu____16034 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders uu____16034))
in ((ne.FStar_Syntax_Syntax.univs), (uu____16031)))
in (inst_tscheme1 uu____16030))
in ((uu____16025), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____16016))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, uu____16056, uu____16057) -> begin
(

let uu____16062 = (

let uu____16071 = (

let uu____16076 = (

let uu____16077 = (

let uu____16080 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders uu____16080))
in ((us), (uu____16077)))
in (inst_tscheme1 uu____16076))
in ((uu____16071), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____16062))
end
| uu____16099 -> begin
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

let mapper = (fun uu____16188 -> (match (uu____16188) with
| (lr, rng) -> begin
(match (lr) with
| FStar_Util.Inl (t) -> begin
FStar_Pervasives_Native.Some (((t), (rng)))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____16284, uvs, t, uu____16287, uu____16288, uu____16289); FStar_Syntax_Syntax.sigrng = uu____16290; FStar_Syntax_Syntax.sigquals = uu____16291; FStar_Syntax_Syntax.sigmeta = uu____16292; FStar_Syntax_Syntax.sigattrs = uu____16293}, FStar_Pervasives_Native.None) -> begin
(

let uu____16316 = (

let uu____16325 = (inst_tscheme1 ((uvs), (t)))
in ((uu____16325), (rng)))
in FStar_Pervasives_Native.Some (uu____16316))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t); FStar_Syntax_Syntax.sigrng = uu____16349; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____16351; FStar_Syntax_Syntax.sigattrs = uu____16352}, FStar_Pervasives_Native.None) -> begin
(

let uu____16369 = (

let uu____16371 = (in_cur_mod env l)
in (Prims.op_Equality uu____16371 Yes))
in (match (uu____16369) with
| true -> begin
(

let uu____16383 = ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface)
in (match (uu____16383) with
| true -> begin
(

let uu____16399 = (

let uu____16408 = (inst_tscheme1 ((uvs), (t)))
in ((uu____16408), (rng)))
in FStar_Pervasives_Native.Some (uu____16399))
end
| uu____16429 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____16439 -> begin
(

let uu____16441 = (

let uu____16450 = (inst_tscheme1 ((uvs), (t)))
in ((uu____16450), (rng)))
in FStar_Pervasives_Native.Some (uu____16441))
end))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____16475, uu____16476); FStar_Syntax_Syntax.sigrng = uu____16477; FStar_Syntax_Syntax.sigquals = uu____16478; FStar_Syntax_Syntax.sigmeta = uu____16479; FStar_Syntax_Syntax.sigattrs = uu____16480}, FStar_Pervasives_Native.None) -> begin
(match (tps) with
| [] -> begin
(

let uu____16521 = (

let uu____16530 = (inst_tscheme1 ((uvs), (k)))
in ((uu____16530), (rng)))
in FStar_Pervasives_Native.Some (uu____16521))
end
| uu____16551 -> begin
(

let uu____16552 = (

let uu____16561 = (

let uu____16566 = (

let uu____16567 = (

let uu____16570 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____16570))
in ((uvs), (uu____16567)))
in (inst_tscheme1 uu____16566))
in ((uu____16561), (rng)))
in FStar_Pervasives_Native.Some (uu____16552))
end)
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____16593, uu____16594); FStar_Syntax_Syntax.sigrng = uu____16595; FStar_Syntax_Syntax.sigquals = uu____16596; FStar_Syntax_Syntax.sigmeta = uu____16597; FStar_Syntax_Syntax.sigattrs = uu____16598}, FStar_Pervasives_Native.Some (us)) -> begin
(match (tps) with
| [] -> begin
(

let uu____16640 = (

let uu____16649 = (inst_tscheme_with ((uvs), (k)) us)
in ((uu____16649), (rng)))
in FStar_Pervasives_Native.Some (uu____16640))
end
| uu____16670 -> begin
(

let uu____16671 = (

let uu____16680 = (

let uu____16685 = (

let uu____16686 = (

let uu____16689 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____16689))
in ((uvs), (uu____16686)))
in (inst_tscheme_with uu____16685 us))
in ((uu____16680), (rng)))
in FStar_Pervasives_Native.Some (uu____16671))
end)
end
| FStar_Util.Inr (se) -> begin
(

let uu____16725 = (match (se) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____16746); FStar_Syntax_Syntax.sigrng = uu____16747; FStar_Syntax_Syntax.sigquals = uu____16748; FStar_Syntax_Syntax.sigmeta = uu____16749; FStar_Syntax_Syntax.sigattrs = uu____16750}, FStar_Pervasives_Native.None) -> begin
(lookup_type_of_let us_opt (FStar_Pervasives_Native.fst se) lid)
end
| uu____16765 -> begin
(effect_signature us_opt (FStar_Pervasives_Native.fst se))
end)
in (FStar_All.pipe_right uu____16725 (FStar_Util.map_option (fun uu____16813 -> (match (uu____16813) with
| (us_t, rng1) -> begin
((us_t), (rng1))
end)))))
end)
end))
in (

let uu____16844 = (

let uu____16855 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____16855 mapper))
in (match (uu____16844) with
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
(

let uu____16929 = (

let uu____16940 = (

let uu____16947 = (

let uu___258_16950 = t
in (

let uu____16951 = (FStar_Ident.range_of_lid lid)
in {FStar_Syntax_Syntax.n = uu___258_16950.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = uu____16951; FStar_Syntax_Syntax.vars = uu___258_16950.FStar_Syntax_Syntax.vars}))
in ((us), (uu____16947)))
in ((uu____16940), (r)))
in FStar_Pervasives_Native.Some (uu____16929))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____17000 = (lookup_qname env l)
in (match (uu____17000) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____17021) -> begin
true
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) = (fun env bv -> (

let bvr = (FStar_Syntax_Syntax.range_of_bv bv)
in (

let uu____17075 = (try_lookup_bv env bv)
in (match (uu____17075) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17090 = (variable_not_found bv)
in (FStar_Errors.raise_error uu____17090 bvr))
end
| FStar_Pervasives_Native.Some (t, r) -> begin
(

let uu____17106 = (FStar_Syntax_Subst.set_use_range bvr t)
in (

let uu____17107 = (

let uu____17108 = (FStar_Range.use_range bvr)
in (FStar_Range.set_use_range r uu____17108))
in ((uu____17106), (uu____17107))))
end))))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) FStar_Pervasives_Native.option = (fun env l -> (

let uu____17130 = (try_lookup_lid_aux FStar_Pervasives_Native.None env l)
in (match (uu____17130) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
(

let use_range1 = (FStar_Ident.range_of_lid l)
in (

let r1 = (

let uu____17196 = (FStar_Range.use_range use_range1)
in (FStar_Range.set_use_range r uu____17196))
in (

let uu____17197 = (

let uu____17206 = (

let uu____17211 = (FStar_Syntax_Subst.set_use_range use_range1 t)
in ((us), (uu____17211)))
in ((uu____17206), (r1)))
in FStar_Pervasives_Native.Some (uu____17197))))
end)))


let try_lookup_and_inst_lid : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) FStar_Pervasives_Native.option = (fun env us l -> (

let uu____17246 = (try_lookup_lid_aux (FStar_Pervasives_Native.Some (us)) env l)
in (match (uu____17246) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((uu____17279, t), r) -> begin
(

let use_range1 = (FStar_Ident.range_of_lid l)
in (

let r1 = (

let uu____17304 = (FStar_Range.use_range use_range1)
in (FStar_Range.set_use_range r uu____17304))
in (

let uu____17305 = (

let uu____17310 = (FStar_Syntax_Subst.set_use_range use_range1 t)
in ((uu____17310), (r1)))
in FStar_Pervasives_Native.Some (uu____17305))))
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) = (fun env l -> (

let uu____17334 = (try_lookup_lid env l)
in (match (uu____17334) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17361 = (name_not_found l)
in (

let uu____17367 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____17361 uu____17367)))
end
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end)))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun uu___239_17410 -> (match (uu___239_17410) with
| FStar_Syntax_Syntax.Binding_univ (y) -> begin
(Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)
end
| uu____17414 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env lid -> (

let uu____17435 = (lookup_qname env lid)
in (match (uu____17435) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____17444, uvs, t); FStar_Syntax_Syntax.sigrng = uu____17447; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____17449; FStar_Syntax_Syntax.sigattrs = uu____17450}, FStar_Pervasives_Native.None), uu____17451) -> begin
(

let uu____17500 = (

let uu____17507 = (

let uu____17508 = (

let uu____17511 = (FStar_Ident.range_of_lid lid)
in (FStar_Syntax_Subst.set_use_range uu____17511 t))
in ((uvs), (uu____17508)))
in ((uu____17507), (q)))
in FStar_Pervasives_Native.Some (uu____17500))
end
| uu____17524 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____17546 = (lookup_qname env lid)
in (match (uu____17546) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____17551, uvs, t); FStar_Syntax_Syntax.sigrng = uu____17554; FStar_Syntax_Syntax.sigquals = uu____17555; FStar_Syntax_Syntax.sigmeta = uu____17556; FStar_Syntax_Syntax.sigattrs = uu____17557}, FStar_Pervasives_Native.None), uu____17558) -> begin
(

let uu____17607 = (FStar_Ident.range_of_lid lid)
in (inst_tscheme_with_range uu____17607 ((uvs), (t))))
end
| uu____17612 -> begin
(

let uu____17613 = (name_not_found lid)
in (

let uu____17619 = (FStar_Ident.range_of_lid lid)
in (FStar_Errors.raise_error uu____17613 uu____17619)))
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____17639 = (lookup_qname env lid)
in (match (uu____17639) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____17644, uvs, t, uu____17647, uu____17648, uu____17649); FStar_Syntax_Syntax.sigrng = uu____17650; FStar_Syntax_Syntax.sigquals = uu____17651; FStar_Syntax_Syntax.sigmeta = uu____17652; FStar_Syntax_Syntax.sigattrs = uu____17653}, FStar_Pervasives_Native.None), uu____17654) -> begin
(

let uu____17709 = (FStar_Ident.range_of_lid lid)
in (inst_tscheme_with_range uu____17709 ((uvs), (t))))
end
| uu____17714 -> begin
(

let uu____17715 = (name_not_found lid)
in (

let uu____17721 = (FStar_Ident.range_of_lid lid)
in (FStar_Errors.raise_error uu____17715 uu____17721)))
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  (Prims.bool * FStar_Ident.lident Prims.list) = (fun env lid -> (

let uu____17744 = (lookup_qname env lid)
in (match (uu____17744) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____17752, uu____17753, uu____17754, uu____17755, uu____17756, dcs); FStar_Syntax_Syntax.sigrng = uu____17758; FStar_Syntax_Syntax.sigquals = uu____17759; FStar_Syntax_Syntax.sigmeta = uu____17760; FStar_Syntax_Syntax.sigattrs = uu____17761}, uu____17762), uu____17763) -> begin
((true), (dcs))
end
| uu____17826 -> begin
((false), ([]))
end)))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____17842 = (lookup_qname env lid)
in (match (uu____17842) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____17843, uu____17844, uu____17845, l, uu____17847, uu____17848); FStar_Syntax_Syntax.sigrng = uu____17849; FStar_Syntax_Syntax.sigquals = uu____17850; FStar_Syntax_Syntax.sigmeta = uu____17851; FStar_Syntax_Syntax.sigattrs = uu____17852}, uu____17853), uu____17854) -> begin
l
end
| uu____17911 -> begin
(

let uu____17912 = (

let uu____17914 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" uu____17914))
in (failwith uu____17912))
end)))


let lookup_definition_qninfo_aux : Prims.bool  ->  delta_level Prims.list  ->  FStar_Ident.lident  ->  qninfo  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option = (fun rec_ok delta_levels lid qninfo -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____17984) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, lbs), uu____18041) when ((visible se.FStar_Syntax_Syntax.sigquals) && ((not (is_rec)) || rec_ok)) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____18065 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____18065) with
| true -> begin
FStar_Pervasives_Native.Some (((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbdef)))
end
| uu____18090 -> begin
FStar_Pervasives_Native.None
end)))))
end
| uu____18100 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____18109 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_definition_qninfo : delta_level Prims.list  ->  FStar_Ident.lident  ->  qninfo  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun delta_levels lid qninfo -> (lookup_definition_qninfo_aux true delta_levels lid qninfo))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun delta_levels env lid -> (

let uu____18171 = (lookup_qname env lid)
in (FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid) uu____18171)))


let lookup_nonrec_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun delta_levels env lid -> (

let uu____18204 = (lookup_qname env lid)
in (FStar_All.pipe_left (lookup_definition_qninfo_aux false delta_levels lid) uu____18204)))


let delta_depth_of_qninfo : FStar_Syntax_Syntax.fv  ->  qninfo  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun fv qn -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((Prims.op_Equality lid.FStar_Ident.nsstr "Prims")) with
| true -> begin
FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
end
| uu____18233 -> begin
(match (qn) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "0")))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (uu____18256), uu____18257) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "0")))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, uu____18306), uu____18307) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____18356) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.Sig_bundle (uu____18374) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____18384) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____18401) -> begin
(

let uu____18408 = (FStar_Syntax_DsEnv.delta_depth_of_declaration lid se.FStar_Syntax_Syntax.sigquals)
in FStar_Pervasives_Native.Some (uu____18408))
end
| FStar_Syntax_Syntax.Sig_let ((uu____18409, lbs), uu____18411) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv1 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____18427 = (FStar_Syntax_Syntax.fv_eq_lid fv1 lid)
in (match (uu____18427) with
| true -> begin
FStar_Pervasives_Native.Some (fv1.FStar_Syntax_Syntax.fv_delta)
end
| uu____18432 -> begin
FStar_Pervasives_Native.None
end)))))
end
| FStar_Syntax_Syntax.Sig_splice (uu____18434) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1")))
end
| FStar_Syntax_Syntax.Sig_main (uu____18442) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_assume (uu____18443) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____18450) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____18451) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____18452) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____18453) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_pragma (uu____18466) -> begin
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
| uu____18482 -> begin
(

let uu____18484 = (FStar_All.pipe_right lid.FStar_Ident.str (FStar_Util.smap_try_find env.fv_delta_depths))
in (FStar_All.pipe_right uu____18484 (fun d_opt -> (

let uu____18497 = (FStar_All.pipe_right d_opt FStar_Util.is_some)
in (match (uu____18497) with
| true -> begin
(FStar_All.pipe_right d_opt FStar_Util.must)
end
| uu____18505 -> begin
(

let uu____18507 = (

let uu____18510 = (lookup_qname env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (delta_depth_of_qninfo fv uu____18510))
in (match (uu____18507) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18511 = (

let uu____18513 = (FStar_Syntax_Print.fv_to_string fv)
in (FStar_Util.format1 "Delta depth not found for %s" uu____18513))
in (failwith uu____18511))
end
| FStar_Pervasives_Native.Some (d) -> begin
((

let uu____18518 = ((Prims.op_disEquality d fv.FStar_Syntax_Syntax.fv_delta) && (FStar_Options.debug_any ()))
in (match (uu____18518) with
| true -> begin
(

let uu____18521 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____18523 = (FStar_Syntax_Print.delta_depth_to_string fv.FStar_Syntax_Syntax.fv_delta)
in (

let uu____18525 = (FStar_Syntax_Print.delta_depth_to_string d)
in (FStar_Util.print3 "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n" uu____18521 uu____18523 uu____18525))))
end
| uu____18528 -> begin
()
end));
(FStar_Util.smap_add env.fv_delta_depths lid.FStar_Ident.str d);
d;
)
end))
end)))))
end)))


let quals_of_qninfo : qninfo  ->  FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option = (fun qninfo -> (match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, uu____18550), uu____18551) -> begin
FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
end
| uu____18600 -> begin
FStar_Pervasives_Native.None
end))


let attrs_of_qninfo : qninfo  ->  FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option = (fun qninfo -> (match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, uu____18622), uu____18623) -> begin
FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
end
| uu____18672 -> begin
FStar_Pervasives_Native.None
end))


let lookup_attrs_of_lid : env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option = (fun env lid -> (

let uu____18694 = (lookup_qname env lid)
in (FStar_All.pipe_left attrs_of_qninfo uu____18694)))


let fv_has_attr : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Ident.lid  ->  Prims.bool = (fun env fv attr_lid -> (

let uu____18717 = (lookup_attrs_of_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____18717) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some ([]) -> begin
false
end
| FStar_Pervasives_Native.Some (attrs) -> begin
(FStar_All.pipe_right attrs (FStar_Util.for_some (fun tm -> (

let uu____18741 = (

let uu____18742 = (FStar_Syntax_Util.un_uinst tm)
in uu____18742.FStar_Syntax_Syntax.n)
in (match (uu____18741) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv1 attr_lid)
end
| uu____18747 -> begin
false
end)))))
end)))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env ftv -> (

let uu____18764 = (lookup_qname env ftv)
in (match (uu____18764) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____18768) -> begin
(

let uu____18813 = (effect_signature FStar_Pervasives_Native.None se)
in (match (uu____18813) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((uu____18834, t), r) -> begin
(

let uu____18849 = (

let uu____18850 = (FStar_Ident.range_of_lid ftv)
in (FStar_Syntax_Subst.set_use_range uu____18850 t))
in FStar_Pervasives_Native.Some (uu____18849))
end))
end
| uu____18851 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (

let uu____18863 = (try_lookup_effect_lid env ftv)
in (match (uu____18863) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18866 = (name_not_found ftv)
in (

let uu____18872 = (FStar_Ident.range_of_lid ftv)
in (FStar_Errors.raise_error uu____18866 uu____18872)))
end
| FStar_Pervasives_Native.Some (k) -> begin
k
end)))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun env univ_insts lid0 -> (

let uu____18896 = (lookup_qname env lid0)
in (match (uu____18896) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs1, binders, c, uu____18907); FStar_Syntax_Syntax.sigrng = uu____18908; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____18910; FStar_Syntax_Syntax.sigattrs = uu____18911}, FStar_Pervasives_Native.None), uu____18912) -> begin
(

let lid1 = (

let uu____18966 = (

let uu____18967 = (FStar_Ident.range_of_lid lid)
in (

let uu____18968 = (

let uu____18969 = (FStar_Ident.range_of_lid lid0)
in (FStar_Range.use_range uu____18969))
in (FStar_Range.set_use_range uu____18967 uu____18968)))
in (FStar_Ident.set_lid_range lid uu____18966))
in (

let uu____18970 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___240_18976 -> (match (uu___240_18976) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____18979 -> begin
false
end))))
in (match (uu____18970) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____18992 -> begin
(

let insts = (match ((Prims.op_Equality (FStar_List.length univ_insts) (FStar_List.length univs1))) with
| true -> begin
univ_insts
end
| uu____18996 -> begin
(

let uu____18998 = (

let uu____19000 = (

let uu____19002 = (get_range env)
in (FStar_Range.string_of_range uu____19002))
in (

let uu____19003 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____19005 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format3 "(%s) Unexpected instantiation of effect %s with %s universes" uu____19000 uu____19003 uu____19005))))
in (failwith uu____18998))
end)
in (match (((binders), (univs1))) with
| ([], uu____19026) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (uu____19052, (uu____19053)::(uu____19054)::uu____19055) -> begin
(

let uu____19076 = (

let uu____19078 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____19080 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" uu____19078 uu____19080)))
in (failwith uu____19076))
end
| uu____19091 -> begin
(

let uu____19106 = (

let uu____19111 = (

let uu____19112 = (FStar_Syntax_Util.arrow binders c)
in ((univs1), (uu____19112)))
in (inst_tscheme_with uu____19111 insts))
in (match (uu____19106) with
| (uu____19125, t) -> begin
(

let t1 = (

let uu____19128 = (FStar_Ident.range_of_lid lid1)
in (FStar_Syntax_Subst.set_use_range uu____19128 t))
in (

let uu____19129 = (

let uu____19130 = (FStar_Syntax_Subst.compress t1)
in uu____19130.FStar_Syntax_Syntax.n)
in (match (uu____19129) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
FStar_Pervasives_Native.Some (((binders1), (c1)))
end
| uu____19165 -> begin
(failwith "Impossible")
end)))
end))
end))
end)))
end
| uu____19173 -> begin
FStar_Pervasives_Native.None
end)))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l -> (

let rec find1 = (fun l1 -> (

let uu____19197 = (lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l1)
in (match (uu____19197) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____19210, c) -> begin
(

let l2 = (FStar_Syntax_Util.comp_effect_name c)
in (

let uu____19217 = (find1 l2)
in (match (uu____19217) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (l2)
end
| FStar_Pervasives_Native.Some (l') -> begin
FStar_Pervasives_Native.Some (l')
end)))
end)))
in (

let res = (

let uu____19224 = (FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str)
in (match (uu____19224) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____19228 = (find1 l)
in (match (uu____19228) with
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

let uu____19233 = (FStar_Ident.range_of_lid l)
in (FStar_Ident.set_lid_range res uu____19233)))))


let lookup_effect_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env l -> (

let l1 = (norm_eff_name env l)
in (

let uu____19248 = (lookup_qname env l1)
in (match (uu____19248) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (uu____19251); FStar_Syntax_Syntax.sigrng = uu____19252; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____19254; FStar_Syntax_Syntax.sigattrs = uu____19255}, uu____19256), uu____19257) -> begin
q
end
| uu____19308 -> begin
[]
end))))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail1 = (fun uu____19332 -> (

let uu____19333 = (

let uu____19335 = (FStar_Util.string_of_int i)
in (

let uu____19337 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" uu____19335 uu____19337)))
in (failwith uu____19333)))
in (

let uu____19340 = (lookup_datacon env lid)
in (match (uu____19340) with
| (uu____19345, t) -> begin
(

let uu____19347 = (

let uu____19348 = (FStar_Syntax_Subst.compress t)
in uu____19348.FStar_Syntax_Syntax.n)
in (match (uu____19347) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____19352) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail1 ())
end
| uu____19381 -> begin
(

let b = (FStar_List.nth binders i)
in (

let uu____19396 = (FStar_Syntax_Util.mk_field_projector_name lid (FStar_Pervasives_Native.fst b) i)
in (FStar_All.pipe_right uu____19396 FStar_Pervasives_Native.fst)))
end)
end
| uu____19407 -> begin
(fail1 ())
end))
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____19421 = (lookup_qname env l)
in (match (uu____19421) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____19423, uu____19424, uu____19425); FStar_Syntax_Syntax.sigrng = uu____19426; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____19428; FStar_Syntax_Syntax.sigattrs = uu____19429}, uu____19430), uu____19431) -> begin
(FStar_Util.for_some (fun uu___241_19484 -> (match (uu___241_19484) with
| FStar_Syntax_Syntax.Projector (uu____19486) -> begin
true
end
| uu____19492 -> begin
false
end)) quals)
end
| uu____19494 -> begin
false
end)))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____19508 = (lookup_qname env lid)
in (match (uu____19508) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____19510, uu____19511, uu____19512, uu____19513, uu____19514, uu____19515); FStar_Syntax_Syntax.sigrng = uu____19516; FStar_Syntax_Syntax.sigquals = uu____19517; FStar_Syntax_Syntax.sigmeta = uu____19518; FStar_Syntax_Syntax.sigattrs = uu____19519}, uu____19520), uu____19521) -> begin
true
end
| uu____19579 -> begin
false
end)))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____19593 = (lookup_qname env lid)
in (match (uu____19593) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____19595, uu____19596, uu____19597, uu____19598, uu____19599, uu____19600); FStar_Syntax_Syntax.sigrng = uu____19601; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____19603; FStar_Syntax_Syntax.sigattrs = uu____19604}, uu____19605), uu____19606) -> begin
(FStar_Util.for_some (fun uu___242_19667 -> (match (uu___242_19667) with
| FStar_Syntax_Syntax.RecordType (uu____19669) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____19679) -> begin
true
end
| uu____19689 -> begin
false
end)) quals)
end
| uu____19691 -> begin
false
end)))


let qninfo_is_action : qninfo  ->  Prims.bool = (fun qninfo -> (match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____19701, uu____19702); FStar_Syntax_Syntax.sigrng = uu____19703; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____19705; FStar_Syntax_Syntax.sigattrs = uu____19706}, uu____19707), uu____19708) -> begin
(FStar_Util.for_some (fun uu___243_19765 -> (match (uu___243_19765) with
| FStar_Syntax_Syntax.Action (uu____19767) -> begin
true
end
| uu____19769 -> begin
false
end)) quals)
end
| uu____19771 -> begin
false
end))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____19785 = (lookup_qname env lid)
in (FStar_All.pipe_left qninfo_is_action uu____19785)))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition_lid)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (fun env head1 -> (

let uu____19802 = (

let uu____19803 = (FStar_Syntax_Util.un_uinst head1)
in uu____19803.FStar_Syntax_Syntax.n)
in (match (uu____19802) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(match (fv.FStar_Syntax_Syntax.fv_delta) with
| FStar_Syntax_Syntax.Delta_equational_at_level (uu____19809) -> begin
true
end
| uu____19812 -> begin
false
end)
end
| uu____19814 -> begin
false
end))))


let is_irreducible : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____19828 = (lookup_qname env l)
in (match (uu____19828) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, uu____19831), uu____19832) -> begin
(FStar_Util.for_some (fun uu___244_19880 -> (match (uu___244_19880) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____19883 -> begin
false
end)) se.FStar_Syntax_Syntax.sigquals)
end
| uu____19885 -> begin
false
end)))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun x -> (match ((FStar_Pervasives_Native.fst x)) with
| FStar_Util.Inl (uu____19961) -> begin
FStar_Pervasives_Native.Some (false)
end
| FStar_Util.Inr (se, uu____19979) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____19997) -> begin
FStar_Pervasives_Native.Some ((FStar_List.contains FStar_Syntax_Syntax.New se.FStar_Syntax_Syntax.sigquals))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____20005) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____20024 -> begin
FStar_Pervasives_Native.Some (false)
end)
end))
in (

let uu____20027 = (

let uu____20031 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____20031 mapper))
in (match (uu____20027) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
false
end))))


let num_inductive_ty_params : env  ->  FStar_Ident.lident  ->  Prims.int FStar_Pervasives_Native.option = (fun env lid -> (

let uu____20091 = (lookup_qname env lid)
in (match (uu____20091) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____20095, uu____20096, tps, uu____20098, uu____20099, uu____20100); FStar_Syntax_Syntax.sigrng = uu____20101; FStar_Syntax_Syntax.sigquals = uu____20102; FStar_Syntax_Syntax.sigmeta = uu____20103; FStar_Syntax_Syntax.sigattrs = uu____20104}, uu____20105), uu____20106) -> begin
FStar_Pervasives_Native.Some ((FStar_List.length tps))
end
| uu____20172 -> begin
FStar_Pervasives_Native.None
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun uu____20218 -> (match (uu____20218) with
| (d, uu____20227) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)
end)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (

let uu____20243 = (effect_decl_opt env l)
in (match (uu____20243) with
| FStar_Pervasives_Native.None -> begin
(

let uu____20258 = (name_not_found l)
in (

let uu____20264 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.raise_error uu____20258 uu____20264)))
end
| FStar_Pervasives_Native.Some (md) -> begin
(FStar_Pervasives_Native.fst md)
end)))


let identity_mlift : mlift = {mlift_wp = (fun uu____20287 t wp -> wp); mlift_term = FStar_Pervasives_Native.Some ((fun uu____20306 t wp e -> (FStar_Util.return_all e)))}


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> (

let uu____20338 = (FStar_Ident.lid_equals l1 l2)
in (match (uu____20338) with
| true -> begin
((l1), (identity_mlift), (identity_mlift))
end
| uu____20347 -> begin
(

let uu____20349 = (((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid)))
in (match (uu____20349) with
| true -> begin
((FStar_Parser_Const.effect_GTot_lid), (identity_mlift), (identity_mlift))
end
| uu____20358 -> begin
(

let uu____20360 = (FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun uu____20413 -> (match (uu____20413) with
| (m1, m2, uu____20427, uu____20428, uu____20429) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))
in (match (uu____20360) with
| FStar_Pervasives_Native.None -> begin
(

let uu____20446 = (

let uu____20452 = (

let uu____20454 = (FStar_Syntax_Print.lid_to_string l1)
in (

let uu____20456 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" uu____20454 uu____20456)))
in ((FStar_Errors.Fatal_EffectsCannotBeComposed), (uu____20452)))
in (FStar_Errors.raise_error uu____20446 env.range))
end
| FStar_Pervasives_Native.Some (uu____20466, uu____20467, m3, j1, j2) -> begin
((m3), (j1), (j2))
end))
end))
end)))


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge FStar_Pervasives_Native.option = (fun env l1 l2 -> (

let uu____20501 = ((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)))
in (match (uu____20501) with
| true -> begin
FStar_Pervasives_Native.Some ({msource = l1; mtarget = l2; mlift = identity_mlift})
end
| uu____20506 -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)))


let wp_sig_aux : 'Auu____20521 . (FStar_Syntax_Syntax.eff_decl * 'Auu____20521) Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun decls m -> (

let uu____20550 = (FStar_All.pipe_right decls (FStar_Util.find_opt (fun uu____20576 -> (match (uu____20576) with
| (d, uu____20583) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)
end))))
in (match (uu____20550) with
| FStar_Pervasives_Native.None -> begin
(

let uu____20594 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith uu____20594))
end
| FStar_Pervasives_Native.Some (md, _q) -> begin
(

let uu____20609 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (uu____20609) with
| (uu____20624, s) -> begin
(

let s1 = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s1.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, uu____20642))::((wp, uu____20644))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____20700 -> begin
(failwith "Impossible")
end))
end))
end)))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let null_wp_for_eff : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env eff_name res_u res_t -> (

let uu____20758 = (FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid)
in (match (uu____20758) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' res_t (FStar_Pervasives_Native.Some (res_u)))
end
| uu____20761 -> begin
(

let uu____20763 = (FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_GTot_lid)
in (match (uu____20763) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal' res_t (FStar_Pervasives_Native.Some (res_u)))
end
| uu____20766 -> begin
(

let eff_name1 = (norm_eff_name env eff_name)
in (

let ed = (get_effect_decl env eff_name1)
in (

let null_wp = (inst_effect_fun_with ((res_u)::[]) env ed ed.FStar_Syntax_Syntax.null_wp)
in (

let null_wp_res = (

let uu____20774 = (get_range env)
in (

let uu____20775 = (

let uu____20782 = (

let uu____20783 = (

let uu____20800 = (

let uu____20811 = (FStar_Syntax_Syntax.as_arg res_t)
in (uu____20811)::[])
in ((null_wp), (uu____20800)))
in FStar_Syntax_Syntax.Tm_app (uu____20783))
in (FStar_Syntax_Syntax.mk uu____20782))
in (uu____20775 FStar_Pervasives_Native.None uu____20774)))
in (

let uu____20851 = (

let uu____20852 = (

let uu____20863 = (FStar_Syntax_Syntax.as_arg null_wp_res)
in (uu____20863)::[])
in {FStar_Syntax_Syntax.comp_univs = (res_u)::[]; FStar_Syntax_Syntax.effect_name = eff_name1; FStar_Syntax_Syntax.result_typ = res_t; FStar_Syntax_Syntax.effect_args = uu____20852; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp uu____20851))))))
end))
end)))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let effects = (

let uu___259_20901 = env.effects
in {decls = (((ne), (se.FStar_Syntax_Syntax.sigquals)))::env.effects.decls; order = uu___259_20901.order; joins = uu___259_20901.joins})
in (

let uu___260_20910 = env
in {solver = uu___260_20910.solver; range = uu___260_20910.range; curmodule = uu___260_20910.curmodule; gamma = uu___260_20910.gamma; gamma_sig = uu___260_20910.gamma_sig; gamma_cache = uu___260_20910.gamma_cache; modules = uu___260_20910.modules; expected_typ = uu___260_20910.expected_typ; sigtab = uu___260_20910.sigtab; attrtab = uu___260_20910.attrtab; is_pattern = uu___260_20910.is_pattern; instantiate_imp = uu___260_20910.instantiate_imp; effects = effects; generalize = uu___260_20910.generalize; letrecs = uu___260_20910.letrecs; top_level = uu___260_20910.top_level; check_uvars = uu___260_20910.check_uvars; use_eq = uu___260_20910.use_eq; is_iface = uu___260_20910.is_iface; admit = uu___260_20910.admit; lax = uu___260_20910.lax; lax_universes = uu___260_20910.lax_universes; phase1 = uu___260_20910.phase1; failhard = uu___260_20910.failhard; nosynth = uu___260_20910.nosynth; uvar_subtyping = uu___260_20910.uvar_subtyping; tc_term = uu___260_20910.tc_term; type_of = uu___260_20910.type_of; universe_of = uu___260_20910.universe_of; check_type_of = uu___260_20910.check_type_of; use_bv_sorts = uu___260_20910.use_bv_sorts; qtbl_name_and_index = uu___260_20910.qtbl_name_and_index; normalized_eff_names = uu___260_20910.normalized_eff_names; fv_delta_depths = uu___260_20910.fv_delta_depths; proof_ns = uu___260_20910.proof_ns; synth_hook = uu___260_20910.synth_hook; splice = uu___260_20910.splice; postprocess = uu___260_20910.postprocess; is_native_tactic = uu___260_20910.is_native_tactic; identifier_info = uu___260_20910.identifier_info; tc_hooks = uu___260_20910.tc_hooks; dsenv = uu___260_20910.dsenv; nbe = uu___260_20910.nbe}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let compose_edges = (fun e1 e2 -> (

let composed_lift = (

let mlift_wp = (fun u r wp1 -> (

let uu____20940 = (e1.mlift.mlift_wp u r wp1)
in (e2.mlift.mlift_wp u r uu____20940)))
in (

let mlift_term = (match (((e1.mlift.mlift_term), (e2.mlift.mlift_term))) with
| (FStar_Pervasives_Native.Some (l1), FStar_Pervasives_Native.Some (l2)) -> begin
FStar_Pervasives_Native.Some ((fun u t wp e -> (

let uu____21098 = (e1.mlift.mlift_wp u t wp)
in (

let uu____21099 = (l1 u t wp e)
in (l2 u t uu____21098 uu____21099)))))
end
| uu____21100 -> begin
FStar_Pervasives_Native.None
end)
in {mlift_wp = mlift_wp; mlift_term = mlift_term}))
in {msource = e1.msource; mtarget = e2.mtarget; mlift = composed_lift}))
in (

let mk_mlift_wp = (fun lift_t u r wp1 -> (

let uu____21172 = (inst_tscheme_with lift_t ((u)::[]))
in (match (uu____21172) with
| (uu____21179, lift_t1) -> begin
(

let uu____21181 = (

let uu____21188 = (

let uu____21189 = (

let uu____21206 = (

let uu____21217 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____21226 = (

let uu____21237 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____21237)::[])
in (uu____21217)::uu____21226))
in ((lift_t1), (uu____21206)))
in FStar_Syntax_Syntax.Tm_app (uu____21189))
in (FStar_Syntax_Syntax.mk uu____21188))
in (uu____21181 FStar_Pervasives_Native.None wp1.FStar_Syntax_Syntax.pos))
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

let uu____21350 = (inst_tscheme_with lift_t ((u)::[]))
in (match (uu____21350) with
| (uu____21357, lift_t1) -> begin
(

let uu____21359 = (

let uu____21366 = (

let uu____21367 = (

let uu____21384 = (

let uu____21395 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____21404 = (

let uu____21415 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____21424 = (

let uu____21435 = (FStar_Syntax_Syntax.as_arg e)
in (uu____21435)::[])
in (uu____21415)::uu____21424))
in (uu____21395)::uu____21404))
in ((lift_t1), (uu____21384)))
in FStar_Syntax_Syntax.Tm_app (uu____21367))
in (FStar_Syntax_Syntax.mk uu____21366))
in (uu____21359 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
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

let uu____21540 = (

let uu____21541 = (FStar_Ident.lid_of_path ((s)::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____21541 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.fv_to_tm uu____21540)))
in (

let arg = (bogus_term "ARG")
in (

let wp = (bogus_term "WP")
in (

let e = (bogus_term "COMP")
in (

let uu____21550 = (

let uu____21552 = (l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp)
in (FStar_Syntax_Print.term_to_string uu____21552))
in (

let uu____21553 = (

let uu____21555 = (FStar_Util.map_opt l.mlift_term (fun l1 -> (

let uu____21583 = (l1 FStar_Syntax_Syntax.U_zero arg wp e)
in (FStar_Syntax_Print.term_to_string uu____21583))))
in (FStar_Util.dflt "none" uu____21555))
in (FStar_Util.format2 "{ wp : %s ; term : %s }" uu____21550 uu____21553))))))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun uu____21612 -> (match (uu____21612) with
| (e, uu____21620) -> begin
e.FStar_Syntax_Syntax.mname
end))))
in (

let find_edge = (fun order1 uu____21643 -> (match (uu____21643) with
| (i, j) -> begin
(

let uu____21654 = (FStar_Ident.lid_equals i j)
in (match (uu____21654) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _0_1 -> FStar_Pervasives_Native.Some (_0_1)))
end
| uu____21661 -> begin
(FStar_All.pipe_right order1 (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end))
end))
in (

let order1 = (

let fold_fun = (fun order1 k -> (

let uu____21689 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (

let uu____21699 = (FStar_Ident.lid_equals i k)
in (match (uu____21699) with
| true -> begin
[]
end
| uu____21704 -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let uu____21713 = (FStar_Ident.lid_equals j k)
in (match (uu____21713) with
| true -> begin
[]
end
| uu____21718 -> begin
(

let uu____21720 = (

let uu____21729 = (find_edge order1 ((i), (k)))
in (

let uu____21732 = (find_edge order1 ((k), (j)))
in ((uu____21729), (uu____21732))))
in (match (uu____21720) with
| (FStar_Pervasives_Native.Some (e1), FStar_Pervasives_Native.Some (e2)) -> begin
(

let uu____21747 = (compose_edges e1 e2)
in (uu____21747)::[])
end
| uu____21748 -> begin
[]
end))
end)))))
end)))))
in (FStar_List.append order1 uu____21689)))
in (FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)))
in (

let order2 = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order1)
in ((FStar_All.pipe_right order2 (FStar_List.iter (fun edge1 -> (

let uu____21778 = ((FStar_Ident.lid_equals edge1.msource FStar_Parser_Const.effect_DIV_lid) && (

let uu____21781 = (lookup_effect_quals env edge1.mtarget)
in (FStar_All.pipe_right uu____21781 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))))
in (match (uu____21778) with
| true -> begin
(

let uu____21788 = (

let uu____21794 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge1.mtarget.FStar_Ident.str)
in ((FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal), (uu____21794)))
in (

let uu____21798 = (get_range env)
in (FStar_Errors.raise_error uu____21788 uu____21798)))
end
| uu____21799 -> begin
()
end)))));
(

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (

let uu____21876 = (FStar_Ident.lid_equals i j)
in (match (uu____21876) with
| true -> begin
FStar_Pervasives_Native.Some (((i), ((id_edge i)), ((id_edge i))))
end
| uu____21893 -> begin
(FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (

let uu____21928 = (

let uu____21937 = (find_edge order2 ((i), (k)))
in (

let uu____21940 = (find_edge order2 ((j), (k)))
in ((uu____21937), (uu____21940))))
in (match (uu____21928) with
| (FStar_Pervasives_Native.Some (ik), FStar_Pervasives_Native.Some (jk)) -> begin
(match (bopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((k), (ik), (jk)))
end
| FStar_Pervasives_Native.Some (ub, uu____21982, uu____21983) -> begin
(

let uu____21990 = (

let uu____21997 = (

let uu____21999 = (find_edge order2 ((k), (ub)))
in (FStar_Util.is_some uu____21999))
in (

let uu____22002 = (

let uu____22004 = (find_edge order2 ((ub), (k)))
in (FStar_Util.is_some uu____22004))
in ((uu____21997), (uu____22002))))
in (match (uu____21990) with
| (true, true) -> begin
(

let uu____22021 = (FStar_Ident.lid_equals k ub)
in (match (uu____22021) with
| true -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Warning_UpperBoundCandidateAlreadyVisited), ("Looking multiple times at the same upper bound candidate")));
bopt;
)
end
| uu____22035 -> begin
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
| uu____22064 -> begin
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

let uu___261_22137 = env.effects
in {decls = uu___261_22137.decls; order = order2; joins = joins})
in (

let uu___262_22138 = env
in {solver = uu___262_22138.solver; range = uu___262_22138.range; curmodule = uu___262_22138.curmodule; gamma = uu___262_22138.gamma; gamma_sig = uu___262_22138.gamma_sig; gamma_cache = uu___262_22138.gamma_cache; modules = uu___262_22138.modules; expected_typ = uu___262_22138.expected_typ; sigtab = uu___262_22138.sigtab; attrtab = uu___262_22138.attrtab; is_pattern = uu___262_22138.is_pattern; instantiate_imp = uu___262_22138.instantiate_imp; effects = effects; generalize = uu___262_22138.generalize; letrecs = uu___262_22138.letrecs; top_level = uu___262_22138.top_level; check_uvars = uu___262_22138.check_uvars; use_eq = uu___262_22138.use_eq; is_iface = uu___262_22138.is_iface; admit = uu___262_22138.admit; lax = uu___262_22138.lax; lax_universes = uu___262_22138.lax_universes; phase1 = uu___262_22138.phase1; failhard = uu___262_22138.failhard; nosynth = uu___262_22138.nosynth; uvar_subtyping = uu___262_22138.uvar_subtyping; tc_term = uu___262_22138.tc_term; type_of = uu___262_22138.type_of; universe_of = uu___262_22138.universe_of; check_type_of = uu___262_22138.check_type_of; use_bv_sorts = uu___262_22138.use_bv_sorts; qtbl_name_and_index = uu___262_22138.qtbl_name_and_index; normalized_eff_names = uu___262_22138.normalized_eff_names; fv_delta_depths = uu___262_22138.fv_delta_depths; proof_ns = uu___262_22138.proof_ns; synth_hook = uu___262_22138.synth_hook; splice = uu___262_22138.splice; postprocess = uu___262_22138.postprocess; is_native_tactic = uu___262_22138.is_native_tactic; identifier_info = uu___262_22138.identifier_info; tc_hooks = uu___262_22138.tc_hooks; dsenv = uu___262_22138.dsenv; nbe = uu___262_22138.nbe})));
))))))))))))))
end
| uu____22139 -> begin
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
| uu____22168 -> begin
c
end)
in (FStar_Syntax_Util.comp_to_comp_typ c1)))


let rec unfold_effect_abbrev : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (comp_to_comp_typ env comp)
in (

let uu____22181 = (lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name)
in (match (uu____22181) with
| FStar_Pervasives_Native.None -> begin
c
end
| FStar_Pervasives_Native.Some (binders, cdef) -> begin
(

let uu____22198 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (uu____22198) with
| (binders1, cdef1) -> begin
((match ((Prims.op_disEquality (FStar_List.length binders1) ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))) with
| true -> begin
(

let uu____22223 = (

let uu____22229 = (

let uu____22231 = (FStar_Util.string_of_int (FStar_List.length binders1))
in (

let uu____22239 = (FStar_Util.string_of_int ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))
in (

let uu____22250 = (

let uu____22252 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Print.comp_to_string uu____22252))
in (FStar_Util.format3 "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s" uu____22231 uu____22239 uu____22250))))
in ((FStar_Errors.Fatal_ConstructorArgLengthMismatch), (uu____22229)))
in (FStar_Errors.raise_error uu____22223 comp.FStar_Syntax_Syntax.pos))
end
| uu____22255 -> begin
()
end);
(

let inst1 = (

let uu____22260 = (

let uu____22271 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (uu____22271)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun uu____22308 uu____22309 -> (match (((uu____22308), (uu____22309))) with
| ((x, uu____22339), (t, uu____22341)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders1 uu____22260))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst1 cdef1)
in (

let c2 = (

let uu____22372 = (

let uu___263_22373 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = uu___263_22373.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___263_22373.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___263_22373.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___263_22373.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right uu____22372 FStar_Syntax_Syntax.mk_Comp))
in (unfold_effect_abbrev env c2))));
)
end))
end))))


let effect_repr_aux : 'Auu____22385 . 'Auu____22385  ->  env  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun only_reifiable env c u_c -> (

let effect_name = (norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (

let uu____22415 = (effect_decl_opt env effect_name)
in (match (uu____22415) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(match (ed.FStar_Syntax_Syntax.repr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| uu____22454 -> begin
(

let c1 = (unfold_effect_abbrev env c)
in (

let res_typ = c1.FStar_Syntax_Syntax.result_typ
in (

let wp = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (hd1)::uu____22477 -> begin
hd1
end
| [] -> begin
(

let name = (FStar_Ident.string_of_lid effect_name)
in (

let message = (

let uu____22516 = (FStar_Util.format1 "Not enough arguments for effect %s. " name)
in (Prims.strcat uu____22516 (Prims.strcat "This usually happens when you use a partially applied DM4F effect, " "like [TAC int] instead of [Tac int].")))
in (

let uu____22521 = (get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NotEnoughArgumentsForEffect), (message)) uu____22521))))
end)
in (

let repr = (inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____22536 = (

let uu____22539 = (get_range env)
in (

let uu____22540 = (

let uu____22547 = (

let uu____22548 = (

let uu____22565 = (

let uu____22576 = (FStar_Syntax_Syntax.as_arg res_typ)
in (uu____22576)::(wp)::[])
in ((repr), (uu____22565)))
in FStar_Syntax_Syntax.Tm_app (uu____22548))
in (FStar_Syntax_Syntax.mk uu____22547))
in (uu____22540 FStar_Pervasives_Native.None uu____22539)))
in FStar_Pervasives_Native.Some (uu____22536))))))
end)
end))))


let effect_repr : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let is_user_reifiable_effect : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env effect_lid -> (

let effect_lid1 = (norm_eff_name env effect_lid)
in (

let quals = (lookup_effect_quals env effect_lid1)
in (FStar_List.contains FStar_Syntax_Syntax.Reifiable quals))))


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
| uu____22723 -> begin
false
end))


let is_reifiable_function : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____22738 = (

let uu____22739 = (FStar_Syntax_Subst.compress t)
in uu____22739.FStar_Syntax_Syntax.n)
in (match (uu____22738) with
| FStar_Syntax_Syntax.Tm_arrow (uu____22743, c) -> begin
(is_reifiable_comp env c)
end
| uu____22765 -> begin
false
end)))


let reify_comp : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let l = (FStar_Syntax_Util.comp_effect_name c)
in ((

let uu____22785 = (

let uu____22787 = (is_reifiable_effect env l)
in (not (uu____22787)))
in (match (uu____22785) with
| true -> begin
(

let uu____22790 = (

let uu____22796 = (

let uu____22798 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format1 "Effect %s cannot be reified" uu____22798))
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____22796)))
in (

let uu____22802 = (get_range env)
in (FStar_Errors.raise_error uu____22790 uu____22802)))
end
| uu____22803 -> begin
()
end));
(

let uu____22805 = (effect_repr_aux true env c u_c)
in (match (uu____22805) with
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

let uu___264_22841 = env
in {solver = uu___264_22841.solver; range = uu___264_22841.range; curmodule = uu___264_22841.curmodule; gamma = uu___264_22841.gamma; gamma_sig = (sb)::env.gamma_sig; gamma_cache = uu___264_22841.gamma_cache; modules = uu___264_22841.modules; expected_typ = uu___264_22841.expected_typ; sigtab = uu___264_22841.sigtab; attrtab = uu___264_22841.attrtab; is_pattern = uu___264_22841.is_pattern; instantiate_imp = uu___264_22841.instantiate_imp; effects = uu___264_22841.effects; generalize = uu___264_22841.generalize; letrecs = uu___264_22841.letrecs; top_level = uu___264_22841.top_level; check_uvars = uu___264_22841.check_uvars; use_eq = uu___264_22841.use_eq; is_iface = uu___264_22841.is_iface; admit = uu___264_22841.admit; lax = uu___264_22841.lax; lax_universes = uu___264_22841.lax_universes; phase1 = uu___264_22841.phase1; failhard = uu___264_22841.failhard; nosynth = uu___264_22841.nosynth; uvar_subtyping = uu___264_22841.uvar_subtyping; tc_term = uu___264_22841.tc_term; type_of = uu___264_22841.type_of; universe_of = uu___264_22841.universe_of; check_type_of = uu___264_22841.check_type_of; use_bv_sorts = uu___264_22841.use_bv_sorts; qtbl_name_and_index = uu___264_22841.qtbl_name_and_index; normalized_eff_names = uu___264_22841.normalized_eff_names; fv_delta_depths = uu___264_22841.fv_delta_depths; proof_ns = uu___264_22841.proof_ns; synth_hook = uu___264_22841.synth_hook; splice = uu___264_22841.splice; postprocess = uu___264_22841.postprocess; is_native_tactic = uu___264_22841.is_native_tactic; identifier_info = uu___264_22841.identifier_info; tc_hooks = uu___264_22841.tc_hooks; dsenv = uu___264_22841.dsenv; nbe = uu___264_22841.nbe})
in ((add_sigelt env1 s);
(env1.tc_hooks.tc_push_in_gamma_hook env1 (FStar_Util.Inr (sb)));
(build_lattice env1 s);
))))


let push_local_binding : env  ->  FStar_Syntax_Syntax.binding  ->  env = (fun env b -> (

let uu___265_22855 = env
in {solver = uu___265_22855.solver; range = uu___265_22855.range; curmodule = uu___265_22855.curmodule; gamma = (b)::env.gamma; gamma_sig = uu___265_22855.gamma_sig; gamma_cache = uu___265_22855.gamma_cache; modules = uu___265_22855.modules; expected_typ = uu___265_22855.expected_typ; sigtab = uu___265_22855.sigtab; attrtab = uu___265_22855.attrtab; is_pattern = uu___265_22855.is_pattern; instantiate_imp = uu___265_22855.instantiate_imp; effects = uu___265_22855.effects; generalize = uu___265_22855.generalize; letrecs = uu___265_22855.letrecs; top_level = uu___265_22855.top_level; check_uvars = uu___265_22855.check_uvars; use_eq = uu___265_22855.use_eq; is_iface = uu___265_22855.is_iface; admit = uu___265_22855.admit; lax = uu___265_22855.lax; lax_universes = uu___265_22855.lax_universes; phase1 = uu___265_22855.phase1; failhard = uu___265_22855.failhard; nosynth = uu___265_22855.nosynth; uvar_subtyping = uu___265_22855.uvar_subtyping; tc_term = uu___265_22855.tc_term; type_of = uu___265_22855.type_of; universe_of = uu___265_22855.universe_of; check_type_of = uu___265_22855.check_type_of; use_bv_sorts = uu___265_22855.use_bv_sorts; qtbl_name_and_index = uu___265_22855.qtbl_name_and_index; normalized_eff_names = uu___265_22855.normalized_eff_names; fv_delta_depths = uu___265_22855.fv_delta_depths; proof_ns = uu___265_22855.proof_ns; synth_hook = uu___265_22855.synth_hook; splice = uu___265_22855.splice; postprocess = uu___265_22855.postprocess; is_native_tactic = uu___265_22855.is_native_tactic; identifier_info = uu___265_22855.identifier_info; tc_hooks = uu___265_22855.tc_hooks; dsenv = uu___265_22855.dsenv; nbe = uu___265_22855.nbe}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (FStar_Syntax_Syntax.Binding_var (x))))


let push_bvs : env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  env = (fun env bvs -> (FStar_List.fold_left (fun env1 bv -> (push_bv env1 bv)) env bvs))


let pop_bv : env  ->  (FStar_Syntax_Syntax.bv * env) FStar_Pervasives_Native.option = (fun env -> (match (env.gamma) with
| (FStar_Syntax_Syntax.Binding_var (x))::rest -> begin
FStar_Pervasives_Native.Some (((x), ((

let uu___266_22913 = env
in {solver = uu___266_22913.solver; range = uu___266_22913.range; curmodule = uu___266_22913.curmodule; gamma = rest; gamma_sig = uu___266_22913.gamma_sig; gamma_cache = uu___266_22913.gamma_cache; modules = uu___266_22913.modules; expected_typ = uu___266_22913.expected_typ; sigtab = uu___266_22913.sigtab; attrtab = uu___266_22913.attrtab; is_pattern = uu___266_22913.is_pattern; instantiate_imp = uu___266_22913.instantiate_imp; effects = uu___266_22913.effects; generalize = uu___266_22913.generalize; letrecs = uu___266_22913.letrecs; top_level = uu___266_22913.top_level; check_uvars = uu___266_22913.check_uvars; use_eq = uu___266_22913.use_eq; is_iface = uu___266_22913.is_iface; admit = uu___266_22913.admit; lax = uu___266_22913.lax; lax_universes = uu___266_22913.lax_universes; phase1 = uu___266_22913.phase1; failhard = uu___266_22913.failhard; nosynth = uu___266_22913.nosynth; uvar_subtyping = uu___266_22913.uvar_subtyping; tc_term = uu___266_22913.tc_term; type_of = uu___266_22913.type_of; universe_of = uu___266_22913.universe_of; check_type_of = uu___266_22913.check_type_of; use_bv_sorts = uu___266_22913.use_bv_sorts; qtbl_name_and_index = uu___266_22913.qtbl_name_and_index; normalized_eff_names = uu___266_22913.normalized_eff_names; fv_delta_depths = uu___266_22913.fv_delta_depths; proof_ns = uu___266_22913.proof_ns; synth_hook = uu___266_22913.synth_hook; splice = uu___266_22913.splice; postprocess = uu___266_22913.postprocess; is_native_tactic = uu___266_22913.is_native_tactic; identifier_info = uu___266_22913.identifier_info; tc_hooks = uu___266_22913.tc_hooks; dsenv = uu___266_22913.dsenv; nbe = uu___266_22913.nbe}))))
end
| uu____22914 -> begin
FStar_Pervasives_Native.None
end))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env1 uu____22943 -> (match (uu____22943) with
| (x, uu____22951) -> begin
(push_bv env1 x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x1) -> begin
(

let x2 = (

let uu___267_22986 = x1
in {FStar_Syntax_Syntax.ppname = uu___267_22986.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___267_22986.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)})
in FStar_Syntax_Syntax.Binding_var (x2))
end
| FStar_Util.Inr (fv) -> begin
FStar_Syntax_Syntax.Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> ((add_sigelts env m.FStar_Syntax_Syntax.exports);
(

let uu___268_23028 = env
in {solver = uu___268_23028.solver; range = uu___268_23028.range; curmodule = uu___268_23028.curmodule; gamma = []; gamma_sig = []; gamma_cache = uu___268_23028.gamma_cache; modules = (m)::env.modules; expected_typ = FStar_Pervasives_Native.None; sigtab = uu___268_23028.sigtab; attrtab = uu___268_23028.attrtab; is_pattern = uu___268_23028.is_pattern; instantiate_imp = uu___268_23028.instantiate_imp; effects = uu___268_23028.effects; generalize = uu___268_23028.generalize; letrecs = uu___268_23028.letrecs; top_level = uu___268_23028.top_level; check_uvars = uu___268_23028.check_uvars; use_eq = uu___268_23028.use_eq; is_iface = uu___268_23028.is_iface; admit = uu___268_23028.admit; lax = uu___268_23028.lax; lax_universes = uu___268_23028.lax_universes; phase1 = uu___268_23028.phase1; failhard = uu___268_23028.failhard; nosynth = uu___268_23028.nosynth; uvar_subtyping = uu___268_23028.uvar_subtyping; tc_term = uu___268_23028.tc_term; type_of = uu___268_23028.type_of; universe_of = uu___268_23028.universe_of; check_type_of = uu___268_23028.check_type_of; use_bv_sorts = uu___268_23028.use_bv_sorts; qtbl_name_and_index = uu___268_23028.qtbl_name_and_index; normalized_eff_names = uu___268_23028.normalized_eff_names; fv_delta_depths = uu___268_23028.fv_delta_depths; proof_ns = uu___268_23028.proof_ns; synth_hook = uu___268_23028.synth_hook; splice = uu___268_23028.splice; postprocess = uu___268_23028.postprocess; is_native_tactic = uu___268_23028.is_native_tactic; identifier_info = uu___268_23028.identifier_info; tc_hooks = uu___268_23028.tc_hooks; dsenv = uu___268_23028.dsenv; nbe = uu___268_23028.nbe});
))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env1 x -> (push_local_binding env1 (FStar_Syntax_Syntax.Binding_univ (x)))) env xs))


let open_universes_in : env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term Prims.list  ->  (env * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term Prims.list) = (fun env uvs terms -> (

let uu____23072 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____23072) with
| (univ_subst, univ_vars) -> begin
(

let env' = (push_univ_vars env univ_vars)
in (

let uu____23100 = (FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms)
in ((env'), (univ_vars), (uu____23100))))
end)))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let uu___269_23116 = env
in {solver = uu___269_23116.solver; range = uu___269_23116.range; curmodule = uu___269_23116.curmodule; gamma = uu___269_23116.gamma; gamma_sig = uu___269_23116.gamma_sig; gamma_cache = uu___269_23116.gamma_cache; modules = uu___269_23116.modules; expected_typ = FStar_Pervasives_Native.Some (t); sigtab = uu___269_23116.sigtab; attrtab = uu___269_23116.attrtab; is_pattern = uu___269_23116.is_pattern; instantiate_imp = uu___269_23116.instantiate_imp; effects = uu___269_23116.effects; generalize = uu___269_23116.generalize; letrecs = uu___269_23116.letrecs; top_level = uu___269_23116.top_level; check_uvars = uu___269_23116.check_uvars; use_eq = false; is_iface = uu___269_23116.is_iface; admit = uu___269_23116.admit; lax = uu___269_23116.lax; lax_universes = uu___269_23116.lax_universes; phase1 = uu___269_23116.phase1; failhard = uu___269_23116.failhard; nosynth = uu___269_23116.nosynth; uvar_subtyping = uu___269_23116.uvar_subtyping; tc_term = uu___269_23116.tc_term; type_of = uu___269_23116.type_of; universe_of = uu___269_23116.universe_of; check_type_of = uu___269_23116.check_type_of; use_bv_sorts = uu___269_23116.use_bv_sorts; qtbl_name_and_index = uu___269_23116.qtbl_name_and_index; normalized_eff_names = uu___269_23116.normalized_eff_names; fv_delta_depths = uu___269_23116.fv_delta_depths; proof_ns = uu___269_23116.proof_ns; synth_hook = uu___269_23116.synth_hook; splice = uu___269_23116.splice; postprocess = uu___269_23116.postprocess; is_native_tactic = uu___269_23116.is_native_tactic; identifier_info = uu___269_23116.identifier_info; tc_hooks = uu___269_23116.tc_hooks; dsenv = uu___269_23116.dsenv; nbe = uu___269_23116.nbe}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun env -> (match (env.expected_typ) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) = (fun env_ -> (

let uu____23147 = (expected_typ env_)
in (((

let uu___270_23153 = env_
in {solver = uu___270_23153.solver; range = uu___270_23153.range; curmodule = uu___270_23153.curmodule; gamma = uu___270_23153.gamma; gamma_sig = uu___270_23153.gamma_sig; gamma_cache = uu___270_23153.gamma_cache; modules = uu___270_23153.modules; expected_typ = FStar_Pervasives_Native.None; sigtab = uu___270_23153.sigtab; attrtab = uu___270_23153.attrtab; is_pattern = uu___270_23153.is_pattern; instantiate_imp = uu___270_23153.instantiate_imp; effects = uu___270_23153.effects; generalize = uu___270_23153.generalize; letrecs = uu___270_23153.letrecs; top_level = uu___270_23153.top_level; check_uvars = uu___270_23153.check_uvars; use_eq = false; is_iface = uu___270_23153.is_iface; admit = uu___270_23153.admit; lax = uu___270_23153.lax; lax_universes = uu___270_23153.lax_universes; phase1 = uu___270_23153.phase1; failhard = uu___270_23153.failhard; nosynth = uu___270_23153.nosynth; uvar_subtyping = uu___270_23153.uvar_subtyping; tc_term = uu___270_23153.tc_term; type_of = uu___270_23153.type_of; universe_of = uu___270_23153.universe_of; check_type_of = uu___270_23153.check_type_of; use_bv_sorts = uu___270_23153.use_bv_sorts; qtbl_name_and_index = uu___270_23153.qtbl_name_and_index; normalized_eff_names = uu___270_23153.normalized_eff_names; fv_delta_depths = uu___270_23153.fv_delta_depths; proof_ns = uu___270_23153.proof_ns; synth_hook = uu___270_23153.synth_hook; splice = uu___270_23153.splice; postprocess = uu___270_23153.postprocess; is_native_tactic = uu___270_23153.is_native_tactic; identifier_info = uu___270_23153.identifier_info; tc_hooks = uu___270_23153.tc_hooks; dsenv = uu___270_23153.dsenv; nbe = uu___270_23153.nbe})), (uu____23147))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (

let uu____23165 = (

let uu____23168 = (FStar_Ident.id_of_text "")
in (uu____23168)::[])
in (FStar_Ident.lid_of_ids uu____23165))
in (fun env m -> (

let sigs = (

let uu____23175 = (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Parser_Const.prims_lid)
in (match (uu____23175) with
| true -> begin
(

let uu____23180 = (FStar_All.pipe_right env.gamma_sig (FStar_List.map FStar_Pervasives_Native.snd))
in (FStar_All.pipe_right uu____23180 FStar_List.rev))
end
| uu____23205 -> begin
m.FStar_Syntax_Syntax.exports
end))
in ((add_sigelts env sigs);
(

let uu___271_23208 = env
in {solver = uu___271_23208.solver; range = uu___271_23208.range; curmodule = empty_lid; gamma = []; gamma_sig = []; gamma_cache = uu___271_23208.gamma_cache; modules = (m)::env.modules; expected_typ = uu___271_23208.expected_typ; sigtab = uu___271_23208.sigtab; attrtab = uu___271_23208.attrtab; is_pattern = uu___271_23208.is_pattern; instantiate_imp = uu___271_23208.instantiate_imp; effects = uu___271_23208.effects; generalize = uu___271_23208.generalize; letrecs = uu___271_23208.letrecs; top_level = uu___271_23208.top_level; check_uvars = uu___271_23208.check_uvars; use_eq = uu___271_23208.use_eq; is_iface = uu___271_23208.is_iface; admit = uu___271_23208.admit; lax = uu___271_23208.lax; lax_universes = uu___271_23208.lax_universes; phase1 = uu___271_23208.phase1; failhard = uu___271_23208.failhard; nosynth = uu___271_23208.nosynth; uvar_subtyping = uu___271_23208.uvar_subtyping; tc_term = uu___271_23208.tc_term; type_of = uu___271_23208.type_of; universe_of = uu___271_23208.universe_of; check_type_of = uu___271_23208.check_type_of; use_bv_sorts = uu___271_23208.use_bv_sorts; qtbl_name_and_index = uu___271_23208.qtbl_name_and_index; normalized_eff_names = uu___271_23208.normalized_eff_names; fv_delta_depths = uu___271_23208.fv_delta_depths; proof_ns = uu___271_23208.proof_ns; synth_hook = uu___271_23208.synth_hook; splice = uu___271_23208.splice; postprocess = uu___271_23208.postprocess; is_native_tactic = uu___271_23208.is_native_tactic; identifier_info = uu___271_23208.identifier_info; tc_hooks = uu___271_23208.tc_hooks; dsenv = uu___271_23208.dsenv; nbe = uu___271_23208.nbe});
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
| (FStar_Syntax_Syntax.Binding_univ (uu____23260))::tl1 -> begin
(aux out tl1)
end
| (FStar_Syntax_Syntax.Binding_lid (uu____23264, (uu____23265, t)))::tl1 -> begin
(

let uu____23286 = (

let uu____23289 = (FStar_Syntax_Free.uvars t)
in (ext out uu____23289))
in (aux uu____23286 tl1))
end
| (FStar_Syntax_Syntax.Binding_var ({FStar_Syntax_Syntax.ppname = uu____23292; FStar_Syntax_Syntax.index = uu____23293; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____23301 = (

let uu____23304 = (FStar_Syntax_Free.uvars t)
in (ext out uu____23304))
in (aux uu____23301 tl1))
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
| (FStar_Syntax_Syntax.Binding_univ (uu____23362))::tl1 -> begin
(aux out tl1)
end
| (FStar_Syntax_Syntax.Binding_lid (uu____23366, (uu____23367, t)))::tl1 -> begin
(

let uu____23388 = (

let uu____23391 = (FStar_Syntax_Free.univs t)
in (ext out uu____23391))
in (aux uu____23388 tl1))
end
| (FStar_Syntax_Syntax.Binding_var ({FStar_Syntax_Syntax.ppname = uu____23394; FStar_Syntax_Syntax.index = uu____23395; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____23403 = (

let uu____23406 = (FStar_Syntax_Free.univs t)
in (ext out uu____23406))
in (aux uu____23403 tl1))
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

let uu____23468 = (FStar_Util.set_add uname out)
in (aux uu____23468 tl1))
end
| (FStar_Syntax_Syntax.Binding_lid (uu____23471, (uu____23472, t)))::tl1 -> begin
(

let uu____23493 = (

let uu____23496 = (FStar_Syntax_Free.univnames t)
in (ext out uu____23496))
in (aux uu____23493 tl1))
end
| (FStar_Syntax_Syntax.Binding_var ({FStar_Syntax_Syntax.ppname = uu____23499; FStar_Syntax_Syntax.index = uu____23500; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____23508 = (

let uu____23511 = (FStar_Syntax_Free.univnames t)
in (ext out uu____23511))
in (aux uu____23508 tl1))
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : FStar_Syntax_Syntax.binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu___245_23532 -> (match (uu___245_23532) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Binding_lid (uu____23536) -> begin
[]
end
| FStar_Syntax_Syntax.Binding_univ (uu____23549) -> begin
[]
end)))))


let binders_of_bindings : FStar_Syntax_Syntax.binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____23560 = (

let uu____23569 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right uu____23569 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right uu____23560 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let print_gamma : FStar_Syntax_Syntax.gamma  ->  Prims.string = (fun gamma -> (

let uu____23617 = (FStar_All.pipe_right gamma (FStar_List.map (fun uu___246_23630 -> (match (uu___246_23630) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let uu____23633 = (FStar_Syntax_Print.bv_to_string x)
in (Prims.strcat "Binding_var " uu____23633))
end
| FStar_Syntax_Syntax.Binding_univ (u) -> begin
(Prims.strcat "Binding_univ " u.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.Binding_lid (l, uu____23639) -> begin
(

let uu____23656 = (FStar_Ident.string_of_lid l)
in (Prims.strcat "Binding_lid " uu____23656))
end))))
in (FStar_All.pipe_right uu____23617 (FStar_String.concat "::\n"))))


let string_of_delta_level : delta_level  ->  Prims.string = (fun uu___247_23670 -> (match (uu___247_23670) with
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

let uu____23676 = (FStar_Syntax_Print.delta_depth_to_string d)
in (Prims.strcat "Unfold " uu____23676))
end))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig)
in (FStar_Util.smap_fold (sigtab env) (fun uu____23699 v1 keys1 -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)) keys)))


let should_enc_path : env  ->  Prims.string Prims.list  ->  Prims.bool = (fun env path -> (

let rec str_i_prefix = (fun xs ys -> (match (((xs), (ys))) with
| ([], uu____23754) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((Prims.op_Equality (FStar_String.lowercase x) (FStar_String.lowercase y)) && (str_i_prefix xs1 ys1))
end
| (uu____23787, uu____23788) -> begin
false
end))
in (

let uu____23802 = (FStar_List.tryFind (fun uu____23824 -> (match (uu____23824) with
| (p, uu____23835) -> begin
(str_i_prefix p path)
end)) env.proof_ns)
in (match (uu____23802) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____23854, b) -> begin
b
end))))


let should_enc_lid : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____23884 = (FStar_Ident.path_of_lid lid)
in (should_enc_path env uu____23884)))


let cons_proof_ns : Prims.bool  ->  env  ->  name_prefix  ->  env = (fun b e path -> (

let uu___272_23906 = e
in {solver = uu___272_23906.solver; range = uu___272_23906.range; curmodule = uu___272_23906.curmodule; gamma = uu___272_23906.gamma; gamma_sig = uu___272_23906.gamma_sig; gamma_cache = uu___272_23906.gamma_cache; modules = uu___272_23906.modules; expected_typ = uu___272_23906.expected_typ; sigtab = uu___272_23906.sigtab; attrtab = uu___272_23906.attrtab; is_pattern = uu___272_23906.is_pattern; instantiate_imp = uu___272_23906.instantiate_imp; effects = uu___272_23906.effects; generalize = uu___272_23906.generalize; letrecs = uu___272_23906.letrecs; top_level = uu___272_23906.top_level; check_uvars = uu___272_23906.check_uvars; use_eq = uu___272_23906.use_eq; is_iface = uu___272_23906.is_iface; admit = uu___272_23906.admit; lax = uu___272_23906.lax; lax_universes = uu___272_23906.lax_universes; phase1 = uu___272_23906.phase1; failhard = uu___272_23906.failhard; nosynth = uu___272_23906.nosynth; uvar_subtyping = uu___272_23906.uvar_subtyping; tc_term = uu___272_23906.tc_term; type_of = uu___272_23906.type_of; universe_of = uu___272_23906.universe_of; check_type_of = uu___272_23906.check_type_of; use_bv_sorts = uu___272_23906.use_bv_sorts; qtbl_name_and_index = uu___272_23906.qtbl_name_and_index; normalized_eff_names = uu___272_23906.normalized_eff_names; fv_delta_depths = uu___272_23906.fv_delta_depths; proof_ns = (((path), (b)))::e.proof_ns; synth_hook = uu___272_23906.synth_hook; splice = uu___272_23906.splice; postprocess = uu___272_23906.postprocess; is_native_tactic = uu___272_23906.is_native_tactic; identifier_info = uu___272_23906.identifier_info; tc_hooks = uu___272_23906.tc_hooks; dsenv = uu___272_23906.dsenv; nbe = uu___272_23906.nbe}))


let add_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns true e path))


let rem_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns false e path))


let get_proof_ns : env  ->  proof_namespace = (fun e -> e.proof_ns)


let set_proof_ns : proof_namespace  ->  env  ->  env = (fun ns e -> (

let uu___273_23954 = e
in {solver = uu___273_23954.solver; range = uu___273_23954.range; curmodule = uu___273_23954.curmodule; gamma = uu___273_23954.gamma; gamma_sig = uu___273_23954.gamma_sig; gamma_cache = uu___273_23954.gamma_cache; modules = uu___273_23954.modules; expected_typ = uu___273_23954.expected_typ; sigtab = uu___273_23954.sigtab; attrtab = uu___273_23954.attrtab; is_pattern = uu___273_23954.is_pattern; instantiate_imp = uu___273_23954.instantiate_imp; effects = uu___273_23954.effects; generalize = uu___273_23954.generalize; letrecs = uu___273_23954.letrecs; top_level = uu___273_23954.top_level; check_uvars = uu___273_23954.check_uvars; use_eq = uu___273_23954.use_eq; is_iface = uu___273_23954.is_iface; admit = uu___273_23954.admit; lax = uu___273_23954.lax; lax_universes = uu___273_23954.lax_universes; phase1 = uu___273_23954.phase1; failhard = uu___273_23954.failhard; nosynth = uu___273_23954.nosynth; uvar_subtyping = uu___273_23954.uvar_subtyping; tc_term = uu___273_23954.tc_term; type_of = uu___273_23954.type_of; universe_of = uu___273_23954.universe_of; check_type_of = uu___273_23954.check_type_of; use_bv_sorts = uu___273_23954.use_bv_sorts; qtbl_name_and_index = uu___273_23954.qtbl_name_and_index; normalized_eff_names = uu___273_23954.normalized_eff_names; fv_delta_depths = uu___273_23954.fv_delta_depths; proof_ns = ns; synth_hook = uu___273_23954.synth_hook; splice = uu___273_23954.splice; postprocess = uu___273_23954.postprocess; is_native_tactic = uu___273_23954.is_native_tactic; identifier_info = uu___273_23954.identifier_info; tc_hooks = uu___273_23954.tc_hooks; dsenv = uu___273_23954.dsenv; nbe = uu___273_23954.nbe}))


let unbound_vars : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun e t -> (

let uu____23970 = (FStar_Syntax_Free.names t)
in (

let uu____23973 = (bound_vars e)
in (FStar_List.fold_left (fun s bv -> (FStar_Util.set_remove bv s)) uu____23970 uu____23973))))


let closed : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e t -> (

let uu____23996 = (unbound_vars e t)
in (FStar_Util.set_is_empty uu____23996)))


let closed' : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____24006 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_is_empty uu____24006)))


let string_of_proof_ns : env  ->  Prims.string = (fun env -> (

let aux = (fun uu____24027 -> (match (uu____24027) with
| (p, b) -> begin
(match (((Prims.op_Equality p []) && b)) with
| true -> begin
"*"
end
| uu____24045 -> begin
(

let uu____24047 = (FStar_Ident.text_of_path p)
in (Prims.strcat (match (b) with
| true -> begin
"+"
end
| uu____24052 -> begin
"-"
end) uu____24047))
end)
end))
in (

let uu____24055 = (

let uu____24059 = (FStar_List.map aux env.proof_ns)
in (FStar_All.pipe_right uu____24059 FStar_List.rev))
in (FStar_All.pipe_right uu____24055 (FStar_String.concat " ")))))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  guard_t = (fun g -> {guard_f = g; deferred = []; univ_ineqs = (([]), ([])); implicits = []})


let guard_form : guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.guard_f)


let is_trivial : guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {guard_f = FStar_TypeChecker_Common.Trivial; deferred = []; univ_ineqs = ([], []); implicits = i} -> begin
(FStar_All.pipe_right i (FStar_Util.for_all (fun imp -> ((Prims.op_Equality imp.imp_uvar.FStar_Syntax_Syntax.ctx_uvar_should_check FStar_Syntax_Syntax.Allow_unresolved) || (

let uu____24129 = (FStar_Syntax_Unionfind.find imp.imp_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____24129) with
| FStar_Pervasives_Native.Some (uu____24133) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end))))))
end
| uu____24136 -> begin
false
end))


let is_trivial_guard_formula : guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {guard_f = FStar_TypeChecker_Common.Trivial; deferred = uu____24146; univ_ineqs = uu____24147; implicits = uu____24148} -> begin
true
end
| uu____24160 -> begin
false
end))


let trivial_guard : guard_t = {guard_f = FStar_TypeChecker_Common.Trivial; deferred = []; univ_ineqs = (([]), ([])); implicits = []}


let abstract_guard_n : FStar_Syntax_Syntax.binder Prims.list  ->  guard_t  ->  guard_t = (fun bs g -> (match (g.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let f' = (FStar_Syntax_Util.abs bs f (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in (

let uu___274_24191 = g
in {guard_f = FStar_TypeChecker_Common.NonTrivial (f'); deferred = uu___274_24191.deferred; univ_ineqs = uu___274_24191.univ_ineqs; implicits = uu___274_24191.implicits}))
end))


let abstract_guard : FStar_Syntax_Syntax.binder  ->  guard_t  ->  guard_t = (fun b g -> (abstract_guard_n ((b)::[]) g))


let def_check_vars_in_set : FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.term  ->  unit = (fun rng msg vset t -> (

let uu____24230 = (FStar_Options.defensive ())
in (match (uu____24230) with
| true -> begin
(

let s = (FStar_Syntax_Free.names t)
in (

let uu____24236 = (

let uu____24238 = (

let uu____24240 = (FStar_Util.set_difference s vset)
in (FStar_All.pipe_left FStar_Util.set_is_empty uu____24240))
in (not (uu____24238)))
in (match (uu____24236) with
| true -> begin
(

let uu____24247 = (

let uu____24253 = (

let uu____24255 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____24257 = (

let uu____24259 = (FStar_Util.set_elements s)
in (FStar_All.pipe_right uu____24259 (FStar_Syntax_Print.bvs_to_string ",\n\t")))
in (FStar_Util.format3 "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n" msg uu____24255 uu____24257)))
in ((FStar_Errors.Warning_Defensive), (uu____24253)))
in (FStar_Errors.log_issue rng uu____24247))
end
| uu____24268 -> begin
()
end)))
end
| uu____24270 -> begin
()
end)))


let def_check_closed_in : FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  unit = (fun rng msg l t -> (

let uu____24299 = (

let uu____24301 = (FStar_Options.defensive ())
in (not (uu____24301)))
in (match (uu____24299) with
| true -> begin
()
end
| uu____24304 -> begin
(

let uu____24306 = (FStar_Util.as_set l FStar_Syntax_Syntax.order_bv)
in (def_check_vars_in_set rng msg uu____24306 t))
end)))


let def_check_closed_in_env : FStar_Range.range  ->  Prims.string  ->  env  ->  FStar_Syntax_Syntax.term  ->  unit = (fun rng msg e t -> (

let uu____24332 = (

let uu____24334 = (FStar_Options.defensive ())
in (not (uu____24334)))
in (match (uu____24332) with
| true -> begin
()
end
| uu____24337 -> begin
(

let uu____24339 = (bound_vars e)
in (def_check_closed_in rng msg uu____24339 t))
end)))


let def_check_guard_wf : FStar_Range.range  ->  Prims.string  ->  env  ->  guard_t  ->  unit = (fun rng msg env g -> (match (g.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(def_check_closed_in_env rng msg env f)
end))


let apply_guard : guard_t  ->  FStar_Syntax_Syntax.term  ->  guard_t = (fun g e -> (match (g.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___275_24378 = g
in (

let uu____24379 = (

let uu____24380 = (

let uu____24381 = (

let uu____24388 = (

let uu____24389 = (

let uu____24406 = (

let uu____24417 = (FStar_Syntax_Syntax.as_arg e)
in (uu____24417)::[])
in ((f), (uu____24406)))
in FStar_Syntax_Syntax.Tm_app (uu____24389))
in (FStar_Syntax_Syntax.mk uu____24388))
in (uu____24381 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _0_2 -> FStar_TypeChecker_Common.NonTrivial (_0_2)) uu____24380))
in {guard_f = uu____24379; deferred = uu___275_24378.deferred; univ_ineqs = uu___275_24378.univ_ineqs; implicits = uu___275_24378.implicits}))
end))


let map_guard : guard_t  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  guard_t = (fun g map1 -> (match (g.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___276_24474 = g
in (

let uu____24475 = (

let uu____24476 = (map1 f)
in FStar_TypeChecker_Common.NonTrivial (uu____24476))
in {guard_f = uu____24475; deferred = uu___276_24474.deferred; univ_ineqs = uu___276_24474.univ_ineqs; implicits = uu___276_24474.implicits}))
end))


let always_map_guard : guard_t  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  guard_t = (fun g map1 -> (match (g.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let uu___277_24493 = g
in (

let uu____24494 = (

let uu____24495 = (map1 FStar_Syntax_Util.t_true)
in FStar_TypeChecker_Common.NonTrivial (uu____24495))
in {guard_f = uu____24494; deferred = uu___277_24493.deferred; univ_ineqs = uu___277_24493.univ_ineqs; implicits = uu___277_24493.implicits}))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___278_24497 = g
in (

let uu____24498 = (

let uu____24499 = (map1 f)
in FStar_TypeChecker_Common.NonTrivial (uu____24499))
in {guard_f = uu____24498; deferred = uu___278_24497.deferred; univ_ineqs = uu___278_24497.univ_ineqs; implicits = uu___278_24497.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____24506) -> begin
(failwith "impossible")
end))


let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.Trivial, g) -> begin
g
end
| (g, FStar_TypeChecker_Common.Trivial) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let uu____24523 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (uu____24523))
end))


let check_trivial : FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (

let uu____24530 = (

let uu____24531 = (FStar_Syntax_Util.unmeta t)
in uu____24531.FStar_Syntax_Syntax.n)
in (match (uu____24530) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____24535 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end)))


let imp_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.Trivial, g) -> begin
g
end
| (g, FStar_TypeChecker_Common.Trivial) -> begin
FStar_TypeChecker_Common.Trivial
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let imp = (FStar_Syntax_Util.mk_imp f1 f2)
in (check_trivial imp))
end))


let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  guard_t  ->  guard_t  ->  guard_t = (fun f g1 g2 -> (

let uu____24578 = (f g1.guard_f g2.guard_f)
in {guard_f = uu____24578; deferred = (FStar_List.append g1.deferred g2.deferred); univ_ineqs = (((FStar_List.append (FStar_Pervasives_Native.fst g1.univ_ineqs) (FStar_Pervasives_Native.fst g2.univ_ineqs))), ((FStar_List.append (FStar_Pervasives_Native.snd g1.univ_ineqs) (FStar_Pervasives_Native.snd g2.univ_ineqs)))); implicits = (FStar_List.append g1.implicits g2.implicits)}))


let conj_guard : guard_t  ->  guard_t  ->  guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : guard_t  ->  guard_t  ->  guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let conj_guards : guard_t Prims.list  ->  guard_t = (fun gs -> (FStar_List.fold_left conj_guard trivial_guard gs))


let close_guard_univs : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.binders  ->  guard_t  ->  guard_t = (fun us bs g -> (match (g.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let f1 = (FStar_List.fold_right2 (fun u b f1 -> (

let uu____24673 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____24673) with
| true -> begin
f1
end
| uu____24676 -> begin
(FStar_Syntax_Util.mk_forall u (FStar_Pervasives_Native.fst b) f1)
end))) us bs f)
in (

let uu___279_24680 = g
in {guard_f = FStar_TypeChecker_Common.NonTrivial (f1); deferred = uu___279_24680.deferred; univ_ineqs = uu___279_24680.univ_ineqs; implicits = uu___279_24680.implicits}))
end))


let close_forall : env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____24714 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____24714) with
| true -> begin
f1
end
| uu____24717 -> begin
(

let u = (env.universe_of env (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Util.mk_forall u (FStar_Pervasives_Native.fst b) f1))
end))) bs f))


let close_guard : env  ->  FStar_Syntax_Syntax.binders  ->  guard_t  ->  guard_t = (fun env binders g -> (match (g.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___280_24741 = g
in (

let uu____24742 = (

let uu____24743 = (close_forall env binders f)
in FStar_TypeChecker_Common.NonTrivial (uu____24743))
in {guard_f = uu____24742; deferred = uu___280_24741.deferred; univ_ineqs = uu___280_24741.univ_ineqs; implicits = uu___280_24741.implicits}))
end))


let new_implicit_var_aux : Prims.string  ->  FStar_Range.range  ->  env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.should_check_uvar  ->  (FStar_Dyn.dyn * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar * FStar_Range.range) Prims.list * guard_t) = (fun reason r env k should_check meta -> (

let uu____24801 = (FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid)
in (match (uu____24801) with
| FStar_Pervasives_Native.Some ((uu____24826)::((tm, uu____24828))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (trivial_guard)))
end
| uu____24892 -> begin
(

let binders = (all_binders env)
in (

let gamma = env.gamma
in (

let ctx_uvar = (

let uu____24910 = (FStar_Syntax_Unionfind.fresh ())
in {FStar_Syntax_Syntax.ctx_uvar_head = uu____24910; FStar_Syntax_Syntax.ctx_uvar_gamma = gamma; FStar_Syntax_Syntax.ctx_uvar_binders = binders; FStar_Syntax_Syntax.ctx_uvar_typ = k; FStar_Syntax_Syntax.ctx_uvar_reason = reason; FStar_Syntax_Syntax.ctx_uvar_should_check = should_check; FStar_Syntax_Syntax.ctx_uvar_range = r; FStar_Syntax_Syntax.ctx_uvar_meta = meta})
in ((FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r true gamma binders);
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((ctx_uvar), ((([]), (FStar_Syntax_Syntax.NoUseRange)))))) FStar_Pervasives_Native.None r)
in (

let imp = {imp_reason = reason; imp_uvar = ctx_uvar; imp_tm = t; imp_range = r}
in (

let g = (

let uu___281_24942 = trivial_guard
in {guard_f = uu___281_24942.guard_f; deferred = uu___281_24942.deferred; univ_ineqs = uu___281_24942.univ_ineqs; implicits = (imp)::[]})
in ((t), ((((ctx_uvar), (r)))::[]), (g)))));
))))
end)))


let dummy_solver : solver_t = {init = (fun uu____24960 -> ()); push = (fun uu____24962 -> ()); pop = (fun uu____24965 -> ()); snapshot = (fun uu____24968 -> (((((Prims.parse_int "0")), ((Prims.parse_int "0")), ((Prims.parse_int "0")))), (()))); rollback = (fun uu____24987 uu____24988 -> ()); encode_modul = (fun uu____25003 uu____25004 -> ()); encode_sig = (fun uu____25007 uu____25008 -> ()); preprocess = (fun e g -> (

let uu____25014 = (

let uu____25021 = (FStar_Options.peek ())
in ((e), (g), (uu____25021)))
in (uu____25014)::[])); solve = (fun uu____25037 uu____25038 uu____25039 -> ()); finish = (fun uu____25046 -> ()); refresh = (fun uu____25048 -> ())}





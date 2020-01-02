
open Prims
open FStar_Pervasives

let print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar  ->  Prims.string = (fun ctx_uvar -> (FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar))


type lstring =
Prims.string FStar_Thunk.t

type uvi =
| TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)


let uu___is_TERM : uvi  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TERM (_0) -> begin
true
end
| uu____49 -> begin
false
end))


let __proj__TERM__item___0 : uvi  ->  (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| TERM (_0) -> begin
_0
end))


let uu___is_UNIV : uvi  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UNIV (_0) -> begin
true
end
| uu____84 -> begin
false
end))


let __proj__UNIV__item___0 : uvi  ->  (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe) = (fun projectee -> (match (projectee) with
| UNIV (_0) -> begin
_0
end))

type worklist =
{attempting : FStar_TypeChecker_Common.probs; wl_deferred : (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list; ctr : Prims.int; defer_ok : Prims.bool; smt_ok : Prims.bool; umax_heuristic_ok : Prims.bool; tcenv : FStar_TypeChecker_Env.env; wl_implicits : FStar_TypeChecker_Common.implicits}


let __proj__Mkworklist__item__attempting : worklist  ->  FStar_TypeChecker_Common.probs = (fun projectee -> (match (projectee) with
| {attempting = attempting; wl_deferred = wl_deferred; ctr = ctr; defer_ok = defer_ok; smt_ok = smt_ok; umax_heuristic_ok = umax_heuristic_ok; tcenv = tcenv; wl_implicits = wl_implicits} -> begin
attempting
end))


let __proj__Mkworklist__item__wl_deferred : worklist  ->  (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list = (fun projectee -> (match (projectee) with
| {attempting = attempting; wl_deferred = wl_deferred; ctr = ctr; defer_ok = defer_ok; smt_ok = smt_ok; umax_heuristic_ok = umax_heuristic_ok; tcenv = tcenv; wl_implicits = wl_implicits} -> begin
wl_deferred
end))


let __proj__Mkworklist__item__ctr : worklist  ->  Prims.int = (fun projectee -> (match (projectee) with
| {attempting = attempting; wl_deferred = wl_deferred; ctr = ctr; defer_ok = defer_ok; smt_ok = smt_ok; umax_heuristic_ok = umax_heuristic_ok; tcenv = tcenv; wl_implicits = wl_implicits} -> begin
ctr
end))


let __proj__Mkworklist__item__defer_ok : worklist  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {attempting = attempting; wl_deferred = wl_deferred; ctr = ctr; defer_ok = defer_ok; smt_ok = smt_ok; umax_heuristic_ok = umax_heuristic_ok; tcenv = tcenv; wl_implicits = wl_implicits} -> begin
defer_ok
end))


let __proj__Mkworklist__item__smt_ok : worklist  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {attempting = attempting; wl_deferred = wl_deferred; ctr = ctr; defer_ok = defer_ok; smt_ok = smt_ok; umax_heuristic_ok = umax_heuristic_ok; tcenv = tcenv; wl_implicits = wl_implicits} -> begin
smt_ok
end))


let __proj__Mkworklist__item__umax_heuristic_ok : worklist  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {attempting = attempting; wl_deferred = wl_deferred; ctr = ctr; defer_ok = defer_ok; smt_ok = smt_ok; umax_heuristic_ok = umax_heuristic_ok; tcenv = tcenv; wl_implicits = wl_implicits} -> begin
umax_heuristic_ok
end))


let __proj__Mkworklist__item__tcenv : worklist  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {attempting = attempting; wl_deferred = wl_deferred; ctr = ctr; defer_ok = defer_ok; smt_ok = smt_ok; umax_heuristic_ok = umax_heuristic_ok; tcenv = tcenv; wl_implicits = wl_implicits} -> begin
tcenv
end))


let __proj__Mkworklist__item__wl_implicits : worklist  ->  FStar_TypeChecker_Common.implicits = (fun projectee -> (match (projectee) with
| {attempting = attempting; wl_deferred = wl_deferred; ctr = ctr; defer_ok = defer_ok; smt_ok = smt_ok; umax_heuristic_ok = umax_heuristic_ok; tcenv = tcenv; wl_implicits = wl_implicits} -> begin
wl_implicits
end))


let new_uvar : Prims.string  ->  worklist  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.binding Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.should_check_uvar  ->  (FStar_Dyn.dyn * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term * worklist) = (fun reason wl r gamma binders k should_check meta -> (

let ctx_uvar = (

let uu____515 = (FStar_Syntax_Unionfind.fresh ())
in {FStar_Syntax_Syntax.ctx_uvar_head = uu____515; FStar_Syntax_Syntax.ctx_uvar_gamma = gamma; FStar_Syntax_Syntax.ctx_uvar_binders = binders; FStar_Syntax_Syntax.ctx_uvar_typ = k; FStar_Syntax_Syntax.ctx_uvar_reason = reason; FStar_Syntax_Syntax.ctx_uvar_should_check = should_check; FStar_Syntax_Syntax.ctx_uvar_range = r; FStar_Syntax_Syntax.ctx_uvar_meta = meta})
in ((FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r true gamma binders);
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((ctx_uvar), ((([]), (FStar_Syntax_Syntax.NoUseRange)))))) FStar_Pervasives_Native.None r)
in (

let imp = {FStar_TypeChecker_Common.imp_reason = reason; FStar_TypeChecker_Common.imp_uvar = ctx_uvar; FStar_TypeChecker_Common.imp_tm = t; FStar_TypeChecker_Common.imp_range = r}
in ((ctx_uvar), (t), ((

let uu___71_547 = wl
in {attempting = uu___71_547.attempting; wl_deferred = uu___71_547.wl_deferred; ctr = uu___71_547.ctr; defer_ok = uu___71_547.defer_ok; smt_ok = uu___71_547.smt_ok; umax_heuristic_ok = uu___71_547.umax_heuristic_ok; tcenv = uu___71_547.tcenv; wl_implicits = (imp)::wl.wl_implicits})))));
)))


let copy_uvar : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  worklist  ->  (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term * worklist) = (fun u bs t wl -> (

let env = (

let uu___77_580 = wl.tcenv
in {FStar_TypeChecker_Env.solver = uu___77_580.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___77_580.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___77_580.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = u.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_TypeChecker_Env.gamma_sig = uu___77_580.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___77_580.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___77_580.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___77_580.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___77_580.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___77_580.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___77_580.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___77_580.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___77_580.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___77_580.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___77_580.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___77_580.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___77_580.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___77_580.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___77_580.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___77_580.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___77_580.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___77_580.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___77_580.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___77_580.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___77_580.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___77_580.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___77_580.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___77_580.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___77_580.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___77_580.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___77_580.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___77_580.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___77_580.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___77_580.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___77_580.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___77_580.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___77_580.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___77_580.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___77_580.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___77_580.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___77_580.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___77_580.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___77_580.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___77_580.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___77_580.FStar_TypeChecker_Env.erasable_types_tab})
in (

let env1 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____582 = (FStar_TypeChecker_Env.all_binders env1)
in (new_uvar (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl u.FStar_Syntax_Syntax.ctx_uvar_range env1.FStar_TypeChecker_Env.gamma uu____582 t u.FStar_Syntax_Syntax.ctx_uvar_should_check u.FStar_Syntax_Syntax.ctx_uvar_meta)))))

type solution =
| Success of (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits)
| Failed of (FStar_TypeChecker_Common.prob * lstring)


let uu___is_Success : solution  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
true
end
| uu____643 -> begin
false
end))


let __proj__Success__item___0 : solution  ->  (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits) = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
_0
end))


let uu___is_Failed : solution  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Failed (_0) -> begin
true
end
| uu____678 -> begin
false
end))


let __proj__Failed__item___0 : solution  ->  (FStar_TypeChecker_Common.prob * lstring) = (fun projectee -> (match (projectee) with
| Failed (_0) -> begin
_0
end))

type variance =
| COVARIANT
| CONTRAVARIANT
| INVARIANT


let uu___is_COVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| COVARIANT -> begin
true
end
| uu____708 -> begin
false
end))


let uu___is_CONTRAVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CONTRAVARIANT -> begin
true
end
| uu____719 -> begin
false
end))


let uu___is_INVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| INVARIANT -> begin
true
end
| uu____730 -> begin
false
end))


type tprob =
FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem


type cprob =
FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem


type 'a problem_t =
'a FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun uu___0_748 -> (match (uu___0_748) with
| FStar_TypeChecker_Common.EQ -> begin
"="
end
| FStar_TypeChecker_Common.SUB -> begin
"<:"
end
| FStar_TypeChecker_Common.SUBINV -> begin
":>"
end))


let term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (

let uu____760 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____760) with
| (head1, args) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(

let uu____823 = (FStar_Syntax_Print.ctx_uvar_to_string u)
in (

let uu____825 = (match ((FStar_Pervasives_Native.fst s)) with
| [] -> begin
""
end
| s1 -> begin
(

let uu____840 = (

let uu____842 = (FStar_List.hd s1)
in (FStar_Syntax_Print.subst_to_string uu____842))
in (FStar_Util.format1 "@<%s>" uu____840))
end)
in (

let uu____846 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "%s%s %s" uu____823 uu____825 uu____846))))
end
| uu____849 -> begin
(FStar_Syntax_Print.term_to_string t)
end)
end)))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env uu___1_861 -> (match (uu___1_861) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____866 = (

let uu____870 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____872 = (

let uu____876 = (term_to_string p.FStar_TypeChecker_Common.lhs)
in (

let uu____878 = (

let uu____882 = (

let uu____886 = (term_to_string p.FStar_TypeChecker_Common.rhs)
in (uu____886)::[])
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::uu____882)
in (uu____876)::uu____878))
in (uu____870)::uu____872))
in (FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____866))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____897 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____899 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____901 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____897 uu____899 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____901))))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env uu___2_915 -> (match (uu___2_915) with
| UNIV (u, t) -> begin
(

let x = (

let uu____921 = (FStar_Options.hide_uvar_nums ())
in (match (uu____921) with
| true -> begin
"?"
end
| uu____926 -> begin
(

let uu____928 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____928 FStar_Util.string_of_int))
end))
in (

let uu____932 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x uu____932)))
end
| TERM (u, t) -> begin
(

let x = (

let uu____939 = (FStar_Options.hide_uvar_nums ())
in (match (uu____939) with
| true -> begin
"?"
end
| uu____944 -> begin
(

let uu____946 = (FStar_Syntax_Unionfind.uvar_id u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_right uu____946 FStar_Util.string_of_int))
end))
in (

let uu____950 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x uu____950)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (

let uu____969 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right uu____969 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (

let uu____990 = (

let uu____994 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right uu____994 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right uu____990 (FStar_String.concat ", "))))


let args_to_string : 'Auu____1013 . (FStar_Syntax_Syntax.term * 'Auu____1013) Prims.list  ->  Prims.string = (fun args -> (

let uu____1032 = (FStar_All.pipe_right args (FStar_List.map (fun uu____1053 -> (match (uu____1053) with
| (x, uu____1060) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____1032 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = true; smt_ok = true; umax_heuristic_ok = true; tcenv = env; wl_implicits = []})


let giveup : FStar_TypeChecker_Env.env  ->  lstring  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> ((

let uu____1100 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____1100) with
| true -> begin
(

let uu____1105 = (FStar_Thunk.force reason)
in (

let uu____1108 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" uu____1105 uu____1108)))
end
| uu____1111 -> begin
()
end));
Failed (((prob), (reason)));
))


let giveup_lit : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (

let uu____1131 = (FStar_Thunk.mk (fun uu____1134 -> reason))
in (giveup env uu____1131 prob)))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun uu___3_1140 -> (match (uu___3_1140) with
| FStar_TypeChecker_Common.EQ -> begin
FStar_TypeChecker_Common.EQ
end
| FStar_TypeChecker_Common.SUB -> begin
FStar_TypeChecker_Common.SUBINV
end
| FStar_TypeChecker_Common.SUBINV -> begin
FStar_TypeChecker_Common.SUB
end))


let invert : 'Auu____1146 . 'Auu____1146 FStar_TypeChecker_Common.problem  ->  'Auu____1146 FStar_TypeChecker_Common.problem = (fun p -> (

let uu___141_1158 = p
in {FStar_TypeChecker_Common.pid = uu___141_1158.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = uu___141_1158.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___141_1158.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___141_1158.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___141_1158.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___141_1158.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___141_1158.FStar_TypeChecker_Common.rank}))


let maybe_invert : 'Auu____1166 . 'Auu____1166 FStar_TypeChecker_Common.problem  ->  'Auu____1166 FStar_TypeChecker_Common.problem = (fun p -> (match ((Prims.op_Equality p.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUBINV)) with
| true -> begin
(invert p)
end
| uu____1179 -> begin
p
end))


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___4_1186 -> (match (uu___4_1186) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _1192 -> FStar_TypeChecker_Common.TProb (_1192)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _1198 -> FStar_TypeChecker_Common.CProb (_1198)))
end))


let make_prob_eq : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___5_1204 -> (match (uu___5_1204) with
| FStar_TypeChecker_Common.TProb (p) -> begin
FStar_TypeChecker_Common.TProb ((

let uu___153_1210 = p
in {FStar_TypeChecker_Common.pid = uu___153_1210.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___153_1210.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___153_1210.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___153_1210.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___153_1210.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___153_1210.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___153_1210.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___153_1210.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___153_1210.FStar_TypeChecker_Common.rank}))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
FStar_TypeChecker_Common.CProb ((

let uu___157_1218 = p
in {FStar_TypeChecker_Common.pid = uu___157_1218.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___157_1218.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___157_1218.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___157_1218.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___157_1218.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___157_1218.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___157_1218.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___157_1218.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___157_1218.FStar_TypeChecker_Common.rank}))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel uu___6_1231 -> (match (uu___6_1231) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun uu___7_1238 -> (match (uu___7_1238) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun uu___8_1251 -> (match (uu___8_1251) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun uu___9_1266 -> (match (uu___9_1266) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun uu___10_1281 -> (match (uu___10_1281) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_element : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option = (fun uu___11_1295 -> (match (uu___11_1295) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.element
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.element
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term = (fun uu___12_1309 -> (match (uu___12_1309) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_guard_uvar : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.ctx_uvar = (fun uu___13_1321 -> (match (uu___13_1321) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard_uvar
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard_uvar
end))


let def_scope_wf : 'Auu____1337 . Prims.string  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.bv * 'Auu____1337) Prims.list  ->  unit = (fun msg rng r -> (

let uu____1367 = (

let uu____1369 = (FStar_Options.defensive ())
in (not (uu____1369)))
in (match (uu____1367) with
| true -> begin
()
end
| uu____1372 -> begin
(

let rec aux = (fun prev next -> (match (next) with
| [] -> begin
()
end
| ((bv, uu____1406))::bs -> begin
((FStar_TypeChecker_Env.def_check_closed_in rng msg prev bv.FStar_Syntax_Syntax.sort);
(aux (FStar_List.append prev ((bv)::[])) bs);
)
end))
in (aux [] r))
end)))


let p_scope : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun prob -> (

let r = (match (prob) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____1453 = (match ((p_element prob)) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____1477 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1477)::[])
end)
in (FStar_List.append p.FStar_TypeChecker_Common.logical_guard_uvar.FStar_Syntax_Syntax.ctx_uvar_binders uu____1453))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____1505 = (match ((p_element prob)) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____1529 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1529)::[])
end)
in (FStar_List.append p.FStar_TypeChecker_Common.logical_guard_uvar.FStar_Syntax_Syntax.ctx_uvar_binders uu____1505))
end)
in ((def_scope_wf "p_scope" (p_loc prob) r);
r;
)))


let def_check_scoped : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  unit = (fun msg prob phi -> (

let uu____1576 = (

let uu____1578 = (FStar_Options.defensive ())
in (not (uu____1578)))
in (match (uu____1576) with
| true -> begin
()
end
| uu____1581 -> begin
(

let uu____1583 = (

let uu____1586 = (p_scope prob)
in (FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst) uu____1586))
in (FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg uu____1583 phi))
end)))


let def_check_scoped_comp : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  unit = (fun msg prob comp -> (

let uu____1635 = (

let uu____1637 = (FStar_Options.defensive ())
in (not (uu____1637)))
in (match (uu____1635) with
| true -> begin
()
end
| uu____1640 -> begin
(

let uu____1642 = (FStar_Syntax_Util.arrow [] comp)
in (def_check_scoped msg prob uu____1642))
end)))


let def_check_prob : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  unit = (fun msg prob -> (

let uu____1662 = (

let uu____1664 = (FStar_Options.defensive ())
in (not (uu____1664)))
in (match (uu____1662) with
| true -> begin
()
end
| uu____1667 -> begin
(

let msgf = (fun m -> (

let uu____1678 = (

let uu____1680 = (

let uu____1682 = (FStar_Util.string_of_int (p_pid prob))
in (Prims.op_Hat uu____1682 (Prims.op_Hat "." m)))
in (Prims.op_Hat "." uu____1680))
in (Prims.op_Hat msg uu____1678)))
in ((

let uu____1687 = (msgf "scope")
in (

let uu____1690 = (p_scope prob)
in (def_scope_wf uu____1687 (p_loc prob) uu____1690)));
(

let uu____1702 = (msgf "guard")
in (def_check_scoped uu____1702 prob (p_guard prob)));
(match (prob) with
| FStar_TypeChecker_Common.TProb (p) -> begin
((

let uu____1709 = (msgf "lhs")
in (def_check_scoped uu____1709 prob p.FStar_TypeChecker_Common.lhs));
(

let uu____1712 = (msgf "rhs")
in (def_check_scoped uu____1712 prob p.FStar_TypeChecker_Common.rhs));
)
end
| FStar_TypeChecker_Common.CProb (p) -> begin
((

let uu____1719 = (msgf "lhs")
in (def_check_scoped_comp uu____1719 prob p.FStar_TypeChecker_Common.lhs));
(

let uu____1722 = (msgf "rhs")
in (def_check_scoped_comp uu____1722 prob p.FStar_TypeChecker_Common.rhs));
)
end);
))
end)))


let singleton : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun wl prob smt_ok -> (

let uu___250_1743 = wl
in {attempting = (prob)::[]; wl_deferred = uu___250_1743.wl_deferred; ctr = uu___250_1743.ctr; defer_ok = uu___250_1743.defer_ok; smt_ok = smt_ok; umax_heuristic_ok = uu___250_1743.umax_heuristic_ok; tcenv = uu___250_1743.tcenv; wl_implicits = uu___250_1743.wl_implicits}))


let wl_of_guard : 'Auu____1751 . FStar_TypeChecker_Env.env  ->  ('Auu____1751 * FStar_TypeChecker_Common.prob) Prims.list  ->  worklist = (fun env g -> (

let uu___254_1774 = (empty_worklist env)
in (

let uu____1775 = (FStar_List.map FStar_Pervasives_Native.snd g)
in {attempting = uu____1775; wl_deferred = uu___254_1774.wl_deferred; ctr = uu___254_1774.ctr; defer_ok = uu___254_1774.defer_ok; smt_ok = uu___254_1774.smt_ok; umax_heuristic_ok = uu___254_1774.umax_heuristic_ok; tcenv = uu___254_1774.tcenv; wl_implicits = uu___254_1774.wl_implicits})))


let defer : lstring  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu___259_1796 = wl
in {attempting = uu___259_1796.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = uu___259_1796.ctr; defer_ok = uu___259_1796.defer_ok; smt_ok = uu___259_1796.smt_ok; umax_heuristic_ok = uu___259_1796.umax_heuristic_ok; tcenv = uu___259_1796.tcenv; wl_implicits = uu___259_1796.wl_implicits}))


let defer_lit : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu____1823 = (FStar_Thunk.mkv reason)
in (defer uu____1823 prob wl)))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> ((FStar_List.iter (def_check_prob "attempt") probs);
(

let uu___267_1842 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = uu___267_1842.wl_deferred; ctr = uu___267_1842.ctr; defer_ok = uu___267_1842.defer_ok; smt_ok = uu___267_1842.smt_ok; umax_heuristic_ok = uu___267_1842.umax_heuristic_ok; tcenv = uu___267_1842.tcenv; wl_implicits = uu___267_1842.wl_implicits});
))


let mk_eq2 : 'Auu____1856 . worklist  ->  FStar_TypeChecker_Env.env  ->  'Auu____1856  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * worklist) = (fun wl env prob t1 t2 -> (

let uu____1890 = (FStar_Syntax_Util.type_u ())
in (match (uu____1890) with
| (t_type, u) -> begin
(

let binders = (FStar_TypeChecker_Env.all_binders env)
in (

let uu____1902 = (new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos env.FStar_TypeChecker_Env.gamma binders t_type FStar_Syntax_Syntax.Allow_unresolved FStar_Pervasives_Native.None)
in (match (uu____1902) with
| (uu____1920, tt, wl1) -> begin
(

let uu____1923 = (FStar_Syntax_Util.mk_eq2 u tt t1 t2)
in ((uu____1923), (wl1)))
end)))
end)))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___14_1929 -> (match (uu___14_1929) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _1935 -> FStar_TypeChecker_Common.TProb (_1935)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _1941 -> FStar_TypeChecker_Common.CProb (_1941)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> (

let uu____1949 = (FStar_All.pipe_right (p_reason p) FStar_List.length)
in (Prims.op_Equality uu____1949 (Prims.parse_int "1"))))


let next_pid : unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____1969 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
)))


let mk_problem : 'Auu____2011 . worklist  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_TypeChecker_Common.prob  ->  'Auu____2011  ->  FStar_TypeChecker_Common.rel  ->  'Auu____2011  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  Prims.string  ->  ('Auu____2011 FStar_TypeChecker_Common.problem * worklist) = (fun wl scope orig lhs rel rhs elt reason -> (

let scope1 = (match (elt) with
| FStar_Pervasives_Native.None -> begin
scope
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____2098 = (

let uu____2107 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2107)::[])
in (FStar_List.append scope uu____2098))
end)
in (

let bs = (FStar_List.append (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders scope1)
in (

let gamma = (

let uu____2150 = (

let uu____2153 = (FStar_List.map (fun b -> FStar_Syntax_Syntax.Binding_var ((FStar_Pervasives_Native.fst b))) scope1)
in (FStar_List.rev uu____2153))
in (FStar_List.append uu____2150 (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma))
in (

let uu____2172 = (new_uvar (Prims.op_Hat "mk_problem: logical guard for " reason) wl FStar_Range.dummyRange gamma bs FStar_Syntax_Util.ktype0 FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None)
in (match (uu____2172) with
| (ctx_uvar, lg, wl1) -> begin
(

let prob = (

let uu____2198 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____2198; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = lg; FStar_TypeChecker_Common.logical_guard_uvar = ctx_uvar; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})
in ((prob), (wl1)))
end))))))


let mk_t_problem : worklist  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_TypeChecker_Common.prob * worklist) = (fun wl scope orig lhs rel rhs elt reason -> ((def_check_prob (Prims.op_Hat reason ".mk_t.arg") orig);
(

let uu____2272 = (mk_problem wl scope orig lhs rel rhs elt reason)
in (match (uu____2272) with
| (p, wl1) -> begin
((def_check_prob (Prims.op_Hat reason ".mk_t") (FStar_TypeChecker_Common.TProb (p)));
((FStar_TypeChecker_Common.TProb (p)), (wl1));
)
end));
))


let mk_c_problem : worklist  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_TypeChecker_Common.prob * worklist) = (fun wl scope orig lhs rel rhs elt reason -> ((def_check_prob (Prims.op_Hat reason ".mk_c.arg") orig);
(

let uu____2360 = (mk_problem wl scope orig lhs rel rhs elt reason)
in (match (uu____2360) with
| (p, wl1) -> begin
((def_check_prob (Prims.op_Hat reason ".mk_c") (FStar_TypeChecker_Common.CProb (p)));
((FStar_TypeChecker_Common.CProb (p)), (wl1));
)
end));
))


let new_problem : 'Auu____2398 . worklist  ->  FStar_TypeChecker_Env.env  ->  'Auu____2398  ->  FStar_TypeChecker_Common.rel  ->  'Auu____2398  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  Prims.string  ->  ('Auu____2398 FStar_TypeChecker_Common.problem * worklist) = (fun wl env lhs rel rhs subject loc reason -> (

let lg_ty = (match (subject) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let bs = (

let uu____2466 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2466)::[])
in (

let uu____2485 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow bs uu____2485)))
end)
in (

let uu____2488 = (

let uu____2495 = (FStar_TypeChecker_Env.all_binders env)
in (new_uvar (Prims.op_Hat "new_problem: logical guard for " reason) (

let uu___350_2506 = wl
in {attempting = uu___350_2506.attempting; wl_deferred = uu___350_2506.wl_deferred; ctr = uu___350_2506.ctr; defer_ok = uu___350_2506.defer_ok; smt_ok = uu___350_2506.smt_ok; umax_heuristic_ok = uu___350_2506.umax_heuristic_ok; tcenv = env; wl_implicits = uu___350_2506.wl_implicits}) loc env.FStar_TypeChecker_Env.gamma uu____2495 lg_ty FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None))
in (match (uu____2488) with
| (ctx_uvar, lg, wl1) -> begin
(

let lg1 = (match (subject) with
| FStar_Pervasives_Native.None -> begin
lg
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____2524 = (

let uu____2529 = (

let uu____2530 = (

let uu____2539 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____2539))
in (uu____2530)::[])
in (FStar_Syntax_Syntax.mk_Tm_app lg uu____2529))
in (uu____2524 FStar_Pervasives_Native.None loc))
end)
in (

let prob = (

let uu____2567 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____2567; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = subject; FStar_TypeChecker_Common.logical_guard = lg1; FStar_TypeChecker_Common.logical_guard_uvar = ctx_uvar; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})
in ((prob), (wl1))))
end))))


let problem_using_guard : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  Prims.string  ->  FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem = (fun orig lhs rel rhs elt reason -> (

let p = (

let uu____2615 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____2615; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.logical_guard_uvar = (p_guard_uvar orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})
in ((def_check_prob reason (FStar_TypeChecker_Common.TProb (p)));
p;
)))


let guard_on_element : 'Auu____2630 . worklist  ->  'Auu____2630 FStar_TypeChecker_Common.problem  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun wl problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| FStar_Pervasives_Native.None -> begin
(

let u = (wl.tcenv.FStar_TypeChecker_Env.universe_of wl.tcenv x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Util.mk_forall u x phi))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____2663 = (

let uu____2666 = (

let uu____2667 = (

let uu____2674 = (FStar_Syntax_Syntax.bv_to_name e)
in ((x), (uu____2674)))
in FStar_Syntax_Syntax.NT (uu____2667))
in (uu____2666)::[])
in (FStar_Syntax_Subst.subst uu____2663 phi))
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  lstring  ->  Prims.string = (fun env d s -> (

let uu____2696 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))))
in (match (uu____2696) with
| true -> begin
(

let uu____2704 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (

let uu____2707 = (prob_to_string env d)
in (

let uu____2709 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (

let uu____2716 = (FStar_Thunk.force s)
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" uu____2704 uu____2707 uu____2709 uu____2716)))))
end
| uu____2720 -> begin
(

let d1 = (maybe_invert_p d)
in (

let rel = (match ((p_rel d1)) with
| FStar_TypeChecker_Common.EQ -> begin
"equal to"
end
| FStar_TypeChecker_Common.SUB -> begin
"a subtype of"
end
| uu____2728 -> begin
(failwith "impossible")
end)
in (

let uu____2731 = (match (d1) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____2747 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (

let uu____2749 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((uu____2747), (uu____2749))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____2756 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (

let uu____2758 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((uu____2756), (uu____2758))))
end)
in (match (uu____2731) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___15_2786 -> (match (uu___15_2786) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Syntax_Unionfind.univ_union u u')
end
| uu____2798 -> begin
(FStar_Syntax_Unionfind.univ_change u t)
end)
end
| TERM (u, t) -> begin
((

let uu____2802 = (FStar_List.map FStar_Pervasives_Native.fst u.FStar_Syntax_Syntax.ctx_uvar_binders)
in (FStar_TypeChecker_Env.def_check_closed_in t.FStar_Syntax_Syntax.pos "commit" uu____2802 t));
(FStar_Syntax_Util.set_uvar u.FStar_Syntax_Syntax.ctx_uvar_head t);
)
end)))))


let find_term_uvar : FStar_Syntax_Syntax.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun uv s -> (FStar_Util.find_map s (fun uu___16_2833 -> (match (uu___16_2833) with
| UNIV (uu____2836) -> begin
FStar_Pervasives_Native.None
end
| TERM (u, t) -> begin
(

let uu____2843 = (FStar_Syntax_Unionfind.equiv uv u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____2843) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____2848 -> begin
FStar_Pervasives_Native.None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe_uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun u s -> (FStar_Util.find_map s (fun uu___17_2871 -> (match (uu___17_2871) with
| UNIV (u', t) -> begin
(

let uu____2876 = (FStar_Syntax_Unionfind.univ_equiv u u')
in (match (uu____2876) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____2881 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____2883 -> begin
FStar_Pervasives_Native.None
end))))


let whnf' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____2895 = (

let uu____2896 = (

let uu____2897 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::[]) env uu____2897))
in (FStar_Syntax_Subst.compress uu____2896))
in (FStar_All.pipe_right uu____2895 FStar_Syntax_Util.unlazy_emb)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____2909 = (

let uu____2910 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Reify)::[]) env t)
in (FStar_Syntax_Subst.compress uu____2910))
in (FStar_All.pipe_right uu____2909 FStar_Syntax_Util.unlazy_emb)))


let should_strongly_reduce : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2918 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____2918) with
| (h, uu____2937) -> begin
(

let uu____2962 = (

let uu____2963 = (FStar_Syntax_Subst.compress h)
in uu____2963.FStar_Syntax_Syntax.n)
in (match (uu____2962) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____2968 -> begin
false
end))
end)))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____2981 = (should_strongly_reduce t)
in (match (uu____2981) with
| true -> begin
(

let uu____2984 = (

let uu____2985 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env t)
in (FStar_Syntax_Subst.compress uu____2985))
in (FStar_All.pipe_right uu____2984 FStar_Syntax_Util.unlazy_emb))
end
| uu____2986 -> begin
(whnf' env t)
end)))


let norm_arg : 'Auu____2995 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * 'Auu____2995)  ->  (FStar_Syntax_Syntax.term * 'Auu____2995) = (fun env t -> (

let uu____3018 = (sn env (FStar_Pervasives_Native.fst t))
in ((uu____3018), ((FStar_Pervasives_Native.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____3070 -> (match (uu____3070) with
| (x, imp) -> begin
(

let uu____3089 = (

let uu___447_3090 = x
in (

let uu____3091 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___447_3090.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___447_3090.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3091}))
in ((uu____3089), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____3115 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____3115))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____3119 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____3119))
end
| uu____3122 -> begin
u2
end)))
in (

let uu____3123 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3123))))


let base_and_refinement_maybe_delta : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option) = (fun should_delta env t1 -> (

let norm_refinement = (fun env1 t -> (

let steps = (match (should_delta) with
| true -> begin
(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]
end
| uu____3165 -> begin
(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::[]
end)
in (FStar_TypeChecker_Normalize.normalize_refinement steps env1 t)))
in (

let rec aux = (fun norm1 t11 -> (

let t12 = (FStar_Syntax_Util.unmeta t11)
in (match (t12.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(match (norm1) with
| true -> begin
((x.FStar_Syntax_Syntax.sort), (FStar_Pervasives_Native.Some (((x), (phi)))))
end
| uu____3242 -> begin
(

let uu____3244 = (norm_refinement env t12)
in (match (uu____3244) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x1, phi1); FStar_Syntax_Syntax.pos = uu____3259; FStar_Syntax_Syntax.vars = uu____3260} -> begin
((x1.FStar_Syntax_Syntax.sort), (FStar_Pervasives_Native.Some (((x1), (phi1)))))
end
| tt -> begin
(

let uu____3284 = (

let uu____3286 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____3288 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" uu____3286 uu____3288)))
in (failwith uu____3284))
end))
end)
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____3304 = (FStar_Syntax_Util.unfold_lazy i)
in (aux norm1 uu____3304))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____3305) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____3339 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____3342 = (

let uu____3343 = (FStar_Syntax_Subst.compress t1')
in uu____3343.FStar_Syntax_Syntax.n)
in (match (uu____3342) with
| FStar_Syntax_Syntax.Tm_refine (uu____3358) -> begin
(aux true t1')
end
| uu____3366 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____3381) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____3409 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____3412 = (

let uu____3413 = (FStar_Syntax_Subst.compress t1')
in uu____3413.FStar_Syntax_Syntax.n)
in (match (uu____3412) with
| FStar_Syntax_Syntax.Tm_refine (uu____3428) -> begin
(aux true t1')
end
| uu____3436 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_app (uu____3451) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____3495 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____3498 = (

let uu____3499 = (FStar_Syntax_Subst.compress t1')
in uu____3499.FStar_Syntax_Syntax.n)
in (match (uu____3498) with
| FStar_Syntax_Syntax.Tm_refine (uu____3514) -> begin
(aux true t1')
end
| uu____3522 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_type (uu____3537) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_constant (uu____3552) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_name (uu____3567) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3582) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3597) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_abs (uu____3626) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_quoted (uu____3659) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3680) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_let (uu____3707) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_match (uu____3735) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_meta (uu____3772) -> begin
(

let uu____3779 = (

let uu____3781 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3783 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3781 uu____3783)))
in (failwith uu____3779))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3798) -> begin
(

let uu____3825 = (

let uu____3827 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3829 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3827 uu____3829)))
in (failwith uu____3825))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____3844) -> begin
(

let uu____3867 = (

let uu____3869 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3871 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3869 uu____3871)))
in (failwith uu____3867))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____3886 = (

let uu____3888 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3890 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3888 uu____3890)))
in (failwith uu____3886))
end)))
in (

let uu____3905 = (whnf env t1)
in (aux false uu____3905)))))


let base_and_refinement : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option) = (fun env t -> (base_and_refinement_maybe_delta false env t))


let normalize_refinement : FStar_TypeChecker_Env.steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun steps env t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____3966 = (base_and_refinement env t)
in (FStar_All.pipe_right uu____3966 FStar_Pervasives_Native.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (

let uu____4007 = (FStar_Syntax_Syntax.null_bv t)
in ((uu____4007), (FStar_Syntax_Util.t_true))))


let as_refinement : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun delta1 env t -> (

let uu____4034 = (base_and_refinement_maybe_delta delta1 env t)
in (match (uu____4034) with
| (t_base, refinement) -> begin
(match (refinement) with
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end
| FStar_Pervasives_Native.Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term = (fun uu____4094 -> (match (uu____4094) with
| (t_base, refopt) -> begin
(

let uu____4125 = (match (refopt) with
| FStar_Pervasives_Native.Some (y, phi) -> begin
((y), (phi))
end
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end)
in (match (uu____4125) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl prob -> (prob_to_string wl.tcenv prob))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (

let uu____4167 = (

let uu____4171 = (

let uu____4174 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____4199 -> (match (uu____4199) with
| (uu____4207, uu____4208, x) -> begin
x
end))))
in (FStar_List.append wl.attempting uu____4174))
in (FStar_List.map (wl_prob_to_string wl) uu____4171))
in (FStar_All.pipe_right uu____4167 (FStar_String.concat "\n\t"))))


type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)


let flex_t_to_string : 'Auu____4229 . ('Auu____4229 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)  ->  Prims.string = (fun uu____4241 -> (match (uu____4241) with
| (uu____4248, c, args) -> begin
(

let uu____4251 = (print_ctx_uvar c)
in (

let uu____4253 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "%s [%s]" uu____4251 uu____4253)))
end))


let is_flex : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4263 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____4263) with
| (head1, _args) -> begin
(

let uu____4307 = (

let uu____4308 = (FStar_Syntax_Subst.compress head1)
in uu____4308.FStar_Syntax_Syntax.n)
in (match (uu____4307) with
| FStar_Syntax_Syntax.Tm_uvar (uu____4312) -> begin
true
end
| uu____4326 -> begin
false
end))
end)))


let flex_uvar_head : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.ctx_uvar = (fun t -> (

let uu____4334 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____4334) with
| (head1, _args) -> begin
(

let uu____4377 = (

let uu____4378 = (FStar_Syntax_Subst.compress head1)
in uu____4378.FStar_Syntax_Syntax.n)
in (match (uu____4377) with
| FStar_Syntax_Syntax.Tm_uvar (u, uu____4382) -> begin
u
end
| uu____4399 -> begin
(failwith "Not a flex-uvar")
end))
end)))


let destruct_flex_t : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  worklist  ->  (flex_t * worklist) = (fun t wl -> (

let uu____4424 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____4424) with
| (head1, args) -> begin
(

let uu____4471 = (

let uu____4472 = (FStar_Syntax_Subst.compress head1)
in uu____4472.FStar_Syntax_Syntax.n)
in (match (uu____4471) with
| FStar_Syntax_Syntax.Tm_uvar (uv, ([], uu____4480)) -> begin
((((t), (uv), (args))), (wl))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, s) -> begin
(

let uu____4513 = (FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma (FStar_List.partition (fun uu___18_4538 -> (match (uu___18_4538) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let t_x = (FStar_Syntax_Syntax.bv_to_name x)
in (

let t_x' = (FStar_Syntax_Subst.subst' s t_x)
in (

let uu____4543 = (

let uu____4544 = (FStar_Syntax_Subst.compress t_x')
in uu____4544.FStar_Syntax_Syntax.n)
in (match (uu____4543) with
| FStar_Syntax_Syntax.Tm_name (y) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| uu____4549 -> begin
false
end))))
end
| uu____4551 -> begin
true
end))))
in (match (uu____4513) with
| (new_gamma, dom_binders_rev) -> begin
(

let dom_binders = (

let uu____4576 = (FStar_List.collect (fun uu___19_4588 -> (match (uu___19_4588) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let uu____4592 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4592)::[])
end
| uu____4593 -> begin
[]
end)) dom_binders_rev)
in (FStar_All.pipe_right uu____4576 FStar_List.rev))
in (

let uu____4616 = (

let uu____4623 = (

let uu____4632 = (FStar_All.pipe_right new_gamma (FStar_List.collect (fun uu___20_4654 -> (match (uu___20_4654) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let uu____4658 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4658)::[])
end
| uu____4659 -> begin
[]
end))))
in (FStar_All.pipe_right uu____4632 FStar_List.rev))
in (

let uu____4682 = (

let uu____4685 = (FStar_Syntax_Syntax.mk_Total uv.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Syntax_Util.arrow dom_binders uu____4685))
in (new_uvar (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason "; force delayed") wl t.FStar_Syntax_Syntax.pos new_gamma uu____4623 uu____4682 uv.FStar_Syntax_Syntax.ctx_uvar_should_check uv.FStar_Syntax_Syntax.ctx_uvar_meta)))
in (match (uu____4616) with
| (v1, t_v, wl1) -> begin
(

let args_sol = (FStar_List.map (fun uu____4721 -> (match (uu____4721) with
| (x, i) -> begin
(

let uu____4740 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____4740), (i)))
end)) dom_binders)
in (

let sol = (FStar_Syntax_Syntax.mk_Tm_app t_v args_sol FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let args_sol_s = (FStar_List.map (fun uu____4771 -> (match (uu____4771) with
| (a, i) -> begin
(

let uu____4790 = (FStar_Syntax_Subst.subst' s a)
in ((uu____4790), (i)))
end)) args_sol)
in (

let all_args = (FStar_List.append args_sol_s args)
in (

let t1 = (FStar_Syntax_Syntax.mk_Tm_app t_v all_args FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in ((FStar_Syntax_Unionfind.change uv.FStar_Syntax_Syntax.ctx_uvar_head sol);
((((t1), (v1), (all_args))), (wl1));
))))))
end)))
end))
end
| uu____4812 -> begin
(failwith "Not a flex-uvar")
end))
end)))


let u_abs : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____4834 = (

let uu____4857 = (

let uu____4858 = (FStar_Syntax_Subst.compress k)
in uu____4858.FStar_Syntax_Syntax.n)
in (match (uu____4857) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((Prims.op_Equality (FStar_List.length bs) (FStar_List.length ys))) with
| true -> begin
(

let uu____4940 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (uu____4940)))
end
| uu____4973 -> begin
(

let uu____4975 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____4975) with
| (ys', t1, uu____5008) -> begin
(

let uu____5013 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t1))), (uu____5013)))
end))
end)
end
| uu____5052 -> begin
(

let uu____5053 = (

let uu____5058 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____5058)))
in ((((ys), (t))), (uu____5053)))
end))
in (match (uu____4834) with
| ((ys1, t1), (xs, c)) -> begin
(match ((Prims.op_disEquality (FStar_List.length xs) (FStar_List.length ys1))) with
| true -> begin
(FStar_Syntax_Util.abs ys1 t1 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None []))))
end
| uu____5150 -> begin
(

let c1 = (

let uu____5153 = (FStar_Syntax_Util.rename_binders xs ys1)
in (FStar_Syntax_Subst.subst_comp uu____5153 c))
in (FStar_Syntax_Util.abs ys1 t1 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c1)))))
end)
end)))


let solve_prob' : Prims.bool  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun resolve_ok prob logical_guard uvis wl -> ((def_check_prob "solve_prob\'" prob);
(

let phi = (match (logical_guard) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Util.t_true
end
| FStar_Pervasives_Native.Some (phi) -> begin
phi
end)
in (

let assign_solution = (fun xs uv phi1 -> ((

let uu____5231 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____5231) with
| true -> begin
(

let uu____5236 = (FStar_Util.string_of_int (p_pid prob))
in (

let uu____5238 = (print_ctx_uvar uv)
in (

let uu____5240 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" uu____5236 uu____5238 uu____5240))))
end
| uu____5243 -> begin
()
end));
(

let phi2 = (FStar_Syntax_Util.abs xs phi1 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in ((

let uu____5249 = (

let uu____5251 = (FStar_Util.string_of_int (p_pid prob))
in (Prims.op_Hat "solve_prob\'.sol." uu____5251))
in (

let uu____5254 = (

let uu____5257 = (p_scope prob)
in (FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst) uu____5257))
in (FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) uu____5249 uu____5254 phi2)));
(FStar_Syntax_Util.set_uvar uv.FStar_Syntax_Syntax.ctx_uvar_head phi2);
));
))
in (

let uv = (p_guard_uvar prob)
in (

let fail1 = (fun uu____5290 -> (

let uu____5291 = (

let uu____5293 = (FStar_Syntax_Print.ctx_uvar_to_string uv)
in (

let uu____5295 = (FStar_Syntax_Print.term_to_string (p_guard prob))
in (FStar_Util.format2 "Impossible: this instance %s has already been assigned a solution\n%s\n" uu____5293 uu____5295)))
in (failwith uu____5291)))
in (

let args_as_binders = (fun args -> (FStar_All.pipe_right args (FStar_List.collect (fun uu____5361 -> (match (uu____5361) with
| (a, i) -> begin
(

let uu____5382 = (

let uu____5383 = (FStar_Syntax_Subst.compress a)
in uu____5383.FStar_Syntax_Syntax.n)
in (match (uu____5382) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(((x), (i)))::[]
end
| uu____5409 -> begin
((fail1 ());
[];
)
end))
end)))))
in (

let wl1 = (

let g = (whnf wl.tcenv (p_guard prob))
in (

let uu____5419 = (

let uu____5421 = (is_flex g)
in (not (uu____5421)))
in (match (uu____5419) with
| true -> begin
(match (resolve_ok) with
| true -> begin
wl
end
| uu____5425 -> begin
((fail1 ());
wl;
)
end)
end
| uu____5428 -> begin
(

let uu____5430 = (destruct_flex_t g wl)
in (match (uu____5430) with
| ((uu____5435, uv1, args), wl1) -> begin
((

let uu____5440 = (args_as_binders args)
in (assign_solution uu____5440 uv1 phi));
wl1;
)
end))
end)))
in ((commit uvis);
(

let uu___699_5442 = wl1
in {attempting = uu___699_5442.attempting; wl_deferred = uu___699_5442.wl_deferred; ctr = (wl1.ctr + (Prims.parse_int "1")); defer_ok = uu___699_5442.defer_ok; smt_ok = uu___699_5442.smt_ok; umax_heuristic_ok = uu___699_5442.umax_heuristic_ok; tcenv = uu___699_5442.tcenv; wl_implicits = uu___699_5442.wl_implicits});
)))))));
))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____5467 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____5467) with
| true -> begin
(

let uu____5472 = (FStar_Util.string_of_int pid)
in (

let uu____5474 = (

let uu____5476 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right uu____5476 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with [%s]\n" uu____5472 uu____5474)))
end
| uu____5487 -> begin
()
end));
(commit sol);
(

let uu___707_5490 = wl
in {attempting = uu___707_5490.attempting; wl_deferred = uu___707_5490.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___707_5490.defer_ok; smt_ok = uu___707_5490.smt_ok; umax_heuristic_ok = uu___707_5490.umax_heuristic_ok; tcenv = uu___707_5490.tcenv; wl_implicits = uu___707_5490.wl_implicits});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> ((def_check_prob "solve_prob.prob" prob);
(FStar_Util.iter_opt logical_guard (def_check_scoped "solve_prob.guard" prob));
(

let conj_guard1 = (fun t g -> (match (((t), (g))) with
| (uu____5556, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (FStar_Pervasives_Native.None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
FStar_Pervasives_Native.Some (f)
end
| (FStar_Pervasives_Native.Some (t1), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(

let uu____5584 = (FStar_Syntax_Util.mk_conj t1 f)
in FStar_Pervasives_Native.Some (uu____5584))
end))
in ((

let uu____5590 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____5590) with
| true -> begin
(

let uu____5595 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (

let uu____5599 = (

let uu____5601 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right uu____5601 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____5595 uu____5599)))
end
| uu____5612 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
));
))


let occurs : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool) = (fun uk t -> (

let uvars1 = (

let uu____5636 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right uu____5636 FStar_Util.set_elements))
in (

let occurs = (FStar_All.pipe_right uvars1 (FStar_Util.for_some (fun uv -> (FStar_Syntax_Unionfind.equiv uv.FStar_Syntax_Syntax.ctx_uvar_head uk.FStar_Syntax_Syntax.ctx_uvar_head))))
in ((uvars1), (occurs)))))


let occurs_check : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool * Prims.string FStar_Pervasives_Native.option) = (fun uk t -> (

let uu____5676 = (occurs uk t)
in (match (uu____5676) with
| (uvars1, occurs1) -> begin
(

let msg = (match ((not (occurs1))) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5713 -> begin
(

let uu____5715 = (

let uu____5717 = (FStar_Syntax_Print.uvar_to_string uk.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____5719 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" uu____5717 uu____5719)))
in FStar_Pervasives_Native.Some (uu____5715))
end)
in ((uvars1), ((not (occurs1))), (msg)))
end)))


let rec maximal_prefix : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.binders)) = (fun bs bs' -> (match (((bs), (bs'))) with
| (((b, i))::bs_tail, ((b', i'))::bs'_tail) -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
(

let uu____5839 = (maximal_prefix bs_tail bs'_tail)
in (match (uu____5839) with
| (pfx, rest) -> begin
(((((b), (i)))::pfx), (rest))
end))
end
| uu____5878 -> begin
(([]), (((bs), (bs'))))
end)
end
| uu____5890 -> begin
(([]), (((bs), (bs'))))
end))


let extend_gamma : FStar_Syntax_Syntax.gamma  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binding Prims.list = (fun g bs -> (FStar_List.fold_left (fun g1 uu____5947 -> (match (uu____5947) with
| (x, uu____5959) -> begin
(FStar_Syntax_Syntax.Binding_var (x))::g1
end)) g bs))


let gamma_until : FStar_Syntax_Syntax.gamma  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binding Prims.list = (fun g bs -> (

let uu____5977 = (FStar_List.last bs)
in (match (uu____5977) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (x, uu____6001) -> begin
(

let uu____6012 = (FStar_Util.prefix_until (fun uu___21_6027 -> (match (uu___21_6027) with
| FStar_Syntax_Syntax.Binding_var (x') -> begin
(FStar_Syntax_Syntax.bv_eq x x')
end
| uu____6030 -> begin
false
end)) g)
in (match (uu____6012) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____6044, bx, rest) -> begin
(bx)::rest
end))
end)))


let restrict_ctx : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.ctx_uvar  ->  worklist  ->  worklist = (fun tgt src wl -> (

let uu____6081 = (maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders src.FStar_Syntax_Syntax.ctx_uvar_binders)
in (match (uu____6081) with
| (pfx, uu____6091) -> begin
(

let g = (gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx)
in (

let uu____6103 = (new_uvar (Prims.op_Hat "restrict:" src.FStar_Syntax_Syntax.ctx_uvar_reason) wl src.FStar_Syntax_Syntax.ctx_uvar_range g pfx src.FStar_Syntax_Syntax.ctx_uvar_typ src.FStar_Syntax_Syntax.ctx_uvar_should_check src.FStar_Syntax_Syntax.ctx_uvar_meta)
in (match (uu____6103) with
| (uu____6111, src', wl1) -> begin
((FStar_Syntax_Unionfind.change src.FStar_Syntax_Syntax.ctx_uvar_head src');
wl1;
)
end)))
end)))


let restrict_all_uvars : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.ctx_uvar Prims.list  ->  worklist  ->  worklist = (fun tgt sources wl -> (FStar_List.fold_right (restrict_ctx tgt) sources wl))


let intersect_binders : FStar_Syntax_Syntax.gamma  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun g v1 v2 -> (

let as_set1 = (fun v3 -> (FStar_All.pipe_right v3 (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set1 v1)
in (

let ctx_binders = (FStar_List.fold_left (fun out b -> (match (b) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(FStar_Util.set_add x out)
end
| uu____6225 -> begin
out
end)) FStar_Syntax_Syntax.no_names g)
in (

let uu____6226 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____6290 uu____6291 -> (match (((uu____6290), (uu____6291))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____6394 = (

let uu____6396 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation uu____6396))
in (match (uu____6394) with
| true -> begin
((isect), (isect_set))
end
| uu____6425 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____6430 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____6430) with
| true -> begin
(

let uu____6447 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (uu____6447)))
end
| uu____6468 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (ctx_binders))))
in (match (uu____6226) with
| (isect, uu____6497) -> begin
(FStar_List.rev isect)
end))))))


let binders_eq : 'Auu____6533 'Auu____6534 . (FStar_Syntax_Syntax.bv * 'Auu____6533) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____6534) Prims.list  ->  Prims.bool = (fun v1 v2 -> ((Prims.op_Equality (FStar_List.length v1) (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____6592 uu____6593 -> (match (((uu____6592), (uu____6593))) with
| ((a, uu____6612), (b, uu____6614)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let name_exists_in_binders : 'Auu____6630 . FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.bv * 'Auu____6630) Prims.list  ->  Prims.bool = (fun x bs -> (FStar_Util.for_some (fun uu____6661 -> (match (uu____6661) with
| (y, uu____6668) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end)) bs))


let pat_vars : 'Auu____6678 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____6678) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option = (fun env ctx args -> (

let rec aux = (fun seen args1 -> (match (args1) with
| [] -> begin
FStar_Pervasives_Native.Some ((FStar_List.rev seen))
end
| ((arg, i))::args2 -> begin
(

let hd1 = (sn env arg)
in (match (hd1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(

let uu____6840 = ((name_exists_in_binders a seen) || (name_exists_in_binders a ctx))
in (match (uu____6840) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____6863 -> begin
(aux ((((a), (i)))::seen) args2)
end))
end
| uu____6873 -> begin
FStar_Pervasives_Native.None
end))
end))
in (aux [] args)))

type match_result =
| MisMatch of (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
| HeadMatch of Prims.bool
| FullMatch


let uu___is_MisMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MisMatch (_0) -> begin
true
end
| uu____6925 -> begin
false
end))


let __proj__MisMatch__item___0 : match_result  ->  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| MisMatch (_0) -> begin
_0
end))


let uu___is_HeadMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HeadMatch (_0) -> begin
true
end
| uu____6969 -> begin
false
end))


let __proj__HeadMatch__item___0 : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HeadMatch (_0) -> begin
_0
end))


let uu___is_FullMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullMatch -> begin
true
end
| uu____6990 -> begin
false
end))


let string_of_match_result : match_result  ->  Prims.string = (fun uu___22_6998 -> (match (uu___22_6998) with
| MisMatch (d1, d2) -> begin
(

let uu____7010 = (

let uu____7012 = (FStar_Common.string_of_option FStar_Syntax_Print.delta_depth_to_string d1)
in (

let uu____7014 = (

let uu____7016 = (

let uu____7018 = (FStar_Common.string_of_option FStar_Syntax_Print.delta_depth_to_string d2)
in (Prims.op_Hat uu____7018 ")"))
in (Prims.op_Hat ") (" uu____7016))
in (Prims.op_Hat uu____7012 uu____7014)))
in (Prims.op_Hat "MisMatch (" uu____7010))
end
| HeadMatch (u) -> begin
(

let uu____7025 = (FStar_Util.string_of_bool u)
in (Prims.op_Hat "HeadMatch " uu____7025))
end
| FullMatch -> begin
"FullMatch"
end))


let head_match : match_result  ->  match_result = (fun uu___23_7034 -> (match (uu___23_7034) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| HeadMatch (true) -> begin
HeadMatch (true)
end
| uu____7051 -> begin
HeadMatch (false)
end))


let fv_delta_depth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.delta_depth = (fun env fv -> (

let d = (FStar_TypeChecker_Env.delta_depth_of_fv env fv)
in (match (d) with
| FStar_Syntax_Syntax.Delta_abstract (d1) -> begin
(match (((Prims.op_Equality env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr) && (not (env.FStar_TypeChecker_Env.is_iface)))) with
| true -> begin
d1
end
| uu____7068 -> begin
FStar_Syntax_Syntax.delta_constant
end)
end
| FStar_Syntax_Syntax.Delta_constant_at_level (i) when (i > (Prims.parse_int "0")) -> begin
(

let uu____7073 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____7073) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Syntax.delta_constant
end
| uu____7084 -> begin
d
end))
end
| d1 -> begin
d1
end)))


let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____7108) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____7118) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____7145 = (FStar_Syntax_Util.unfold_lazy i)
in (delta_depth_of_term env uu____7145))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_bvar (uu____7146) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_name (uu____7147) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uvar (uu____7148) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_let (uu____7161) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_match (uu____7175) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____7199) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____7205, uu____7206) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____7248) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____7273; FStar_Syntax_Syntax.index = uu____7274; FStar_Syntax_Syntax.sort = t2}, uu____7276) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_constant (uu____7284) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)
end
| FStar_Syntax_Syntax.Tm_type (uu____7285) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____7286) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____7301) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)
end
| FStar_Syntax_Syntax.Tm_abs (uu____7308) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____7328 = (fv_delta_depth env fv)
in FStar_Pervasives_Native.Some (uu____7328))
end)))


let rec head_matches : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  match_result = (fun env t1 t2 -> (

let t11 = (FStar_Syntax_Util.unmeta t1)
in (

let t21 = (FStar_Syntax_Util.unmeta t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_lazy ({FStar_Syntax_Syntax.blob = uu____7347; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding (uu____7348); FStar_Syntax_Syntax.ltyp = uu____7349; FStar_Syntax_Syntax.rng = uu____7350}), uu____7351) -> begin
(

let uu____7362 = (FStar_Syntax_Util.unlazy t11)
in (head_matches env uu____7362 t21))
end
| (uu____7363, FStar_Syntax_Syntax.Tm_lazy ({FStar_Syntax_Syntax.blob = uu____7364; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding (uu____7365); FStar_Syntax_Syntax.ltyp = uu____7366; FStar_Syntax_Syntax.rng = uu____7367})) -> begin
(

let uu____7378 = (FStar_Syntax_Util.unlazy t21)
in (head_matches env t11 uu____7378))
end
| (FStar_Syntax_Syntax.Tm_name (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(match ((FStar_Syntax_Syntax.bv_eq x y)) with
| true -> begin
FullMatch
end
| uu____7382 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____7390 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____7390) with
| true -> begin
FullMatch
end
| uu____7393 -> begin
(

let uu____7395 = (

let uu____7404 = (

let uu____7407 = (fv_delta_depth env f)
in FStar_Pervasives_Native.Some (uu____7407))
in (

let uu____7408 = (

let uu____7411 = (fv_delta_depth env g)
in FStar_Pervasives_Native.Some (uu____7411))
in ((uu____7404), (uu____7408))))
in MisMatch (uu____7395))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____7417), FStar_Syntax_Syntax.Tm_uinst (g, uu____7419)) -> begin
(

let uu____7428 = (head_matches env f g)
in (FStar_All.pipe_right uu____7428 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) -> begin
FullMatch
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____7429) -> begin
HeadMatch (true)
end
| (uu____7431, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) -> begin
HeadMatch (true)
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____7435 = (FStar_Const.eq_const c d)
in (match (uu____7435) with
| true -> begin
FullMatch
end
| uu____7438 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, uu____7445), FStar_Syntax_Syntax.Tm_uvar (uv', uu____7447)) -> begin
(

let uu____7480 = (FStar_Syntax_Unionfind.equiv uv.FStar_Syntax_Syntax.ctx_uvar_head uv'.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____7480) with
| true -> begin
FullMatch
end
| uu____7483 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____7490), FStar_Syntax_Syntax.Tm_refine (y, uu____7492)) -> begin
(

let uu____7501 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____7501 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____7503), uu____7504) -> begin
(

let uu____7509 = (head_matches env x.FStar_Syntax_Syntax.sort t21)
in (FStar_All.pipe_right uu____7509 head_match))
end
| (uu____7510, FStar_Syntax_Syntax.Tm_refine (x, uu____7512)) -> begin
(

let uu____7517 = (head_matches env t11 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____7517 head_match))
end
| (FStar_Syntax_Syntax.Tm_type (uu____7518), FStar_Syntax_Syntax.Tm_type (uu____7519)) -> begin
HeadMatch (false)
end
| (FStar_Syntax_Syntax.Tm_arrow (uu____7521), FStar_Syntax_Syntax.Tm_arrow (uu____7522)) -> begin
HeadMatch (false)
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____7553), FStar_Syntax_Syntax.Tm_app (head', uu____7555)) -> begin
(

let uu____7604 = (head_matches env head1 head')
in (FStar_All.pipe_right uu____7604 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____7606), uu____7607) -> begin
(

let uu____7632 = (head_matches env head1 t21)
in (FStar_All.pipe_right uu____7632 head_match))
end
| (uu____7633, FStar_Syntax_Syntax.Tm_app (head1, uu____7635)) -> begin
(

let uu____7660 = (head_matches env t11 head1)
in (FStar_All.pipe_right uu____7660 head_match))
end
| (FStar_Syntax_Syntax.Tm_let (uu____7661), FStar_Syntax_Syntax.Tm_let (uu____7662)) -> begin
HeadMatch (true)
end
| (FStar_Syntax_Syntax.Tm_match (uu____7690), FStar_Syntax_Syntax.Tm_match (uu____7691)) -> begin
HeadMatch (true)
end
| (FStar_Syntax_Syntax.Tm_abs (uu____7737), FStar_Syntax_Syntax.Tm_abs (uu____7738)) -> begin
HeadMatch (true)
end
| uu____7776 -> begin
(

let uu____7781 = (

let uu____7790 = (delta_depth_of_term env t11)
in (

let uu____7793 = (delta_depth_of_term env t21)
in ((uu____7790), (uu____7793))))
in MisMatch (uu____7781))
end))))


let head_matches_delta : FStar_TypeChecker_Env.env  ->  worklist  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (match_result * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) FStar_Pervasives_Native.option) = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let head1 = (

let uu____7862 = (unrefine env t)
in (FStar_Syntax_Util.head_of uu____7862))
in ((

let uu____7864 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelDelta")))
in (match (uu____7864) with
| true -> begin
(

let uu____7869 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____7871 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.print2 "Head of %s is %s\n" uu____7869 uu____7871)))
end
| uu____7874 -> begin
()
end));
(

let uu____7876 = (

let uu____7877 = (FStar_Syntax_Util.un_uinst head1)
in uu____7877.FStar_Syntax_Syntax.n)
in (match (uu____7876) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____7883 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____7883) with
| FStar_Pervasives_Native.None -> begin
((

let uu____7897 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelDelta")))
in (match (uu____7897) with
| true -> begin
(

let uu____7902 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.print1 "No definition found for %s\n" uu____7902))
end
| uu____7905 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (uu____7907) -> begin
(

let basic_steps = (FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]
in (

let steps = (match (wl.smt_ok) with
| true -> begin
basic_steps
end
| uu____7921 -> begin
(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::basic_steps
end)
in (

let t' = (FStar_TypeChecker_Normalize.normalize steps env t)
in (

let uu____7924 = (

let uu____7926 = (FStar_Syntax_Util.eq_tm t t')
in (Prims.op_Equality uu____7926 FStar_Syntax_Util.Equal))
in (match (uu____7924) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7930 -> begin
((

let uu____7933 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelDelta")))
in (match (uu____7933) with
| true -> begin
(

let uu____7938 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____7940 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Inlined %s to %s\n" uu____7938 uu____7940)))
end
| uu____7943 -> begin
()
end));
FStar_Pervasives_Native.Some (t');
)
end)))))
end))
end
| uu____7945 -> begin
FStar_Pervasives_Native.None
end));
)))
in (

let success = (fun d r t11 t21 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (((t11), (t21)))
end
| uu____7997 -> begin
FStar_Pervasives_Native.None
end))))
in (

let fail1 = (fun d r t11 t21 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (((t11), (t21)))
end
| uu____8054 -> begin
FStar_Pervasives_Native.None
end))))
in (

let rec aux = (fun retry n_delta t11 t21 -> (

let r = (head_matches env t11 t21)
in ((

let uu____8097 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelDelta")))
in (match (uu____8097) with
| true -> begin
(

let uu____8102 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____8104 = (FStar_Syntax_Print.term_to_string t21)
in (

let uu____8106 = (string_of_match_result r)
in (FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8102 uu____8104 uu____8106))))
end
| uu____8109 -> begin
()
end));
(

let reduce_one_and_try_again = (fun d1 d2 -> (

let d1_greater_than_d2 = (FStar_TypeChecker_Common.delta_depth_greater_than d1 d2)
in (

let uu____8134 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Env.UnfoldUntil (d2))::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::[]) env t11)
in ((t1'), (t21)))
end
| uu____8145 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Env.UnfoldUntil (d1))::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::[]) env t21)
in ((t11), (t2')))
end)
in (match (uu____8134) with
| (t12, t22) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
end))))
in (

let reduce_both_and_try_again = (fun d r1 -> (

let uu____8182 = (FStar_TypeChecker_Common.decr_delta_depth d)
in (match (uu____8182) with
| FStar_Pervasives_Native.None -> begin
(fail1 n_delta r1 t11 t21)
end
| FStar_Pervasives_Native.Some (d1) -> begin
(

let t12 = (normalize_refinement ((FStar_TypeChecker_Env.UnfoldUntil (d1))::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::[]) env t11)
in (

let t22 = (normalize_refinement ((FStar_TypeChecker_Env.UnfoldUntil (d1))::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::[]) env t21)
in (aux retry (n_delta + (Prims.parse_int "1")) t12 t22)))
end)))
in (match (r) with
| MisMatch (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational_at_level (i)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational_at_level (j))) when (((i > (Prims.parse_int "0")) || (j > (Prims.parse_int "0"))) && (Prims.op_disEquality i j)) -> begin
(reduce_one_and_try_again (FStar_Syntax_Syntax.Delta_equational_at_level (i)) (FStar_Syntax_Syntax.Delta_equational_at_level (j)))
end
| MisMatch (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational_at_level (uu____8220)), uu____8221) -> begin
(match ((not (retry))) with
| true -> begin
(fail1 n_delta r t11 t21)
end
| uu____8240 -> begin
(

let uu____8242 = (

let uu____8251 = (maybe_inline t11)
in (

let uu____8254 = (maybe_inline t21)
in ((uu____8251), (uu____8254))))
in (match (uu____8242) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(fail1 n_delta r t11 t21)
end
| (FStar_Pervasives_Native.Some (t12), FStar_Pervasives_Native.None) -> begin
(aux false (n_delta + (Prims.parse_int "1")) t12 t21)
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (t22)) -> begin
(aux false (n_delta + (Prims.parse_int "1")) t11 t22)
end
| (FStar_Pervasives_Native.Some (t12), FStar_Pervasives_Native.Some (t22)) -> begin
(aux false (n_delta + (Prims.parse_int "1")) t12 t22)
end))
end)
end
| MisMatch (uu____8297, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational_at_level (uu____8298))) -> begin
(match ((not (retry))) with
| true -> begin
(fail1 n_delta r t11 t21)
end
| uu____8317 -> begin
(

let uu____8319 = (

let uu____8328 = (maybe_inline t11)
in (

let uu____8331 = (maybe_inline t21)
in ((uu____8328), (uu____8331))))
in (match (uu____8319) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(fail1 n_delta r t11 t21)
end
| (FStar_Pervasives_Native.Some (t12), FStar_Pervasives_Native.None) -> begin
(aux false (n_delta + (Prims.parse_int "1")) t12 t21)
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (t22)) -> begin
(aux false (n_delta + (Prims.parse_int "1")) t11 t22)
end
| (FStar_Pervasives_Native.Some (t12), FStar_Pervasives_Native.Some (t22)) -> begin
(aux false (n_delta + (Prims.parse_int "1")) t12 t22)
end))
end)
end
| MisMatch (FStar_Pervasives_Native.Some (d1), FStar_Pervasives_Native.Some (d2)) when (Prims.op_Equality d1 d2) -> begin
(reduce_both_and_try_again d1 r)
end
| MisMatch (FStar_Pervasives_Native.Some (d1), FStar_Pervasives_Native.Some (d2)) -> begin
(reduce_one_and_try_again d1 d2)
end
| MisMatch (uu____8386) -> begin
(fail1 n_delta r t11 t21)
end
| uu____8395 -> begin
(success n_delta r t11 t21)
end)));
)))
in (

let r = (aux true (Prims.parse_int "0") t1 t2)
in ((

let uu____8410 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelDelta")))
in (match (uu____8410) with
| true -> begin
(

let uu____8415 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____8417 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____8419 = (string_of_match_result (FStar_Pervasives_Native.fst r))
in (

let uu____8427 = (match ((FStar_Option.isNone (FStar_Pervasives_Native.snd r))) with
| true -> begin
"None"
end
| uu____8442 -> begin
(

let uu____8444 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd r) FStar_Util.must)
in (FStar_All.pipe_right uu____8444 (fun uu____8479 -> (match (uu____8479) with
| (t11, t21) -> begin
(

let uu____8487 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____8489 = (

let uu____8491 = (FStar_Syntax_Print.term_to_string t21)
in (Prims.op_Hat "; " uu____8491))
in (Prims.op_Hat uu____8487 uu____8489)))
end))))
end)
in (FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n" uu____8415 uu____8417 uu____8419 uu____8427)))))
end
| uu____8495 -> begin
()
end));
r;
)))))))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____8508 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8508 FStar_Pervasives_Native.fst)))


let rank_t_num : FStar_TypeChecker_Common.rank_t  ->  Prims.int = (fun uu___24_8523 -> (match (uu___24_8523) with
| FStar_TypeChecker_Common.Rigid_rigid -> begin
(Prims.parse_int "0")
end
| FStar_TypeChecker_Common.Flex_rigid_eq -> begin
(Prims.parse_int "1")
end
| FStar_TypeChecker_Common.Flex_flex_pattern_eq -> begin
(Prims.parse_int "2")
end
| FStar_TypeChecker_Common.Flex_rigid -> begin
(Prims.parse_int "3")
end
| FStar_TypeChecker_Common.Rigid_flex -> begin
(Prims.parse_int "4")
end
| FStar_TypeChecker_Common.Flex_flex -> begin
(Prims.parse_int "5")
end))


let rank_leq : FStar_TypeChecker_Common.rank_t  ->  FStar_TypeChecker_Common.rank_t  ->  Prims.bool = (fun r1 r2 -> ((rank_t_num r1) <= (rank_t_num r2)))


let rank_less_than : FStar_TypeChecker_Common.rank_t  ->  FStar_TypeChecker_Common.rank_t  ->  Prims.bool = (fun r1 r2 -> ((Prims.op_disEquality r1 r2) && ((rank_t_num r1) <= (rank_t_num r2))))


let compress_tprob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem  ->  FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem = (fun tcenv p -> (

let uu___1211_8572 = p
in (

let uu____8575 = (whnf tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____8576 = (whnf tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___1211_8572.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____8575; FStar_TypeChecker_Common.relation = uu___1211_8572.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____8576; FStar_TypeChecker_Common.element = uu___1211_8572.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___1211_8572.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___1211_8572.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___1211_8572.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___1211_8572.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___1211_8572.FStar_TypeChecker_Common.rank}))))


let compress_prob : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun tcenv p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p1) -> begin
(

let uu____8591 = (compress_tprob tcenv p1)
in (FStar_All.pipe_right uu____8591 (fun _8596 -> FStar_TypeChecker_Common.TProb (_8596))))
end
| FStar_TypeChecker_Common.CProb (uu____8597) -> begin
p
end))


let rank : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob) = (fun tcenv pr -> (

let prob = (

let uu____8620 = (compress_prob tcenv pr)
in (FStar_All.pipe_right uu____8620 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____8628 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____8628) with
| (lh, lhs_args) -> begin
(

let uu____8675 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____8675) with
| (rh, rhs_args) -> begin
(

let uu____8722 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____8735), FStar_Syntax_Syntax.Tm_uvar (uu____8736)) -> begin
(match (((lhs_args), (rhs_args))) with
| ([], []) when (Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
((FStar_TypeChecker_Common.Flex_flex_pattern_eq), (tp))
end
| uu____8825 -> begin
((FStar_TypeChecker_Common.Flex_flex), (tp))
end)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____8852), uu____8853) when (Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
((FStar_TypeChecker_Common.Flex_rigid_eq), (tp))
end
| (uu____8868, FStar_Syntax_Syntax.Tm_uvar (uu____8869)) when (Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
((FStar_TypeChecker_Common.Flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____8884), FStar_Syntax_Syntax.Tm_arrow (uu____8885)) -> begin
((FStar_TypeChecker_Common.Flex_rigid_eq), ((

let uu___1262_8915 = tp
in {FStar_TypeChecker_Common.pid = uu___1262_8915.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___1262_8915.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___1262_8915.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___1262_8915.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___1262_8915.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___1262_8915.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___1262_8915.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___1262_8915.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___1262_8915.FStar_TypeChecker_Common.rank})))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____8918), FStar_Syntax_Syntax.Tm_type (uu____8919)) -> begin
((FStar_TypeChecker_Common.Flex_rigid_eq), ((

let uu___1262_8935 = tp
in {FStar_TypeChecker_Common.pid = uu___1262_8935.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___1262_8935.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___1262_8935.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___1262_8935.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___1262_8935.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___1262_8935.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___1262_8935.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___1262_8935.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___1262_8935.FStar_TypeChecker_Common.rank})))
end
| (FStar_Syntax_Syntax.Tm_type (uu____8938), FStar_Syntax_Syntax.Tm_uvar (uu____8939)) -> begin
((FStar_TypeChecker_Common.Flex_rigid_eq), ((

let uu___1262_8955 = tp
in {FStar_TypeChecker_Common.pid = uu___1262_8955.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___1262_8955.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___1262_8955.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___1262_8955.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___1262_8955.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___1262_8955.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___1262_8955.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___1262_8955.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___1262_8955.FStar_TypeChecker_Common.rank})))
end
| (uu____8958, FStar_Syntax_Syntax.Tm_uvar (uu____8959)) -> begin
((FStar_TypeChecker_Common.Rigid_flex), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____8974), uu____8975) -> begin
((FStar_TypeChecker_Common.Flex_rigid), (tp))
end
| (uu____8990, FStar_Syntax_Syntax.Tm_uvar (uu____8991)) -> begin
((FStar_TypeChecker_Common.Rigid_flex), (tp))
end
| (uu____9006, uu____9007) -> begin
((FStar_TypeChecker_Common.Rigid_rigid), (tp))
end)
in (match (uu____8722) with
| (rank, tp1) -> begin
(

let uu____9020 = (FStar_All.pipe_right (

let uu___1282_9024 = tp1
in {FStar_TypeChecker_Common.pid = uu___1282_9024.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___1282_9024.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___1282_9024.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___1282_9024.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___1282_9024.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___1282_9024.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___1282_9024.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___1282_9024.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___1282_9024.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rank)}) (fun _9027 -> FStar_TypeChecker_Common.TProb (_9027)))
in ((rank), (uu____9020)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____9031 = (FStar_All.pipe_right (

let uu___1286_9035 = cp
in {FStar_TypeChecker_Common.pid = uu___1286_9035.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___1286_9035.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___1286_9035.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___1286_9035.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___1286_9035.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___1286_9035.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___1286_9035.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___1286_9035.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___1286_9035.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (FStar_TypeChecker_Common.Rigid_rigid)}) (fun _9038 -> FStar_TypeChecker_Common.CProb (_9038)))
in ((FStar_TypeChecker_Common.Rigid_rigid), (uu____9031)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option = (fun wl -> (

let rec aux = (fun uu____9098 probs -> (match (uu____9098) with
| (min_rank, min1, out) -> begin
(match (probs) with
| [] -> begin
(match (((min1), (min_rank))) with
| (FStar_Pervasives_Native.Some (p), FStar_Pervasives_Native.Some (r)) -> begin
FStar_Pervasives_Native.Some (((p), (out), (r)))
end
| uu____9179 -> begin
FStar_Pervasives_Native.None
end)
end
| (hd1)::tl1 -> begin
(

let uu____9200 = (rank wl.tcenv hd1)
in (match (uu____9200) with
| (rank1, hd2) -> begin
(match ((rank_leq rank1 FStar_TypeChecker_Common.Flex_rigid_eq)) with
| true -> begin
(match (min1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((hd2), ((FStar_List.append out tl1)), (rank1)))
end
| FStar_Pervasives_Native.Some (m) -> begin
FStar_Pervasives_Native.Some (((hd2), ((FStar_List.append out ((m)::tl1))), (rank1)))
end)
end
| uu____9259 -> begin
(

let uu____9261 = ((Prims.op_Equality min_rank FStar_Pervasives_Native.None) || (

let uu____9266 = (FStar_Option.get min_rank)
in (rank_less_than rank1 uu____9266)))
in (match (uu____9261) with
| true -> begin
(match (min1) with
| FStar_Pervasives_Native.None -> begin
(aux ((FStar_Pervasives_Native.Some (rank1)), (FStar_Pervasives_Native.Some (hd2)), (out)) tl1)
end
| FStar_Pervasives_Native.Some (m) -> begin
(aux ((FStar_Pervasives_Native.Some (rank1)), (FStar_Pervasives_Native.Some (hd2)), ((m)::out)) tl1)
end)
end
| uu____9301 -> begin
(aux ((min_rank), (min1), ((hd2)::out)) tl1)
end))
end)
end))
end)
end))
in (aux ((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), ([])) wl.attempting)))


let flex_prob_closing : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun tcenv bs p -> (

let flex_will_be_closed = (fun t -> (

let uu____9339 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____9339) with
| (hd1, uu____9358) -> begin
(

let uu____9383 = (

let uu____9384 = (FStar_Syntax_Subst.compress hd1)
in uu____9384.FStar_Syntax_Syntax.n)
in (match (uu____9383) with
| FStar_Syntax_Syntax.Tm_uvar (u, uu____9389) -> begin
(FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders (FStar_Util.for_some (fun uu____9424 -> (match (uu____9424) with
| (y, uu____9433) -> begin
(FStar_All.pipe_right bs (FStar_Util.for_some (fun uu____9456 -> (match (uu____9456) with
| (x, uu____9465) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end))))
end))))
end
| uu____9470 -> begin
false
end))
end)))
in (

let uu____9472 = (rank tcenv p)
in (match (uu____9472) with
| (r, p1) -> begin
(match (p1) with
| FStar_TypeChecker_Common.CProb (uu____9481) -> begin
true
end
| FStar_TypeChecker_Common.TProb (p2) -> begin
(match (r) with
| FStar_TypeChecker_Common.Rigid_rigid -> begin
true
end
| FStar_TypeChecker_Common.Flex_rigid_eq -> begin
true
end
| FStar_TypeChecker_Common.Flex_flex_pattern_eq -> begin
true
end
| FStar_TypeChecker_Common.Flex_rigid -> begin
(flex_will_be_closed p2.FStar_TypeChecker_Common.lhs)
end
| FStar_TypeChecker_Common.Rigid_flex -> begin
(flex_will_be_closed p2.FStar_TypeChecker_Common.rhs)
end
| FStar_TypeChecker_Common.Flex_flex -> begin
((Prims.op_Equality p2.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) && ((flex_will_be_closed p2.FStar_TypeChecker_Common.lhs) || (flex_will_be_closed p2.FStar_TypeChecker_Common.rhs)))
end)
end)
end))))

type univ_eq_sol =
| UDeferred of worklist
| USolved of worklist
| UFailed of lstring


let uu___is_UDeferred : univ_eq_sol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UDeferred (_0) -> begin
true
end
| uu____9536 -> begin
false
end))


let __proj__UDeferred__item___0 : univ_eq_sol  ->  worklist = (fun projectee -> (match (projectee) with
| UDeferred (_0) -> begin
_0
end))


let uu___is_USolved : univ_eq_sol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| USolved (_0) -> begin
true
end
| uu____9555 -> begin
false
end))


let __proj__USolved__item___0 : univ_eq_sol  ->  worklist = (fun projectee -> (match (projectee) with
| USolved (_0) -> begin
_0
end))


let uu___is_UFailed : univ_eq_sol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UFailed (_0) -> begin
true
end
| uu____9574 -> begin
false
end))


let __proj__UFailed__item___0 : univ_eq_sol  ->  lstring = (fun projectee -> (match (projectee) with
| UFailed (_0) -> begin
_0
end))


let ufailed_simple : Prims.string  ->  univ_eq_sol = (fun s -> (

let uu____9591 = (FStar_Thunk.mkv s)
in UFailed (uu____9591)))


let ufailed_thunk : (unit  ->  Prims.string)  ->  univ_eq_sol = (fun s -> (

let uu____9606 = (FStar_Thunk.mk s)
in UFailed (uu____9606)))


let rec really_solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun pid_orig wl u1 u2 -> (

let u11 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (

let u21 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (

let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u3 -> (

let uu____9658 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____9658) with
| (k, uu____9666) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Syntax_Unionfind.univ_equiv v1 v2)
end
| uu____9679 -> begin
false
end)
end)))))
end
| uu____9681 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (

let rec filter_out_common_univs = (fun u12 u22 -> (

let common_elts = (FStar_All.pipe_right u12 (FStar_List.fold_left (fun uvs uv1 -> (

let uu____9733 = (FStar_All.pipe_right u22 (FStar_List.existsML (fun uv2 -> (

let uu____9741 = (FStar_Syntax_Util.compare_univs uv1 uv2)
in (Prims.op_Equality uu____9741 (Prims.parse_int "0"))))))
in (match (uu____9733) with
| true -> begin
(uv1)::uvs
end
| uu____9748 -> begin
uvs
end))) []))
in (

let filter1 = (FStar_List.filter (fun u -> (

let uu____9762 = (FStar_All.pipe_right common_elts (FStar_List.existsML (fun u' -> (

let uu____9770 = (FStar_Syntax_Util.compare_univs u u')
in (Prims.op_Equality uu____9770 (Prims.parse_int "0"))))))
in (not (uu____9762)))))
in (

let uu____9774 = (filter1 u12)
in (

let uu____9777 = (filter1 u22)
in ((uu____9774), (uu____9777)))))))
in (

let try_umax_components = (fun u12 u22 msg -> (match ((not (wl.umax_heuristic_ok))) with
| true -> begin
(ufailed_simple "Unable to unify universe terms with umax")
end
| uu____9804 -> begin
(match (((u12), (u22))) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(

let uu____9812 = (filter_out_common_univs us1 us2)
in (match (uu____9812) with
| (us11, us21) -> begin
(match ((Prims.op_Equality (FStar_List.length us11) (FStar_List.length us21))) with
| true -> begin
(

let rec aux = (fun wl1 us12 us22 -> (match (((us12), (us22))) with
| ((u13)::us13, (u23)::us23) -> begin
(

let uu____9872 = (really_solve_universe_eq pid_orig wl1 u13 u23)
in (match (uu____9872) with
| USolved (wl2) -> begin
(aux wl2 us13 us23)
end
| failed -> begin
failed
end))
end
| uu____9875 -> begin
USolved (wl1)
end))
in (aux wl us11 us21))
end
| uu____9884 -> begin
(ufailed_thunk (fun uu____9892 -> (

let uu____9893 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____9895 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" uu____9893 uu____9895)))))
end)
end))
end
| (FStar_Syntax_Syntax.U_max (us), u') -> begin
(

let rec aux = (fun wl1 us1 -> (match (us1) with
| [] -> begin
USolved (wl1)
end
| (u)::us2 -> begin
(

let uu____9921 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____9921) with
| USolved (wl2) -> begin
(aux wl2 us2)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| (u', FStar_Syntax_Syntax.U_max (us)) -> begin
(

let rec aux = (fun wl1 us1 -> (match (us1) with
| [] -> begin
USolved (wl1)
end
| (u)::us2 -> begin
(

let uu____9947 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____9947) with
| USolved (wl2) -> begin
(aux wl2 us2)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____9950 -> begin
(ufailed_thunk (fun uu____9961 -> (

let uu____9962 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____9964 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" uu____9962 uu____9964 msg)))))
end)
end))
in (match (((u11), (u21))) with
| (FStar_Syntax_Syntax.U_bvar (uu____9967), uu____9968) -> begin
(

let uu____9970 = (

let uu____9972 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____9974 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____9972 uu____9974)))
in (failwith uu____9970))
end
| (FStar_Syntax_Syntax.U_unknown, uu____9977) -> begin
(

let uu____9978 = (

let uu____9980 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____9982 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____9980 uu____9982)))
in (failwith uu____9978))
end
| (uu____9985, FStar_Syntax_Syntax.U_bvar (uu____9986)) -> begin
(

let uu____9988 = (

let uu____9990 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____9992 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____9990 uu____9992)))
in (failwith uu____9988))
end
| (uu____9995, FStar_Syntax_Syntax.U_unknown) -> begin
(

let uu____9996 = (

let uu____9998 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____10000 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____9998 uu____10000)))
in (failwith uu____9996))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____10007 -> begin
(ufailed_simple "Incompatible universes")
end)
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
USolved (wl)
end
| (FStar_Syntax_Syntax.U_succ (u12), FStar_Syntax_Syntax.U_succ (u22)) -> begin
(really_solve_universe_eq pid_orig wl u12 u22)
end
| (FStar_Syntax_Syntax.U_unif (v1), FStar_Syntax_Syntax.U_unif (v2)) -> begin
(

let uu____10030 = (FStar_Syntax_Unionfind.univ_equiv v1 v2)
in (match (uu____10030) with
| true -> begin
USolved (wl)
end
| uu____10033 -> begin
(

let wl1 = (extend_solution pid_orig ((UNIV (((v1), (u21))))::[]) wl)
in USolved (wl1))
end))
end
| (FStar_Syntax_Syntax.U_unif (v1), u) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____10047 = (occurs_univ v1 u3)
in (match (uu____10047) with
| true -> begin
(

let uu____10050 = (

let uu____10052 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____10054 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____10052 uu____10054)))
in (try_umax_components u11 u21 uu____10050))
end
| uu____10057 -> begin
(

let uu____10059 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____10059))
end)))
end
| (u, FStar_Syntax_Syntax.U_unif (v1)) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____10071 = (occurs_univ v1 u3)
in (match (uu____10071) with
| true -> begin
(

let uu____10074 = (

let uu____10076 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____10078 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____10076 uu____10078)))
in (try_umax_components u11 u21 uu____10074))
end
| uu____10081 -> begin
(

let uu____10083 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____10083))
end)))
end
| (FStar_Syntax_Syntax.U_max (uu____10084), uu____10085) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____10089 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____10093 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____10093) with
| true -> begin
USolved (wl)
end
| uu____10096 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (uu____10099, FStar_Syntax_Syntax.U_max (uu____10100)) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____10104 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____10108 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____10108) with
| true -> begin
USolved (wl)
end
| uu____10111 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (FStar_Syntax_Syntax.U_succ (uu____10114), FStar_Syntax_Syntax.U_zero) -> begin
(ufailed_simple "Incompatible universes")
end
| (FStar_Syntax_Syntax.U_succ (uu____10116), FStar_Syntax_Syntax.U_name (uu____10117)) -> begin
(ufailed_simple "Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ (uu____10119)) -> begin
(ufailed_simple "Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name (uu____10121)) -> begin
(ufailed_simple "Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____10123), FStar_Syntax_Syntax.U_succ (uu____10124)) -> begin
(ufailed_simple "Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____10126), FStar_Syntax_Syntax.U_zero) -> begin
(ufailed_simple "Incompatible universes")
end)))))))


let solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (match (wl.tcenv.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
USolved (wl)
end
| uu____10152 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders : 'a 'b . ('a Prims.list * ('a Prims.list  ->  'b))  ->  ('a Prims.list * ('a Prims.list  ->  'b))  ->  (('a Prims.list * 'b) * ('a Prims.list * 'b)) = (fun bc1 bc2 -> (

let uu____10233 = bc1
in (match (uu____10233) with
| (bs1, mk_cod1) -> begin
(

let uu____10277 = bc2
in (match (uu____10277) with
| (bs2, mk_cod2) -> begin
(

let rec aux = (fun bs11 bs21 -> (match (((bs11), (bs21))) with
| ((x)::xs, (y)::ys) -> begin
(

let uu____10388 = (aux xs ys)
in (match (uu____10388) with
| ((xs1, xr), (ys1, yr)) -> begin
(((((x)::xs1), (xr))), ((((y)::ys1), (yr))))
end))
end
| (xs, ys) -> begin
(

let uu____10471 = (

let uu____10478 = (mk_cod1 xs)
in (([]), (uu____10478)))
in (

let uu____10481 = (

let uu____10488 = (mk_cod2 ys)
in (([]), (uu____10488)))
in ((uu____10471), (uu____10481))))
end))
in (aux bs1 bs2))
end))
end)))


let guard_of_prob : FStar_TypeChecker_Env.env  ->  worklist  ->  tprob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * worklist) = (fun env wl problem t1 t2 -> (

let has_type_guard = (fun t11 t21 -> (match (problem.FStar_TypeChecker_Common.element) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____10557 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Util.mk_has_type t11 uu____10557 t21))
end
| FStar_Pervasives_Native.None -> begin
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None t11)
in (

let u_x = (env.FStar_TypeChecker_Env.universe_of env t11)
in (

let uu____10560 = (

let uu____10561 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t11 uu____10561 t21))
in (FStar_Syntax_Util.mk_forall u_x x uu____10560))))
end))
in (match (problem.FStar_TypeChecker_Common.relation) with
| FStar_TypeChecker_Common.EQ -> begin
(mk_eq2 wl env (FStar_TypeChecker_Common.TProb (problem)) t1 t2)
end
| FStar_TypeChecker_Common.SUB -> begin
(

let uu____10566 = (has_type_guard t1 t2)
in ((uu____10566), (wl)))
end
| FStar_TypeChecker_Common.SUBINV -> begin
(

let uu____10567 = (has_type_guard t2 t1)
in ((uu____10567), (wl)))
end)))


let is_flex_pat : 'Auu____10577 'Auu____10578 'Auu____10579 . ('Auu____10577 * 'Auu____10578 * 'Auu____10579 Prims.list)  ->  Prims.bool = (fun uu___25_10593 -> (match (uu___25_10593) with
| (uu____10602, uu____10603, []) -> begin
true
end
| uu____10607 -> begin
false
end))


let quasi_pattern : FStar_TypeChecker_Env.env  ->  flex_t  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ) FStar_Pervasives_Native.option = (fun env f -> (

let uu____10640 = f
in (match (uu____10640) with
| (uu____10647, {FStar_Syntax_Syntax.ctx_uvar_head = uu____10648; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10649; FStar_Syntax_Syntax.ctx_uvar_binders = ctx; FStar_Syntax_Syntax.ctx_uvar_typ = t_hd; FStar_Syntax_Syntax.ctx_uvar_reason = uu____10652; FStar_Syntax_Syntax.ctx_uvar_should_check = uu____10653; FStar_Syntax_Syntax.ctx_uvar_range = uu____10654; FStar_Syntax_Syntax.ctx_uvar_meta = uu____10655}, args) -> begin
(

let name_exists_in = (fun x bs -> (FStar_Util.for_some (fun uu____10725 -> (match (uu____10725) with
| (y, uu____10734) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end)) bs))
in (

let rec aux = (fun pat_binders formals t_res args1 -> (match (((formals), (args1))) with
| ([], []) -> begin
(

let uu____10888 = (

let uu____10903 = (

let uu____10906 = (FStar_Syntax_Syntax.mk_Total t_res)
in (FStar_Syntax_Util.arrow formals uu____10906))
in (((FStar_List.rev pat_binders)), (uu____10903)))
in FStar_Pervasives_Native.Some (uu____10888))
end
| (uu____10939, []) -> begin
(

let uu____10970 = (

let uu____10985 = (

let uu____10988 = (FStar_Syntax_Syntax.mk_Total t_res)
in (FStar_Syntax_Util.arrow formals uu____10988))
in (((FStar_List.rev pat_binders)), (uu____10985)))
in FStar_Pervasives_Native.Some (uu____10970))
end
| (((formal, formal_imp))::formals1, ((a, a_imp))::args2) -> begin
(

let uu____11079 = (

let uu____11080 = (FStar_Syntax_Subst.compress a)
in uu____11080.FStar_Syntax_Syntax.n)
in (match (uu____11079) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____11100 = ((name_exists_in x ctx) || (name_exists_in x pat_binders))
in (match (uu____11100) with
| true -> begin
(aux ((((formal), (formal_imp)))::pat_binders) formals1 t_res args2)
end
| uu____11127 -> begin
(

let x1 = (

let uu___1614_11130 = x
in {FStar_Syntax_Syntax.ppname = uu___1614_11130.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1614_11130.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = formal.FStar_Syntax_Syntax.sort})
in (

let subst1 = (

let uu____11134 = (

let uu____11135 = (

let uu____11142 = (FStar_Syntax_Syntax.bv_to_name x1)
in ((formal), (uu____11142)))
in FStar_Syntax_Syntax.NT (uu____11135))
in (uu____11134)::[])
in (

let formals2 = (FStar_Syntax_Subst.subst_binders subst1 formals1)
in (

let t_res1 = (FStar_Syntax_Subst.subst subst1 t_res)
in (aux (((((

let uu___1620_11158 = x1
in {FStar_Syntax_Syntax.ppname = uu___1620_11158.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1620_11158.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = formal.FStar_Syntax_Syntax.sort})), (a_imp)))::pat_binders) formals2 t_res1 args2)))))
end))
end
| uu____11159 -> begin
(aux ((((formal), (formal_imp)))::pat_binders) formals1 t_res args2)
end))
end
| ([], args2) -> begin
(

let uu____11199 = (

let uu____11214 = (FStar_TypeChecker_Normalize.unfold_whnf env t_res)
in (FStar_Syntax_Util.arrow_formals uu____11214))
in (match (uu____11199) with
| (more_formals, t_res1) -> begin
(match (more_formals) with
| [] -> begin
FStar_Pervasives_Native.None
end
| uu____11289 -> begin
(aux pat_binders more_formals t_res1 args2)
end)
end))
end))
in (match (args) with
| [] -> begin
FStar_Pervasives_Native.Some ((([]), (t_hd)))
end
| uu____11322 -> begin
(

let uu____11323 = (FStar_Syntax_Util.arrow_formals t_hd)
in (match (uu____11323) with
| (formals, t_res) -> begin
(aux [] formals t_res args)
end))
end)))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____11643 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11643) with
| true -> begin
(

let uu____11648 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" uu____11648))
end
| uu____11651 -> begin
()
end));
(

let uu____11653 = (next_prob probs)
in (match (uu____11653) with
| FStar_Pervasives_Native.Some (hd1, tl1, rank1) -> begin
(

let probs1 = (

let uu___1645_11680 = probs
in {attempting = tl1; wl_deferred = uu___1645_11680.wl_deferred; ctr = uu___1645_11680.ctr; defer_ok = uu___1645_11680.defer_ok; smt_ok = uu___1645_11680.smt_ok; umax_heuristic_ok = uu___1645_11680.umax_heuristic_ok; tcenv = uu___1645_11680.tcenv; wl_implicits = uu___1645_11680.wl_implicits})
in ((def_check_prob "solve,hd" hd1);
(match (hd1) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs1)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____11689 = (FStar_Util.physical_equality tp.FStar_TypeChecker_Common.lhs tp.FStar_TypeChecker_Common.rhs)
in (match (uu____11689) with
| true -> begin
(

let uu____11692 = (solve_prob hd1 FStar_Pervasives_Native.None [] probs1)
in (solve env uu____11692))
end
| uu____11693 -> begin
(match (((Prims.op_Equality rank1 FStar_TypeChecker_Common.Rigid_rigid) || ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) && (Prims.op_disEquality rank1 FStar_TypeChecker_Common.Flex_flex)))) with
| true -> begin
(solve_t env tp probs1)
end
| uu____11696 -> begin
(match (probs1.defer_ok) with
| true -> begin
(

let uu____11699 = (defer_lit "deferring flex_rigid or flex_flex subtyping" hd1 probs1)
in (solve env uu____11699))
end
| uu____11701 -> begin
(match ((Prims.op_Equality rank1 FStar_TypeChecker_Common.Flex_flex)) with
| true -> begin
(solve_t env (

let uu___1657_11705 = tp
in {FStar_TypeChecker_Common.pid = uu___1657_11705.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___1657_11705.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___1657_11705.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___1657_11705.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___1657_11705.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___1657_11705.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___1657_11705.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___1657_11705.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___1657_11705.FStar_TypeChecker_Common.rank}) probs1)
end
| uu____11708 -> begin
(solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp probs1)
end)
end)
end)
end))
end);
))
end
| FStar_Pervasives_Native.None -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ((([]), (probs.wl_implicits)))
end
| uu____11730 -> begin
(

let uu____11740 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____11805 -> (match (uu____11805) with
| (c, uu____11815, uu____11816) -> begin
(c < probs.ctr)
end))))
in (match (uu____11740) with
| (attempt1, rest) -> begin
(match (attempt1) with
| [] -> begin
(

let uu____11864 = (

let uu____11869 = (FStar_List.map (fun uu____11890 -> (match (uu____11890) with
| (uu____11906, x, y) -> begin
(

let uu____11917 = (FStar_Thunk.force x)
in ((uu____11917), (y)))
end)) probs.wl_deferred)
in ((uu____11869), (probs.wl_implicits)))
in Success (uu____11864))
end
| uu____11921 -> begin
(

let uu____11931 = (

let uu___1675_11932 = probs
in (

let uu____11933 = (FStar_All.pipe_right attempt1 (FStar_List.map (fun uu____11954 -> (match (uu____11954) with
| (uu____11962, uu____11963, y) -> begin
y
end))))
in {attempting = uu____11933; wl_deferred = rest; ctr = uu___1675_11932.ctr; defer_ok = uu___1675_11932.defer_ok; smt_ok = uu___1675_11932.smt_ok; umax_heuristic_ok = uu___1675_11932.umax_heuristic_ok; tcenv = uu___1675_11932.tcenv; wl_implicits = uu___1675_11932.wl_implicits}))
in (solve env uu____11931))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____11972 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____11972) with
| USolved (wl1) -> begin
(

let uu____11974 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____11974))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl1) -> begin
(

let uu____11977 = (defer_lit "" orig wl1)
in (solve env uu____11977))
end)))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (

let rec aux = (fun wl1 us1 us2 -> (match (((us1), (us2))) with
| ([], []) -> begin
USolved (wl1)
end
| ((u1)::us11, (u2)::us21) -> begin
(

let uu____12028 = (solve_universe_eq (p_pid orig) wl1 u1 u2)
in (match (uu____12028) with
| USolved (wl2) -> begin
(aux wl2 us11 us21)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____12031 -> begin
(ufailed_simple "Unequal number of universes")
end))
in (

let t11 = (whnf env t1)
in (

let t21 = (whnf env t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.pos = uu____12044; FStar_Syntax_Syntax.vars = uu____12045}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.pos = uu____12048; FStar_Syntax_Syntax.vars = uu____12049}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____12062), uu____12063) -> begin
(failwith "Impossible: expect head symbols to match")
end
| (uu____12071, FStar_Syntax_Syntax.Tm_uinst (uu____12072)) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____12080 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  lstring  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____12091 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12091) with
| true -> begin
(

let uu____12096 = (prob_to_string env orig)
in (

let uu____12098 = (FStar_Thunk.force msg)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" uu____12096 uu____12098)))
end
| uu____12102 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____12104 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_or_flex_rigid_subtyping : FStar_TypeChecker_Common.rank_t  ->  FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun rank1 env tp wl -> ((def_check_prob "solve_rigid_flex_or_flex_rigid_subtyping" (FStar_TypeChecker_Common.TProb (tp)));
(

let flip = (Prims.op_Equality rank1 FStar_TypeChecker_Common.Flex_rigid)
in (

let meet_or_join = (fun op ts env1 wl1 -> (

let eq_prob = (fun t1 t2 wl2 -> (

let uu____12191 = (new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos "join/meet refinements")
in (match (uu____12191) with
| (p, wl3) -> begin
((def_check_prob "meet_or_join" (FStar_TypeChecker_Common.TProb (p)));
((FStar_TypeChecker_Common.TProb (p)), (wl3));
)
end)))
in (

let pairwise = (fun t1 t2 wl2 -> ((

let uu____12246 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____12246) with
| true -> begin
(

let uu____12251 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12253 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n" uu____12251 uu____12253)))
end
| uu____12256 -> begin
()
end));
(

let uu____12258 = (head_matches_delta env1 wl2 t1 t2)
in (match (uu____12258) with
| (mr, ts1) -> begin
(match (mr) with
| HeadMatch (true) -> begin
(

let uu____12304 = (eq_prob t1 t2 wl2)
in (match (uu____12304) with
| (p, wl3) -> begin
((t1), ((p)::[]), (wl3))
end))
end
| MisMatch (uu____12325) -> begin
(

let uu____12334 = (eq_prob t1 t2 wl2)
in (match (uu____12334) with
| (p, wl3) -> begin
((t1), ((p)::[]), (wl3))
end))
end
| FullMatch -> begin
(match (ts1) with
| FStar_Pervasives_Native.None -> begin
((t1), ([]), (wl2))
end
| FStar_Pervasives_Native.Some (t11, t21) -> begin
((t11), ([]), (wl2))
end)
end
| HeadMatch (false) -> begin
(

let uu____12384 = (match (ts1) with
| FStar_Pervasives_Native.Some (t11, t21) -> begin
(

let uu____12399 = (FStar_Syntax_Subst.compress t11)
in (

let uu____12400 = (FStar_Syntax_Subst.compress t21)
in ((uu____12399), (uu____12400))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____12405 = (FStar_Syntax_Subst.compress t1)
in (

let uu____12406 = (FStar_Syntax_Subst.compress t2)
in ((uu____12405), (uu____12406))))
end)
in (match (uu____12384) with
| (t11, t21) -> begin
(

let try_eq = (fun t12 t22 wl3 -> (

let uu____12437 = (FStar_Syntax_Util.head_and_args t12)
in (match (uu____12437) with
| (t1_hd, t1_args) -> begin
(

let uu____12482 = (FStar_Syntax_Util.head_and_args t22)
in (match (uu____12482) with
| (t2_hd, t2_args) -> begin
(match ((Prims.op_disEquality (FStar_List.length t1_args) (FStar_List.length t2_args))) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____12546 -> begin
(

let uu____12548 = (

let uu____12555 = (

let uu____12566 = (FStar_Syntax_Syntax.as_arg t1_hd)
in (uu____12566)::t1_args)
in (

let uu____12583 = (

let uu____12592 = (FStar_Syntax_Syntax.as_arg t2_hd)
in (uu____12592)::t2_args)
in (FStar_List.fold_left2 (fun uu____12641 uu____12642 uu____12643 -> (match (((uu____12641), (uu____12642), (uu____12643))) with
| ((probs, wl4), (a1, uu____12693), (a2, uu____12695)) -> begin
(

let uu____12732 = (eq_prob a1 a2 wl4)
in (match (uu____12732) with
| (p, wl5) -> begin
(((p)::probs), (wl5))
end))
end)) (([]), (wl3)) uu____12555 uu____12583)))
in (match (uu____12548) with
| (probs, wl4) -> begin
(

let wl' = (

let uu___1829_12758 = wl4
in {attempting = probs; wl_deferred = []; ctr = uu___1829_12758.ctr; defer_ok = false; smt_ok = false; umax_heuristic_ok = uu___1829_12758.umax_heuristic_ok; tcenv = uu___1829_12758.tcenv; wl_implicits = []})
in (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____12769 = (solve env1 wl')
in (match (uu____12769) with
| Success (uu____12772, imps) -> begin
((FStar_Syntax_Unionfind.commit tx);
FStar_Pervasives_Native.Some ((

let uu___1838_12776 = wl4
in {attempting = uu___1838_12776.attempting; wl_deferred = uu___1838_12776.wl_deferred; ctr = uu___1838_12776.ctr; defer_ok = uu___1838_12776.defer_ok; smt_ok = uu___1838_12776.smt_ok; umax_heuristic_ok = uu___1838_12776.umax_heuristic_ok; tcenv = uu___1838_12776.tcenv; wl_implicits = (FStar_List.append wl4.wl_implicits imps)}));
)
end
| Failed (uu____12777) -> begin
((FStar_Syntax_Unionfind.rollback tx);
FStar_Pervasives_Native.None;
)
end))))
end))
end)
end))
end)))
in (

let combine = (fun t12 t22 wl3 -> (

let uu____12809 = (base_and_refinement_maybe_delta false env1 t12)
in (match (uu____12809) with
| (t1_base, p1_opt) -> begin
(

let uu____12845 = (base_and_refinement_maybe_delta false env1 t22)
in (match (uu____12845) with
| (t2_base, p2_opt) -> begin
(

let combine_refinements = (fun t_base p1_opt1 p2_opt1 -> (

let refine1 = (fun x t -> (

let uu____12944 = (FStar_Syntax_Util.is_t_true t)
in (match (uu____12944) with
| true -> begin
x.FStar_Syntax_Syntax.sort
end
| uu____12949 -> begin
(FStar_Syntax_Util.refine x t)
end)))
in (match (((p1_opt1), (p2_opt1))) with
| (FStar_Pervasives_Native.Some (x, phi1), FStar_Pervasives_Native.Some (y, phi2)) -> begin
(

let x1 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let subst1 = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x1))))::[]
in (

let phi11 = (FStar_Syntax_Subst.subst subst1 phi1)
in (

let phi21 = (FStar_Syntax_Subst.subst subst1 phi2)
in (

let uu____12997 = (op phi11 phi21)
in (refine1 x1 uu____12997))))))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (x, phi)) -> begin
(

let x1 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let subst1 = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x1))))::[]
in (

let phi1 = (FStar_Syntax_Subst.subst subst1 phi)
in (

let uu____13029 = (op FStar_Syntax_Util.t_true phi1)
in (refine1 x1 uu____13029)))))
end
| (FStar_Pervasives_Native.Some (x, phi), FStar_Pervasives_Native.None) -> begin
(

let x1 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let subst1 = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x1))))::[]
in (

let phi1 = (FStar_Syntax_Subst.subst subst1 phi)
in (

let uu____13061 = (op FStar_Syntax_Util.t_true phi1)
in (refine1 x1 uu____13061)))))
end
| uu____13064 -> begin
t_base
end)))
in (

let uu____13081 = (try_eq t1_base t2_base wl3)
in (match (uu____13081) with
| FStar_Pervasives_Native.Some (wl4) -> begin
(

let uu____13095 = (combine_refinements t1_base p1_opt p2_opt)
in ((uu____13095), ([]), (wl4)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____13102 = (base_and_refinement_maybe_delta true env1 t12)
in (match (uu____13102) with
| (t1_base1, p1_opt1) -> begin
(

let uu____13138 = (base_and_refinement_maybe_delta true env1 t22)
in (match (uu____13138) with
| (t2_base1, p2_opt1) -> begin
(

let uu____13174 = (eq_prob t1_base1 t2_base1 wl3)
in (match (uu____13174) with
| (p, wl4) -> begin
(

let t = (combine_refinements t1_base1 p1_opt1 p2_opt1)
in ((t), ((p)::[]), (wl4)))
end))
end))
end))
end)))
end))
end)))
in (

let uu____13198 = (combine t11 t21 wl2)
in (match (uu____13198) with
| (t12, ps, wl3) -> begin
((

let uu____13231 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____13231) with
| true -> begin
(

let uu____13236 = (FStar_Syntax_Print.term_to_string t12)
in (FStar_Util.print1 "pairwise fallback2 succeeded: %s" uu____13236))
end
| uu____13239 -> begin
()
end));
((t12), (ps), (wl3));
)
end))))
end))
end)
end));
))
in (

let rec aux = (fun uu____13278 ts1 -> (match (uu____13278) with
| (out, probs, wl2) -> begin
(match (ts1) with
| [] -> begin
((out), (probs), (wl2))
end
| (t)::ts2 -> begin
(

let uu____13341 = (pairwise out t wl2)
in (match (uu____13341) with
| (out1, probs', wl3) -> begin
(aux ((out1), ((FStar_List.append probs probs')), (wl3)) ts2)
end))
end)
end))
in (

let uu____13377 = (

let uu____13388 = (FStar_List.hd ts)
in ((uu____13388), ([]), (wl1)))
in (

let uu____13397 = (FStar_List.tl ts)
in (aux uu____13377 uu____13397)))))))
in (

let uu____13404 = (match (flip) with
| true -> begin
((tp.FStar_TypeChecker_Common.lhs), (tp.FStar_TypeChecker_Common.rhs))
end
| uu____13420 -> begin
((tp.FStar_TypeChecker_Common.rhs), (tp.FStar_TypeChecker_Common.lhs))
end)
in (match (uu____13404) with
| (this_flex, this_rigid) -> begin
(

let uu____13430 = (

let uu____13431 = (FStar_Syntax_Subst.compress this_rigid)
in uu____13431.FStar_Syntax_Syntax.n)
in (match (uu____13430) with
| FStar_Syntax_Syntax.Tm_arrow (_bs, comp) -> begin
(

let uu____13456 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____13456) with
| true -> begin
(

let uu____13459 = (destruct_flex_t this_flex wl)
in (match (uu____13459) with
| (flex, wl1) -> begin
(

let uu____13466 = (quasi_pattern env flex)
in (match (uu____13466) with
| FStar_Pervasives_Native.None -> begin
(giveup_lit env "flex-arrow subtyping, not a quasi pattern" (FStar_TypeChecker_Common.TProb (tp)))
end
| FStar_Pervasives_Native.Some (flex_bs, flex_t) -> begin
((

let uu____13485 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____13485) with
| true -> begin
(

let uu____13490 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by imitating arrow:%s\n" uu____13490))
end
| uu____13493 -> begin
()
end));
(imitate_arrow (FStar_TypeChecker_Common.TProb (tp)) env wl1 flex flex_bs flex_t tp.FStar_TypeChecker_Common.relation this_rigid);
)
end))
end))
end
| uu____13495 -> begin
(

let uu____13497 = (attempt ((FStar_TypeChecker_Common.TProb ((

let uu___1940_13500 = tp
in {FStar_TypeChecker_Common.pid = uu___1940_13500.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___1940_13500.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___1940_13500.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___1940_13500.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___1940_13500.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___1940_13500.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___1940_13500.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___1940_13500.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___1940_13500.FStar_TypeChecker_Common.rank})))::[]) wl)
in (solve env uu____13497))
end))
end
| uu____13501 -> begin
((

let uu____13503 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____13503) with
| true -> begin
(

let uu____13508 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" uu____13508))
end
| uu____13511 -> begin
()
end));
(

let uu____13513 = (FStar_Syntax_Util.head_and_args this_flex)
in (match (uu____13513) with
| (u, _args) -> begin
(

let uu____13556 = (

let uu____13557 = (FStar_Syntax_Subst.compress u)
in uu____13557.FStar_Syntax_Syntax.n)
in (match (uu____13556) with
| FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, _subst) -> begin
(

let equiv1 = (fun t -> (

let uu____13585 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____13585) with
| (u', uu____13604) -> begin
(

let uu____13629 = (

let uu____13630 = (whnf env u')
in uu____13630.FStar_Syntax_Syntax.n)
in (match (uu____13629) with
| FStar_Syntax_Syntax.Tm_uvar (ctx_uvar', _subst') -> begin
(FStar_Syntax_Unionfind.equiv ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head)
end
| uu____13652 -> begin
false
end))
end)))
in (

let uu____13654 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___26_13677 -> (match (uu___26_13677) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(

let tp2 = (maybe_invert tp1)
in (match (tp2.FStar_TypeChecker_Common.rank) with
| FStar_Pervasives_Native.Some (rank') when (Prims.op_Equality rank1 rank') -> begin
(match (flip) with
| true -> begin
(equiv1 tp2.FStar_TypeChecker_Common.lhs)
end
| uu____13689 -> begin
(equiv1 tp2.FStar_TypeChecker_Common.rhs)
end)
end
| uu____13691 -> begin
false
end))
end
| uu____13695 -> begin
false
end))))
in (match (uu____13654) with
| (bounds_probs, rest) -> begin
(

let bounds_typs = (

let uu____13710 = (whnf env this_rigid)
in (

let uu____13711 = (FStar_List.collect (fun uu___27_13717 -> (match (uu___27_13717) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____13723 = (match (flip) with
| true -> begin
(whnf env (maybe_invert p).FStar_TypeChecker_Common.rhs)
end
| uu____13725 -> begin
(whnf env (maybe_invert p).FStar_TypeChecker_Common.lhs)
end)
in (uu____13723)::[])
end
| uu____13727 -> begin
[]
end)) bounds_probs)
in (uu____13710)::uu____13711))
in (

let uu____13728 = (meet_or_join (match (flip) with
| true -> begin
FStar_Syntax_Util.mk_conj_simp
end
| uu____13748 -> begin
FStar_Syntax_Util.mk_disj_simp
end) bounds_typs env wl)
in (match (uu____13728) with
| (bound, sub_probs, wl1) -> begin
(

let uu____13761 = (

let flex_u = (flex_uvar_head this_flex)
in (

let bound1 = (

let uu____13776 = (

let uu____13777 = (FStar_Syntax_Subst.compress bound)
in uu____13777.FStar_Syntax_Syntax.n)
in (match (uu____13776) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) when ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB) && (

let uu____13789 = (occurs flex_u x.FStar_Syntax_Syntax.sort)
in (FStar_Pervasives_Native.snd uu____13789))) -> begin
x.FStar_Syntax_Syntax.sort
end
| uu____13800 -> begin
bound
end))
in (

let uu____13801 = (new_problem wl1 env bound1 FStar_TypeChecker_Common.EQ this_flex FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc (match (flip) with
| true -> begin
"joining refinements"
end
| uu____13811 -> begin
"meeting refinements"
end))
in ((bound1), (uu____13801)))))
in (match (uu____13761) with
| (bound_typ, (eq_prob, wl')) -> begin
((def_check_prob "meet_or_join2" (FStar_TypeChecker_Common.TProb (eq_prob)));
(

let uu____13836 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____13836) with
| true -> begin
(

let wl'1 = (

let uu___2000_13842 = wl1
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___2000_13842.wl_deferred; ctr = uu___2000_13842.ctr; defer_ok = uu___2000_13842.defer_ok; smt_ok = uu___2000_13842.smt_ok; umax_heuristic_ok = uu___2000_13842.umax_heuristic_ok; tcenv = uu___2000_13842.tcenv; wl_implicits = uu___2000_13842.wl_implicits})
in (

let uu____13843 = (wl_to_string wl'1)
in (FStar_Util.print1 "After meet/join refinements: %s\n" uu____13843)))
end
| uu____13846 -> begin
()
end));
(

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____13849 = (solve_t env eq_prob (

let uu___2005_13851 = wl'
in {attempting = sub_probs; wl_deferred = uu___2005_13851.wl_deferred; ctr = uu___2005_13851.ctr; defer_ok = false; smt_ok = uu___2005_13851.smt_ok; umax_heuristic_ok = uu___2005_13851.umax_heuristic_ok; tcenv = uu___2005_13851.tcenv; wl_implicits = []}))
in (match (uu____13849) with
| Success (uu____13853, imps) -> begin
(

let wl2 = (

let uu___2011_13856 = wl'
in {attempting = rest; wl_deferred = uu___2011_13856.wl_deferred; ctr = uu___2011_13856.ctr; defer_ok = uu___2011_13856.defer_ok; smt_ok = uu___2011_13856.smt_ok; umax_heuristic_ok = uu___2011_13856.umax_heuristic_ok; tcenv = uu___2011_13856.tcenv; wl_implicits = uu___2011_13856.wl_implicits})
in (

let wl3 = (

let uu___2014_13858 = wl2
in {attempting = uu___2014_13858.attempting; wl_deferred = uu___2014_13858.wl_deferred; ctr = uu___2014_13858.ctr; defer_ok = uu___2014_13858.defer_ok; smt_ok = uu___2014_13858.smt_ok; umax_heuristic_ok = uu___2014_13858.umax_heuristic_ok; tcenv = uu___2014_13858.tcenv; wl_implicits = (FStar_List.append wl'.wl_implicits imps)})
in (

let g = (FStar_List.fold_left (fun g p -> (FStar_Syntax_Util.mk_conj g (p_guard p))) eq_prob.FStar_TypeChecker_Common.logical_guard sub_probs)
in (

let wl4 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) (FStar_Pervasives_Native.Some (g)) [] wl3)
in (

let uu____13874 = (FStar_List.fold_left (fun wl5 p -> (solve_prob' true p FStar_Pervasives_Native.None [] wl5)) wl4 bounds_probs)
in ((FStar_Syntax_Unionfind.commit tx);
(solve env wl4);
))))))
end
| Failed (p, msg) -> begin
((

let uu____13886 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____13886) with
| true -> begin
(

let uu____13891 = (

let uu____13893 = (FStar_List.map (prob_to_string env) ((FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs))
in (FStar_All.pipe_right uu____13893 (FStar_String.concat "\n")))
in (FStar_Util.print1 "meet/join attempted and failed to solve problems:\n%s\n" uu____13891))
end
| uu____13904 -> begin
()
end));
(

let uu____13906 = (

let uu____13921 = (base_and_refinement env bound_typ)
in ((rank1), (uu____13921)))
in (match (uu____13906) with
| (FStar_TypeChecker_Common.Rigid_flex, (t_base, FStar_Pervasives_Native.Some (uu____13943))) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(

let uu____13969 = (new_problem wl1 env t_base FStar_TypeChecker_Common.EQ this_flex FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "widened subtyping")
in (match (uu____13969) with
| (eq_prob1, wl2) -> begin
((def_check_prob "meet_or_join3" (FStar_TypeChecker_Common.TProb (eq_prob1)));
(

let wl3 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) (FStar_Pervasives_Native.Some ((p_guard (FStar_TypeChecker_Common.TProb (eq_prob1))))) [] wl2)
in (

let uu____13989 = (attempt ((FStar_TypeChecker_Common.TProb (eq_prob1))::[]) wl3)
in (solve env uu____13989)));
)
end));
)
end
| (FStar_TypeChecker_Common.Flex_rigid, (t_base, FStar_Pervasives_Native.Some (x, phi))) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(

let uu____14014 = (new_problem wl1 env t_base FStar_TypeChecker_Common.EQ this_flex FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "widened subtyping")
in (match (uu____14014) with
| (eq_prob1, wl2) -> begin
((def_check_prob "meet_or_join4" (FStar_TypeChecker_Common.TProb (eq_prob1)));
(

let phi1 = (guard_on_element wl2 tp x phi)
in (

let wl3 = (

let uu____14034 = (

let uu____14039 = (FStar_Syntax_Util.mk_conj phi1 (p_guard (FStar_TypeChecker_Common.TProb (eq_prob1))))
in FStar_Pervasives_Native.Some (uu____14039))
in (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) uu____14034 [] wl2))
in (

let uu____14045 = (attempt ((FStar_TypeChecker_Common.TProb (eq_prob1))::[]) wl3)
in (solve env uu____14045))));
)
end));
)
end
| uu____14046 -> begin
(

let uu____14061 = (FStar_Thunk.map (fun s -> (Prims.op_Hat "failed to solve the sub-problems: " s)) msg)
in (giveup env uu____14061 p))
end));
)
end)));
)
end))
end)))
end)))
end
| uu____14068 when flip -> begin
(

let uu____14069 = (

let uu____14071 = (FStar_Util.string_of_int (rank_t_num rank1))
in (

let uu____14073 = (prob_to_string env (FStar_TypeChecker_Common.TProb (tp)))
in (FStar_Util.format2 "Impossible: (rank=%s) Not a flex-rigid: %s" uu____14071 uu____14073)))
in (failwith uu____14069))
end
| uu____14076 -> begin
(

let uu____14077 = (

let uu____14079 = (FStar_Util.string_of_int (rank_t_num rank1))
in (

let uu____14081 = (prob_to_string env (FStar_TypeChecker_Common.TProb (tp)))
in (FStar_Util.format2 "Impossible: (rank=%s) Not a rigid-flex: %s" uu____14079 uu____14081)))
in (failwith uu____14077))
end))
end));
)
end))
end))));
))
and imitate_arrow : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Env.env  ->  worklist  ->  flex_t  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  solution = (fun orig env wl lhs bs_lhs t_res_lhs rel arrow1 -> (

let bs_lhs_args = (FStar_List.map (fun uu____14117 -> (match (uu____14117) with
| (x, i) -> begin
(

let uu____14136 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____14136), (i)))
end)) bs_lhs)
in (

let uu____14139 = lhs
in (match (uu____14139) with
| (uu____14140, u_lhs, uu____14142) -> begin
(

let imitate_comp = (fun bs bs_terms c wl1 -> (

let imitate_tot_or_gtot = (fun t uopt f wl2 -> (

let uu____14239 = (match (uopt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Util.type_u ())
end
| FStar_Pervasives_Native.Some (univ) -> begin
(

let uu____14249 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (univ)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in ((uu____14249), (univ)))
end)
in (match (uu____14239) with
| (k, univ) -> begin
(

let uu____14256 = (copy_uvar u_lhs (FStar_List.append bs_lhs bs) k wl2)
in (match (uu____14256) with
| (uu____14273, u, wl3) -> begin
(

let uu____14276 = (f u (FStar_Pervasives_Native.Some (univ)))
in ((uu____14276), (wl3)))
end))
end)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(imitate_tot_or_gtot t uopt FStar_Syntax_Syntax.mk_Total' wl1)
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(imitate_tot_or_gtot t uopt FStar_Syntax_Syntax.mk_GTotal' wl1)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____14302 = (

let uu____14315 = (

let uu____14326 = (FStar_Syntax_Syntax.as_arg ct.FStar_Syntax_Syntax.result_typ)
in (uu____14326)::ct.FStar_Syntax_Syntax.effect_args)
in (FStar_List.fold_right (fun uu____14377 uu____14378 -> (match (((uu____14377), (uu____14378))) with
| ((a, i), (out_args, wl2)) -> begin
(

let uu____14479 = (

let uu____14486 = (

let uu____14489 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____14489))
in (copy_uvar u_lhs [] uu____14486 wl2))
in (match (uu____14479) with
| (uu____14518, t_a, wl3) -> begin
(

let uu____14521 = (copy_uvar u_lhs bs t_a wl3)
in (match (uu____14521) with
| (uu____14540, a', wl4) -> begin
(((((a'), (i)))::out_args), (wl4))
end))
end))
end)) uu____14315 (([]), (wl1))))
in (match (uu____14302) with
| (out_args, wl2) -> begin
(

let ct' = (

let uu___2125_14596 = ct
in (

let uu____14597 = (

let uu____14600 = (FStar_List.hd out_args)
in (FStar_Pervasives_Native.fst uu____14600))
in (

let uu____14615 = (FStar_List.tl out_args)
in {FStar_Syntax_Syntax.comp_univs = uu___2125_14596.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___2125_14596.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____14597; FStar_Syntax_Syntax.effect_args = uu____14615; FStar_Syntax_Syntax.flags = uu___2125_14596.FStar_Syntax_Syntax.flags})))
in (((

let uu___2128_14633 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct'); FStar_Syntax_Syntax.pos = uu___2128_14633.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___2128_14633.FStar_Syntax_Syntax.vars})), (wl2)))
end))
end)))
in (

let uu____14636 = (FStar_Syntax_Util.arrow_formals_comp arrow1)
in (match (uu____14636) with
| (formals, c) -> begin
(

let rec aux = (fun bs bs_terms formals1 wl1 -> (match (formals1) with
| [] -> begin
(

let uu____14698 = (imitate_comp bs bs_terms c wl1)
in (match (uu____14698) with
| (c', wl2) -> begin
(

let lhs' = (FStar_Syntax_Util.arrow bs c')
in (

let sol = (

let uu____14709 = (

let uu____14714 = (FStar_Syntax_Util.abs bs_lhs lhs' (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot t_res_lhs))))
in ((u_lhs), (uu____14714)))
in TERM (uu____14709))
in (

let uu____14715 = (mk_t_problem wl2 [] orig lhs' rel arrow1 FStar_Pervasives_Native.None "arrow imitation")
in (match (uu____14715) with
| (sub_prob, wl3) -> begin
(

let uu____14729 = (

let uu____14730 = (solve_prob orig FStar_Pervasives_Native.None ((sol)::[]) wl3)
in (attempt ((sub_prob)::[]) uu____14730))
in (solve env uu____14729))
end))))
end))
end
| ((x, imp))::formals2 -> begin
(

let uu____14752 = (

let uu____14759 = (

let uu____14762 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____14762 FStar_Pervasives_Native.fst))
in (copy_uvar u_lhs (FStar_List.append bs_lhs bs) uu____14759 wl1))
in (match (uu____14752) with
| (_ctx_u_x, u_x, wl2) -> begin
(

let y = (

let uu____14783 = (

let uu____14786 = (FStar_Syntax_Syntax.range_of_bv x)
in FStar_Pervasives_Native.Some (uu____14786))
in (FStar_Syntax_Syntax.new_bv uu____14783 u_x))
in (

let uu____14787 = (

let uu____14790 = (

let uu____14793 = (

let uu____14794 = (FStar_Syntax_Syntax.bv_to_name y)
in ((uu____14794), (imp)))
in (uu____14793)::[])
in (FStar_List.append bs_terms uu____14790))
in (aux (FStar_List.append bs ((((y), (imp)))::[])) uu____14787 formals2 wl2)))
end))
end))
in (

let uu____14821 = (occurs_check u_lhs arrow1)
in (match (uu____14821) with
| (uu____14834, occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____14850 = (FStar_Thunk.mk (fun uu____14854 -> (

let uu____14855 = (FStar_Option.get msg)
in (Prims.op_Hat "occurs-check failed: " uu____14855))))
in (giveup_or_defer env orig wl uu____14850))
end
| uu____14859 -> begin
(aux [] [] formals wl)
end)
end)))
end)))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (worklist  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  (FStar_TypeChecker_Common.prob * worklist))  ->  solution = (fun env bs1 bs2 orig wl rhs -> ((

let uu____14888 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14888) with
| true -> begin
(

let uu____14893 = (FStar_Syntax_Print.binders_to_string ", " bs1)
in (

let uu____14896 = (FStar_Syntax_Print.binders_to_string ", " bs2)
in (FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n" uu____14893 (rel_to_string (p_rel orig)) uu____14896)))
end
| uu____14900 -> begin
()
end));
(

let rec aux = (fun wl1 scope env1 subst1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
(

let uu____15027 = (rhs wl1 scope env1 subst1)
in (match (uu____15027) with
| (rhs_prob, wl2) -> begin
((

let uu____15050 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____15050) with
| true -> begin
(

let uu____15055 = (prob_to_string env1 rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" uu____15055))
end
| uu____15058 -> begin
()
end));
(

let formula = (p_guard rhs_prob)
in ((env1), (FStar_Util.Inl ((((rhs_prob)::[]), (formula)))), (wl2)));
)
end))
end
| (((hd1, imp))::xs1, ((hd2, imp'))::ys1) when (

let uu____15133 = (FStar_Syntax_Util.eq_aqual imp imp')
in (Prims.op_Equality uu____15133 FStar_Syntax_Util.Equal)) -> begin
(

let hd11 = (

let uu___2198_15135 = hd1
in (

let uu____15136 = (FStar_Syntax_Subst.subst subst1 hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___2198_15135.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2198_15135.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____15136}))
in (

let hd21 = (

let uu___2201_15140 = hd2
in (

let uu____15141 = (FStar_Syntax_Subst.subst subst1 hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___2201_15140.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2201_15140.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____15141}))
in (

let uu____15144 = (

let uu____15149 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_t_problem wl1 scope orig hd11.FStar_Syntax_Syntax.sort uu____15149 hd21.FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None "Formal parameter"))
in (match (uu____15144) with
| (prob, wl2) -> begin
(

let hd12 = (FStar_Syntax_Syntax.freshen_bv hd11)
in (

let subst2 = (

let uu____15172 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd12))))::uu____15172)
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 hd12)
in (

let uu____15179 = (aux wl2 (FStar_List.append scope ((((hd12), (imp)))::[])) env2 subst2 xs1 ys1)
in (match (uu____15179) with
| (env3, FStar_Util.Inl (sub_probs, phi), wl3) -> begin
(

let phi1 = (

let uu____15251 = (FStar_TypeChecker_Env.close_forall env3 ((((hd12), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj (p_guard prob) uu____15251))
in ((

let uu____15269 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env3) (FStar_Options.Other ("Rel")))
in (match (uu____15269) with
| true -> begin
(

let uu____15274 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____15276 = (FStar_Syntax_Print.bv_to_string hd12)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" uu____15274 uu____15276)))
end
| uu____15279 -> begin
()
end));
((env3), (FStar_Util.Inl ((((prob)::sub_probs), (phi1)))), (wl3));
))
end
| fail1 -> begin
fail1
end)))))
end))))
end
| uu____15311 -> begin
((env1), (FStar_Util.Inr ("arity or argument-qualifier mismatch")), (wl1))
end))
in (

let uu____15347 = (aux wl [] env [] bs1 bs2)
in (match (uu____15347) with
| (env1, FStar_Util.Inr (msg), wl1) -> begin
(giveup_lit env1 msg orig)
end
| (env1, FStar_Util.Inl (sub_probs, phi), wl1) -> begin
(

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some (phi)) [] wl1)
in (

let uu____15406 = (attempt sub_probs wl2)
in (solve env1 uu____15406)))
end)));
))
and try_solve_without_smt_or_else : FStar_TypeChecker_Env.env  ->  worklist  ->  (FStar_TypeChecker_Env.env  ->  worklist  ->  solution)  ->  (FStar_TypeChecker_Env.env  ->  worklist  ->  (FStar_TypeChecker_Common.prob * lstring)  ->  solution)  ->  solution = (fun env wl try_solve else_solve -> (

let wl' = (

let uu___2239_15426 = wl
in {attempting = []; wl_deferred = []; ctr = uu___2239_15426.ctr; defer_ok = false; smt_ok = false; umax_heuristic_ok = false; tcenv = uu___2239_15426.tcenv; wl_implicits = []})
in (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____15438 = (try_solve env wl')
in (match (uu____15438) with
| Success (uu____15439, imps) -> begin
((FStar_Syntax_Unionfind.commit tx);
(

let wl1 = (

let uu___2248_15443 = wl
in {attempting = uu___2248_15443.attempting; wl_deferred = uu___2248_15443.wl_deferred; ctr = uu___2248_15443.ctr; defer_ok = uu___2248_15443.defer_ok; smt_ok = uu___2248_15443.smt_ok; umax_heuristic_ok = uu___2248_15443.umax_heuristic_ok; tcenv = uu___2248_15443.tcenv; wl_implicits = (FStar_List.append wl.wl_implicits imps)})
in (solve env wl1));
)
end
| Failed (p, s) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(else_solve env wl ((p), (s)));
)
end)))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> ((def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb (problem)));
(

let uu____15452 = (compress_tprob wl.tcenv problem)
in (solve_t' env uu____15452 wl));
))
and solve_t_flex_rigid_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  flex_t  ->  FStar_Syntax_Syntax.term  ->  solution = (fun env orig wl lhs rhs -> (

let binders_as_bv_set = (fun bs -> (

let uu____15466 = (FStar_List.map FStar_Pervasives_Native.fst bs)
in (FStar_Util.as_set uu____15466 FStar_Syntax_Syntax.order_bv)))
in (

let mk_solution = (fun env1 lhs1 bs rhs1 -> (

let uu____15500 = lhs1
in (match (uu____15500) with
| (uu____15503, ctx_u, uu____15505) -> begin
(

let sol = (match (bs) with
| [] -> begin
rhs1
end
| uu____15513 -> begin
(

let uu____15514 = (sn_binders env1 bs)
in (u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ uu____15514 rhs1))
end)
in (TERM (((ctx_u), (sol))))::[])
end)))
in (

let try_quasi_pattern = (fun orig1 env1 wl1 lhs1 rhs1 -> (

let uu____15563 = (quasi_pattern env1 lhs1)
in (match (uu____15563) with
| FStar_Pervasives_Native.None -> begin
((FStar_Util.Inl ("Not a quasi-pattern")), (wl1))
end
| FStar_Pervasives_Native.Some (bs, uu____15597) -> begin
(

let uu____15602 = lhs1
in (match (uu____15602) with
| (t_lhs, ctx_u, args) -> begin
(

let uu____15617 = (occurs_check ctx_u rhs1)
in (match (uu____15617) with
| (uvars1, occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____15668 = (

let uu____15676 = (

let uu____15678 = (FStar_Option.get msg)
in (Prims.op_Hat "quasi-pattern, occurs-check failed: " uu____15678))
in FStar_Util.Inl (uu____15676))
in ((uu____15668), (wl1)))
end
| uu____15692 -> begin
(

let fvs_lhs = (binders_as_bv_set (FStar_List.append ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders bs))
in (

let fvs_rhs = (FStar_Syntax_Free.names rhs1)
in (

let uu____15706 = (

let uu____15708 = (FStar_Util.set_is_subset_of fvs_rhs fvs_lhs)
in (not (uu____15708)))
in (match (uu____15706) with
| true -> begin
((FStar_Util.Inl ("quasi-pattern, free names on the RHS are not included in the LHS")), (wl1))
end
| uu____15733 -> begin
(

let uu____15735 = (

let uu____15743 = (mk_solution env1 lhs1 bs rhs1)
in FStar_Util.Inr (uu____15743))
in (

let uu____15749 = (restrict_all_uvars ctx_u uvars1 wl1)
in ((uu____15735), (uu____15749))))
end))))
end)
end))
end))
end)))
in (

let imitate_app = (fun orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 -> (

let uu____15793 = (FStar_Syntax_Util.head_and_args rhs1)
in (match (uu____15793) with
| (rhs_hd, args) -> begin
(

let uu____15836 = (FStar_Util.prefix args)
in (match (uu____15836) with
| (args_rhs, last_arg_rhs) -> begin
(

let rhs' = (FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs FStar_Pervasives_Native.None rhs1.FStar_Syntax_Syntax.pos)
in (

let uu____15908 = lhs1
in (match (uu____15908) with
| (t_lhs, u_lhs, _lhs_args) -> begin
(

let uu____15912 = (

let uu____15923 = (

let uu____15930 = (

let uu____15933 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____15933))
in (copy_uvar u_lhs [] uu____15930 wl1))
in (match (uu____15923) with
| (uu____15960, t_last_arg, wl2) -> begin
(

let uu____15963 = (

let uu____15970 = (

let uu____15971 = (

let uu____15980 = (FStar_Syntax_Syntax.null_binder t_last_arg)
in (uu____15980)::[])
in (FStar_List.append bs_lhs uu____15971))
in (copy_uvar u_lhs uu____15970 t_res_lhs wl2))
in (match (uu____15963) with
| (uu____16015, lhs', wl3) -> begin
(

let uu____16018 = (copy_uvar u_lhs bs_lhs t_last_arg wl3)
in (match (uu____16018) with
| (uu____16035, lhs'_last_arg, wl4) -> begin
((lhs'), (lhs'_last_arg), (wl4))
end))
end))
end))
in (match (uu____15912) with
| (lhs', lhs'_last_arg, wl2) -> begin
(

let sol = (

let uu____16056 = (

let uu____16057 = (

let uu____16062 = (

let uu____16063 = (

let uu____16066 = (

let uu____16071 = (

let uu____16072 = (FStar_Syntax_Syntax.as_arg lhs'_last_arg)
in (uu____16072)::[])
in (FStar_Syntax_Syntax.mk_Tm_app lhs' uu____16071))
in (uu____16066 FStar_Pervasives_Native.None t_lhs.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.abs bs_lhs uu____16063 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot t_res_lhs)))))
in ((u_lhs), (uu____16062)))
in TERM (uu____16057))
in (uu____16056)::[])
in (

let uu____16097 = (

let uu____16104 = (mk_t_problem wl2 [] orig1 lhs' FStar_TypeChecker_Common.EQ rhs' FStar_Pervasives_Native.None "first-order lhs")
in (match (uu____16104) with
| (p1, wl3) -> begin
(

let uu____16124 = (mk_t_problem wl3 [] orig1 lhs'_last_arg FStar_TypeChecker_Common.EQ (FStar_Pervasives_Native.fst last_arg_rhs) FStar_Pervasives_Native.None "first-order rhs")
in (match (uu____16124) with
| (p2, wl4) -> begin
(((p1)::(p2)::[]), (wl4))
end))
end))
in (match (uu____16097) with
| (sub_probs, wl3) -> begin
(

let uu____16156 = (

let uu____16157 = (solve_prob orig1 FStar_Pervasives_Native.None sol wl3)
in (attempt sub_probs uu____16157))
in (solve env1 uu____16156))
end)))
end))
end)))
end))
end)))
in (

let first_order = (fun orig1 env1 wl1 lhs1 rhs1 -> (

let is_app = (fun rhs2 -> (

let uu____16191 = (FStar_Syntax_Util.head_and_args rhs2)
in (match (uu____16191) with
| (uu____16209, args) -> begin
(match (args) with
| [] -> begin
false
end
| uu____16245 -> begin
true
end)
end)))
in (

let is_arrow = (fun rhs2 -> (

let uu____16264 = (

let uu____16265 = (FStar_Syntax_Subst.compress rhs2)
in uu____16265.FStar_Syntax_Syntax.n)
in (match (uu____16264) with
| FStar_Syntax_Syntax.Tm_arrow (uu____16269) -> begin
true
end
| uu____16285 -> begin
false
end)))
in (

let uu____16287 = (quasi_pattern env1 lhs1)
in (match (uu____16287) with
| FStar_Pervasives_Native.None -> begin
(

let msg = (FStar_Thunk.mk (fun uu____16305 -> (

let uu____16306 = (prob_to_string env1 orig1)
in (FStar_Util.format1 "first_order heuristic cannot solve %s; lhs not a quasi-pattern" uu____16306))))
in (giveup_or_defer env1 orig1 wl1 msg))
end
| FStar_Pervasives_Native.Some (bs_lhs, t_res_lhs) -> begin
(

let uu____16315 = (is_app rhs1)
in (match (uu____16315) with
| true -> begin
(imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1)
end
| uu____16318 -> begin
(

let uu____16320 = (is_arrow rhs1)
in (match (uu____16320) with
| true -> begin
(imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs FStar_TypeChecker_Common.EQ rhs1)
end
| uu____16323 -> begin
(

let msg = (FStar_Thunk.mk (fun uu____16332 -> (

let uu____16333 = (prob_to_string env1 orig1)
in (FStar_Util.format1 "first_order heuristic cannot solve %s; rhs not an app or arrow" uu____16333))))
in (giveup_or_defer env1 orig1 wl1 msg))
end))
end))
end)))))
in (match ((p_rel orig)) with
| FStar_TypeChecker_Common.SUB -> begin
(match (wl.defer_ok) with
| true -> begin
(

let uu____16337 = (FStar_Thunk.mkv "flex-rigid subtyping")
in (giveup_or_defer env orig wl uu____16337))
end
| uu____16340 -> begin
(solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.SUBINV -> begin
(match (wl.defer_ok) with
| true -> begin
(

let uu____16343 = (FStar_Thunk.mkv "flex-rigid subtyping")
in (giveup_or_defer env orig wl uu____16343))
end
| uu____16346 -> begin
(solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.EQ -> begin
(

let uu____16348 = lhs
in (match (uu____16348) with
| (_t1, ctx_uv, args_lhs) -> begin
(

let uu____16352 = (pat_vars env ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs)
in (match (uu____16352) with
| FStar_Pervasives_Native.Some (lhs_binders) -> begin
(

let rhs1 = (sn env rhs)
in (

let names_to_string1 = (fun fvs -> (

let uu____16370 = (

let uu____16374 = (FStar_Util.set_elements fvs)
in (FStar_List.map FStar_Syntax_Print.bv_to_string uu____16374))
in (FStar_All.pipe_right uu____16370 (FStar_String.concat ", "))))
in (

let fvs1 = (binders_as_bv_set (FStar_List.append ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders lhs_binders))
in (

let fvs2 = (FStar_Syntax_Free.names rhs1)
in (

let uu____16395 = (occurs_check ctx_uv rhs1)
in (match (uu____16395) with
| (uvars1, occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____16424 = (

let uu____16425 = (

let uu____16427 = (FStar_Option.get msg)
in (Prims.op_Hat "occurs-check failed: " uu____16427))
in (FStar_All.pipe_left FStar_Thunk.mkv uu____16425))
in (giveup_or_defer env orig wl uu____16424))
end
| uu____16433 -> begin
(

let uu____16435 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____16435) with
| true -> begin
(

let sol = (mk_solution env lhs lhs_binders rhs1)
in (

let wl1 = (restrict_all_uvars ctx_uv uvars1 wl)
in (

let uu____16442 = (solve_prob orig FStar_Pervasives_Native.None sol wl1)
in (solve env uu____16442))))
end
| uu____16443 -> begin
(match (wl.defer_ok) with
| true -> begin
(

let msg1 = (FStar_Thunk.mk (fun uu____16455 -> (

let uu____16456 = (names_to_string1 fvs2)
in (

let uu____16458 = (names_to_string1 fvs1)
in (

let uu____16460 = (FStar_Syntax_Print.binders_to_string ", " (FStar_List.append ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders lhs_binders))
in (FStar_Util.format3 "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}" uu____16456 uu____16458 uu____16460))))))
in (giveup_or_defer env orig wl msg1))
end
| uu____16470 -> begin
(first_order orig env wl lhs rhs1)
end)
end))
end)
end))))))
end
| uu____16472 -> begin
(match (wl.defer_ok) with
| true -> begin
(

let uu____16476 = (FStar_Thunk.mkv "Not a pattern")
in (giveup_or_defer env orig wl uu____16476))
end
| uu____16479 -> begin
(

let uu____16481 = (try_quasi_pattern orig env wl lhs rhs)
in (match (uu____16481) with
| (FStar_Util.Inr (sol), wl1) -> begin
(

let uu____16507 = (solve_prob orig FStar_Pervasives_Native.None sol wl1)
in (solve env uu____16507))
end
| (FStar_Util.Inl (msg), uu____16509) -> begin
(first_order orig env wl lhs rhs)
end))
end)
end))
end))
end)))))))
and solve_t_flex_flex : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  flex_t  ->  flex_t  ->  solution = (fun env orig wl lhs rhs -> (match ((p_rel orig)) with
| FStar_TypeChecker_Common.SUB -> begin
(match (wl.defer_ok) with
| true -> begin
(

let uu____16527 = (FStar_Thunk.mkv "flex-flex subtyping")
in (giveup_or_defer env orig wl uu____16527))
end
| uu____16530 -> begin
(solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.SUBINV -> begin
(match (wl.defer_ok) with
| true -> begin
(

let uu____16533 = (FStar_Thunk.mkv "flex-flex subtyping")
in (giveup_or_defer env orig wl uu____16533))
end
| uu____16536 -> begin
(solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.EQ -> begin
(match ((wl.defer_ok && ((not ((is_flex_pat lhs))) || (not ((is_flex_pat rhs)))))) with
| true -> begin
(

let uu____16555 = (FStar_Thunk.mkv "flex-flex non-pattern")
in (giveup_or_defer env orig wl uu____16555))
end
| uu____16558 -> begin
(

let uu____16560 = (

let uu____16577 = (quasi_pattern env lhs)
in (

let uu____16584 = (quasi_pattern env rhs)
in ((uu____16577), (uu____16584))))
in (match (uu____16560) with
| (FStar_Pervasives_Native.Some (binders_lhs, t_res_lhs), FStar_Pervasives_Native.Some (binders_rhs, t_res_rhs)) -> begin
(

let uu____16627 = lhs
in (match (uu____16627) with
| ({FStar_Syntax_Syntax.n = uu____16628; FStar_Syntax_Syntax.pos = range; FStar_Syntax_Syntax.vars = uu____16630}, u_lhs, uu____16632) -> begin
(

let uu____16635 = rhs
in (match (uu____16635) with
| (uu____16636, u_rhs, uu____16638) -> begin
(

let uu____16639 = ((FStar_Syntax_Unionfind.equiv u_lhs.FStar_Syntax_Syntax.ctx_uvar_head u_rhs.FStar_Syntax_Syntax.ctx_uvar_head) && (binders_eq binders_lhs binders_rhs))
in (match (uu____16639) with
| true -> begin
(

let uu____16646 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____16646))
end
| uu____16647 -> begin
(

let uu____16649 = (maximal_prefix u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders)
in (match (uu____16649) with
| (ctx_w, (ctx_l, ctx_r)) -> begin
(

let gamma_w = (gamma_until u_lhs.FStar_Syntax_Syntax.ctx_uvar_gamma ctx_w)
in (

let zs = (intersect_binders gamma_w (FStar_List.append ctx_l binders_lhs) (FStar_List.append ctx_r binders_rhs))
in (

let uu____16681 = (

let uu____16688 = (

let uu____16691 = (FStar_Syntax_Syntax.mk_Total t_res_lhs)
in (FStar_Syntax_Util.arrow zs uu____16691))
in (new_uvar (Prims.op_Hat "flex-flex quasi:" (Prims.op_Hat "\tlhs=" (Prims.op_Hat u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason (Prims.op_Hat "\trhs=" u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason)))) wl range gamma_w ctx_w uu____16688 FStar_Syntax_Syntax.Strict FStar_Pervasives_Native.None))
in (match (uu____16681) with
| (uu____16703, w, wl1) -> begin
(

let w_app = (

let uu____16709 = (

let uu____16714 = (FStar_List.map (fun uu____16725 -> (match (uu____16725) with
| (z, uu____16733) -> begin
(

let uu____16738 = (FStar_Syntax_Syntax.bv_to_name z)
in (FStar_Syntax_Syntax.as_arg uu____16738))
end)) zs)
in (FStar_Syntax_Syntax.mk_Tm_app w uu____16714))
in (uu____16709 FStar_Pervasives_Native.None w.FStar_Syntax_Syntax.pos))
in ((

let uu____16740 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____16740) with
| true -> begin
(

let uu____16745 = (

let uu____16749 = (flex_t_to_string lhs)
in (

let uu____16751 = (

let uu____16755 = (flex_t_to_string rhs)
in (

let uu____16757 = (

let uu____16761 = (term_to_string w)
in (

let uu____16763 = (

let uu____16767 = (FStar_Syntax_Print.binders_to_string ", " (FStar_List.append ctx_l binders_lhs))
in (

let uu____16776 = (

let uu____16780 = (FStar_Syntax_Print.binders_to_string ", " (FStar_List.append ctx_r binders_rhs))
in (

let uu____16789 = (

let uu____16793 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (uu____16793)::[])
in (uu____16780)::uu____16789))
in (uu____16767)::uu____16776))
in (uu____16761)::uu____16763))
in (uu____16755)::uu____16757))
in (uu____16749)::uu____16751))
in (FStar_Util.print "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n" uu____16745))
end
| uu____16804 -> begin
()
end));
(

let sol = (

let s1 = (

let uu____16810 = (

let uu____16815 = (FStar_Syntax_Util.abs binders_lhs w_app (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot t_res_lhs))))
in ((u_lhs), (uu____16815)))
in TERM (uu____16810))
in (

let uu____16816 = (FStar_Syntax_Unionfind.equiv u_lhs.FStar_Syntax_Syntax.ctx_uvar_head u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____16816) with
| true -> begin
(s1)::[]
end
| uu____16821 -> begin
(

let s2 = (

let uu____16824 = (

let uu____16829 = (FStar_Syntax_Util.abs binders_rhs w_app (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot t_res_lhs))))
in ((u_rhs), (uu____16829)))
in TERM (uu____16824))
in (s1)::(s2)::[])
end)))
in (

let uu____16830 = (solve_prob orig FStar_Pervasives_Native.None sol wl1)
in (solve env uu____16830)));
))
end))))
end))
end))
end))
end))
end
| uu____16831 -> begin
(

let uu____16848 = (FStar_Thunk.mkv "flex-flex: non-patterns")
in (giveup_or_defer env orig wl uu____16848))
end))
end)
end))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> ((def_check_prob "solve_t\'.1" (FStar_TypeChecker_Common.TProb (problem)));
(

let giveup_or_defer1 = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_heads_match = (fun env1 need_unif torig wl1 t1 t2 -> (

let orig = FStar_TypeChecker_Common.TProb (torig)
in ((

let uu____16902 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____16902) with
| true -> begin
(

let uu____16907 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____16909 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____16911 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____16913 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n" (match (need_unif) with
| true -> begin
"need unification"
end
| uu____16919 -> begin
"match"
end) uu____16907 uu____16909 uu____16911 uu____16913)))))
end
| uu____16922 -> begin
()
end));
(

let uu____16924 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____16924) with
| (head1, args1) -> begin
(

let uu____16967 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____16967) with
| (head2, args2) -> begin
(

let solve_head_then = (fun wl2 k -> (match (need_unif) with
| true -> begin
(k true wl2)
end
| uu____17035 -> begin
(

let uu____17037 = (solve_maybe_uinsts env1 orig head1 head2 wl2)
in (match (uu____17037) with
| USolved (wl3) -> begin
(k true wl3)
end
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl3) -> begin
(

let uu____17042 = (defer_lit "universe constraints" orig wl3)
in (k false uu____17042))
end))
end))
in (

let nargs = (FStar_List.length args1)
in (match ((Prims.op_disEquality nargs (FStar_List.length args2))) with
| true -> begin
(

let uu____17063 = (FStar_Thunk.mk (fun uu____17070 -> (

let uu____17071 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____17073 = (args_to_string args1)
in (

let uu____17077 = (FStar_Syntax_Print.term_to_string head2)
in (

let uu____17079 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____17071 uu____17073 uu____17077 uu____17079)))))))
in (giveup env1 uu____17063 orig))
end
| uu____17084 -> begin
(

let uu____17086 = ((Prims.op_Equality nargs (Prims.parse_int "0")) || (

let uu____17091 = (FStar_Syntax_Util.eq_args args1 args2)
in (Prims.op_Equality uu____17091 FStar_Syntax_Util.Equal)))
in (match (uu____17086) with
| true -> begin
(match (need_unif) with
| true -> begin
(solve_t env1 (

let uu___2504_17095 = problem
in {FStar_TypeChecker_Common.pid = uu___2504_17095.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = head1; FStar_TypeChecker_Common.relation = uu___2504_17095.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = head2; FStar_TypeChecker_Common.element = uu___2504_17095.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___2504_17095.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___2504_17095.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___2504_17095.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___2504_17095.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___2504_17095.FStar_TypeChecker_Common.rank}) wl1)
end
| uu____17096 -> begin
(solve_head_then wl1 (fun ok wl2 -> (match (ok) with
| true -> begin
(

let uu____17105 = (solve_prob orig FStar_Pervasives_Native.None [] wl2)
in (solve env1 uu____17105))
end
| uu____17106 -> begin
(solve env1 wl2)
end)))
end)
end
| uu____17108 -> begin
(

let uu____17110 = (base_and_refinement env1 t1)
in (match (uu____17110) with
| (base1, refinement1) -> begin
(

let uu____17135 = (base_and_refinement env1 t2)
in (match (uu____17135) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(

let mk_sub_probs = (fun wl2 -> (

let argp = (match (need_unif) with
| true -> begin
(FStar_List.zip ((((head1), (FStar_Pervasives_Native.None)))::args1) ((((head2), (FStar_Pervasives_Native.None)))::args2))
end
| uu____17282 -> begin
(FStar_List.zip args1 args2)
end)
in (

let uu____17300 = (FStar_List.fold_right (fun uu____17340 uu____17341 -> (match (((uu____17340), (uu____17341))) with
| (((a1, uu____17393), (a2, uu____17395)), (probs, wl3)) -> begin
(

let uu____17444 = (mk_problem wl3 [] orig a1 FStar_TypeChecker_Common.EQ a2 FStar_Pervasives_Native.None "index")
in (match (uu____17444) with
| (prob', wl4) -> begin
(((FStar_TypeChecker_Common.TProb (prob'))::probs), (wl4))
end))
end)) argp (([]), (wl2)))
in (match (uu____17300) with
| (subprobs, wl3) -> begin
((

let uu____17487 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____17487) with
| true -> begin
(

let uu____17492 = (FStar_Syntax_Print.list_to_string (prob_to_string env1) subprobs)
in (FStar_Util.print1 "Adding subproblems for arguments: %s" uu____17492))
end
| uu____17495 -> begin
()
end));
(

let uu____17498 = (FStar_Options.defensive ())
in (match (uu____17498) with
| true -> begin
(FStar_List.iter (def_check_prob "solve_t\' subprobs") subprobs)
end
| uu____17502 -> begin
()
end));
((subprobs), (wl3));
)
end))))
in (

let solve_sub_probs = (fun env2 wl2 -> (solve_head_then wl2 (fun ok wl3 -> (match ((not (ok))) with
| true -> begin
(solve env2 wl3)
end
| uu____17523 -> begin
(

let uu____17525 = (mk_sub_probs wl3)
in (match (uu____17525) with
| (subprobs, wl4) -> begin
(

let formula = (

let uu____17541 = (FStar_List.map (fun p -> (p_guard p)) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____17541))
in (

let wl5 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) [] wl4)
in (

let uu____17549 = (attempt subprobs wl5)
in (solve env2 uu____17549))))
end))
end))))
in (

let solve_sub_probs_no_smt = (fun env2 wl2 -> (solve_head_then wl2 (fun ok wl3 -> (

let uu____17573 = (mk_sub_probs wl3)
in (match (uu____17573) with
| (subprobs, wl4) -> begin
(

let wl5 = (solve_prob orig FStar_Pervasives_Native.None [] wl4)
in (

let uu____17587 = (attempt subprobs wl5)
in (solve env2 uu____17587)))
end)))))
in (

let unfold_and_retry = (fun d env2 wl2 uu____17615 -> (match (uu____17615) with
| (prob, reason) -> begin
((

let uu____17632 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____17632) with
| true -> begin
(

let uu____17637 = (prob_to_string env2 orig)
in (

let uu____17639 = (prob_to_string env2 prob)
in (

let uu____17641 = (FStar_Thunk.force reason)
in (FStar_Util.print3 "Failed to solve %s because sub-problem %s is not solvable without SMT because %s" uu____17637 uu____17639 uu____17641))))
end
| uu____17645 -> begin
()
end));
(

let uu____17647 = (

let uu____17656 = (FStar_TypeChecker_Normalize.unfold_head_once env2 t1)
in (

let uu____17659 = (FStar_TypeChecker_Normalize.unfold_head_once env2 t2)
in ((uu____17656), (uu____17659))))
in (match (uu____17647) with
| (FStar_Pervasives_Native.Some (t1'), FStar_Pervasives_Native.Some (t2')) -> begin
(

let uu____17672 = (FStar_Syntax_Util.head_and_args t1')
in (match (uu____17672) with
| (head1', uu____17690) -> begin
(

let uu____17715 = (FStar_Syntax_Util.head_and_args t2')
in (match (uu____17715) with
| (head2', uu____17733) -> begin
(

let uu____17758 = (

let uu____17763 = (FStar_Syntax_Util.eq_tm head1' head1)
in (

let uu____17764 = (FStar_Syntax_Util.eq_tm head2' head2)
in ((uu____17763), (uu____17764))))
in (match (uu____17758) with
| (FStar_Syntax_Util.Equal, FStar_Syntax_Util.Equal) -> begin
((

let uu____17766 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____17766) with
| true -> begin
(

let uu____17771 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____17773 = (FStar_Syntax_Print.term_to_string t1')
in (

let uu____17775 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____17777 = (FStar_Syntax_Print.term_to_string t2')
in (FStar_Util.print4 "Unfolding didn\'t make progress ... got %s ~> %s;\nand %s ~> %s\n" uu____17771 uu____17773 uu____17775 uu____17777)))))
end
| uu____17780 -> begin
()
end));
(solve_sub_probs env2 wl2);
)
end
| uu____17782 -> begin
(

let torig' = (

let uu___2590_17790 = torig
in {FStar_TypeChecker_Common.pid = uu___2590_17790.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1'; FStar_TypeChecker_Common.relation = uu___2590_17790.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2'; FStar_TypeChecker_Common.element = uu___2590_17790.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___2590_17790.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___2590_17790.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___2590_17790.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___2590_17790.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___2590_17790.FStar_TypeChecker_Common.rank})
in ((

let uu____17792 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____17792) with
| true -> begin
(

let uu____17797 = (prob_to_string env2 (FStar_TypeChecker_Common.TProb (torig')))
in (FStar_Util.print1 "Unfolded and now trying %s\n" uu____17797))
end
| uu____17800 -> begin
()
end));
(solve_t env2 torig' wl2);
))
end))
end))
end))
end
| uu____17802 -> begin
(solve_sub_probs env2 wl2)
end));
)
end))
in (

let d = (

let uu____17814 = (delta_depth_of_term env1 head1)
in (match (uu____17814) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(FStar_TypeChecker_Common.decr_delta_depth d)
end))
in (

let treat_as_injective = (

let uu____17822 = (

let uu____17823 = (FStar_Syntax_Util.un_uinst head1)
in uu____17823.FStar_Syntax_Syntax.n)
in (match (uu____17822) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_TypeChecker_Env.fv_has_attr env1 fv FStar_Parser_Const.unifier_hint_injective_lid)
end
| uu____17828 -> begin
false
end))
in (match (d) with
| FStar_Pervasives_Native.Some (d1) when (wl1.smt_ok && (not (treat_as_injective))) -> begin
(try_solve_without_smt_or_else env1 wl1 solve_sub_probs_no_smt (unfold_and_retry d1))
end
| uu____17831 -> begin
(solve_sub_probs env1 wl1)
end)))))))
end
| uu____17834 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env1 (

let uu___2610_17870 = problem
in {FStar_TypeChecker_Common.pid = uu___2610_17870.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___2610_17870.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___2610_17870.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___2610_17870.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___2610_17870.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___2610_17870.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___2610_17870.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___2610_17870.FStar_TypeChecker_Common.rank}) wl1)))
end)
end))
end))
end))
end)))
end))
end));
)))
in (

let try_match_heuristic = (fun env1 orig wl1 s1 s2 t1t2_opt -> (

let try_solve_branch = (fun scrutinee p -> (

let uu____17946 = (destruct_flex_t scrutinee wl1)
in (match (uu____17946) with
| ((_t, uv, _args), wl2) -> begin
(

let uu____17957 = (FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p)
in (match (uu____17957) with
| (xs, pat_term, uu____17973, uu____17974) -> begin
(

let uu____17979 = (FStar_List.fold_left (fun uu____18002 x -> (match (uu____18002) with
| (subst1, wl3) -> begin
(

let t_x = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____18023 = (copy_uvar uv [] t_x wl3)
in (match (uu____18023) with
| (uu____18042, u, wl4) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (u))))::subst1
in ((subst2), (wl4)))
end)))
end)) (([]), (wl2)) xs)
in (match (uu____17979) with
| (subst1, wl3) -> begin
(

let pat_term1 = (FStar_Syntax_Subst.subst subst1 pat_term)
in (

let uu____18063 = (new_problem wl3 env1 scrutinee FStar_TypeChecker_Common.EQ pat_term1 FStar_Pervasives_Native.None scrutinee.FStar_Syntax_Syntax.pos "match heuristic")
in (match (uu____18063) with
| (prob, wl4) -> begin
(

let wl' = (

let uu___2650_18080 = wl4
in {attempting = (FStar_TypeChecker_Common.TProb (prob))::[]; wl_deferred = []; ctr = uu___2650_18080.ctr; defer_ok = false; smt_ok = false; umax_heuristic_ok = uu___2650_18080.umax_heuristic_ok; tcenv = uu___2650_18080.tcenv; wl_implicits = []})
in (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____18091 = (solve env1 wl')
in (match (uu____18091) with
| Success (uu____18094, imps) -> begin
(

let wl'1 = (

let uu___2658_18097 = wl'
in {attempting = (orig)::[]; wl_deferred = uu___2658_18097.wl_deferred; ctr = uu___2658_18097.ctr; defer_ok = uu___2658_18097.defer_ok; smt_ok = uu___2658_18097.smt_ok; umax_heuristic_ok = uu___2658_18097.umax_heuristic_ok; tcenv = uu___2658_18097.tcenv; wl_implicits = uu___2658_18097.wl_implicits})
in (

let uu____18098 = (solve env1 wl'1)
in (match (uu____18098) with
| Success (uu____18101, imps') -> begin
((FStar_Syntax_Unionfind.commit tx);
FStar_Pervasives_Native.Some ((

let uu___2666_18105 = wl4
in {attempting = uu___2666_18105.attempting; wl_deferred = uu___2666_18105.wl_deferred; ctr = uu___2666_18105.ctr; defer_ok = uu___2666_18105.defer_ok; smt_ok = uu___2666_18105.smt_ok; umax_heuristic_ok = uu___2666_18105.umax_heuristic_ok; tcenv = uu___2666_18105.tcenv; wl_implicits = (FStar_List.append wl4.wl_implicits (FStar_List.append imps imps'))}));
)
end
| Failed (uu____18106) -> begin
((FStar_Syntax_Unionfind.rollback tx);
FStar_Pervasives_Native.None;
)
end)))
end
| uu____18112 -> begin
((FStar_Syntax_Unionfind.rollback tx);
FStar_Pervasives_Native.None;
)
end))))
end)))
end))
end))
end)))
in (match (t1t2_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inr (FStar_Pervasives_Native.None)
end
| FStar_Pervasives_Native.Some (t1, t2) -> begin
((

let uu____18135 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____18135) with
| true -> begin
(

let uu____18140 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____18142 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying match heuristic for %s vs. %s\n" uu____18140 uu____18142)))
end
| uu____18145 -> begin
()
end));
(

let uu____18147 = (

let uu____18168 = (

let uu____18177 = (FStar_Syntax_Util.unmeta t1)
in ((s1), (uu____18177)))
in (

let uu____18184 = (

let uu____18193 = (FStar_Syntax_Util.unmeta t2)
in ((s2), (uu____18193)))
in ((uu____18168), (uu____18184))))
in (match (uu____18147) with
| ((uu____18223, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match (scrutinee, branches); FStar_Syntax_Syntax.pos = uu____18226; FStar_Syntax_Syntax.vars = uu____18227}), (s, t)) -> begin
(

let uu____18298 = (

let uu____18300 = (is_flex scrutinee)
in (not (uu____18300)))
in (match (uu____18298) with
| true -> begin
((

let uu____18311 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____18311) with
| true -> begin
(

let uu____18316 = (FStar_Syntax_Print.term_to_string scrutinee)
in (FStar_Util.print1 "match head %s is not a flex term\n" uu____18316))
end
| uu____18319 -> begin
()
end));
FStar_Util.Inr (FStar_Pervasives_Native.None);
)
end
| uu____18324 -> begin
(match (wl1.defer_ok) with
| true -> begin
((

let uu____18335 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____18335) with
| true -> begin
(FStar_Util.print_string "Deferring ... \n")
end
| uu____18341 -> begin
()
end));
FStar_Util.Inl ("defer");
)
end
| uu____18347 -> begin
((

let uu____18350 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____18350) with
| true -> begin
(

let uu____18355 = (FStar_Syntax_Print.term_to_string scrutinee)
in (

let uu____18357 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Heuristic applicable with scrutinee %s and other side = %s\n" uu____18355 uu____18357)))
end
| uu____18360 -> begin
()
end));
(

let pat_discriminates = (fun uu___28_18382 -> (match (uu___28_18382) with
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_constant (uu____18398); FStar_Syntax_Syntax.p = uu____18399}, FStar_Pervasives_Native.None, uu____18400) -> begin
true
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (uu____18414); FStar_Syntax_Syntax.p = uu____18415}, FStar_Pervasives_Native.None, uu____18416) -> begin
true
end
| uu____18443 -> begin
false
end))
in (

let head_matching_branch = (FStar_All.pipe_right branches (FStar_Util.try_find (fun b -> (match ((pat_discriminates b)) with
| true -> begin
(

let uu____18546 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____18546) with
| (uu____18548, uu____18549, t') -> begin
(

let uu____18567 = (head_matches_delta env1 wl1 s t')
in (match (uu____18567) with
| (FullMatch, uu____18579) -> begin
true
end
| (HeadMatch (uu____18593), uu____18594) -> begin
true
end
| uu____18609 -> begin
false
end))
end))
end
| uu____18621 -> begin
false
end))))
in (match (head_matching_branch) with
| FStar_Pervasives_Native.None -> begin
((

let uu____18646 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____18646) with
| true -> begin
(FStar_Util.print_string "No head_matching branch\n")
end
| uu____18652 -> begin
()
end));
(

let try_branches = (

let uu____18657 = (FStar_Util.prefix_until (fun b -> (not ((pat_discriminates b)))) branches)
in (match (uu____18657) with
| FStar_Pervasives_Native.Some (branches1, uu____18745, uu____18746) -> begin
branches1
end
| uu____18891 -> begin
branches
end))
in (

let uu____18946 = (FStar_Util.find_map try_branches (fun b -> (

let uu____18955 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____18955) with
| (p, uu____18959, uu____18960) -> begin
(try_solve_branch scrutinee p)
end))))
in (FStar_All.pipe_left (fun _18989 -> FStar_Util.Inr (_18989)) uu____18946)));
)
end
| FStar_Pervasives_Native.Some (b) -> begin
(

let uu____19019 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____19019) with
| (p, uu____19028, e) -> begin
((

let uu____19047 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____19047) with
| true -> begin
(

let uu____19052 = (FStar_Syntax_Print.pat_to_string p)
in (

let uu____19054 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print2 "Found head matching branch %s -> %s\n" uu____19052 uu____19054)))
end
| uu____19057 -> begin
()
end));
(

let uu____19059 = (try_solve_branch scrutinee p)
in (FStar_All.pipe_left (fun _19074 -> FStar_Util.Inr (_19074)) uu____19059));
)
end))
end)));
)
end)
end))
end
| ((s, t), (uu____19077, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match (scrutinee, branches); FStar_Syntax_Syntax.pos = uu____19080; FStar_Syntax_Syntax.vars = uu____19081})) -> begin
(

let uu____19150 = (

let uu____19152 = (is_flex scrutinee)
in (not (uu____19152)))
in (match (uu____19150) with
| true -> begin
((

let uu____19163 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____19163) with
| true -> begin
(

let uu____19168 = (FStar_Syntax_Print.term_to_string scrutinee)
in (FStar_Util.print1 "match head %s is not a flex term\n" uu____19168))
end
| uu____19171 -> begin
()
end));
FStar_Util.Inr (FStar_Pervasives_Native.None);
)
end
| uu____19176 -> begin
(match (wl1.defer_ok) with
| true -> begin
((

let uu____19187 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____19187) with
| true -> begin
(FStar_Util.print_string "Deferring ... \n")
end
| uu____19193 -> begin
()
end));
FStar_Util.Inl ("defer");
)
end
| uu____19199 -> begin
((

let uu____19202 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____19202) with
| true -> begin
(

let uu____19207 = (FStar_Syntax_Print.term_to_string scrutinee)
in (

let uu____19209 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Heuristic applicable with scrutinee %s and other side = %s\n" uu____19207 uu____19209)))
end
| uu____19212 -> begin
()
end));
(

let pat_discriminates = (fun uu___28_19234 -> (match (uu___28_19234) with
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_constant (uu____19250); FStar_Syntax_Syntax.p = uu____19251}, FStar_Pervasives_Native.None, uu____19252) -> begin
true
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (uu____19266); FStar_Syntax_Syntax.p = uu____19267}, FStar_Pervasives_Native.None, uu____19268) -> begin
true
end
| uu____19295 -> begin
false
end))
in (

let head_matching_branch = (FStar_All.pipe_right branches (FStar_Util.try_find (fun b -> (match ((pat_discriminates b)) with
| true -> begin
(

let uu____19398 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____19398) with
| (uu____19400, uu____19401, t') -> begin
(

let uu____19419 = (head_matches_delta env1 wl1 s t')
in (match (uu____19419) with
| (FullMatch, uu____19431) -> begin
true
end
| (HeadMatch (uu____19445), uu____19446) -> begin
true
end
| uu____19461 -> begin
false
end))
end))
end
| uu____19473 -> begin
false
end))))
in (match (head_matching_branch) with
| FStar_Pervasives_Native.None -> begin
((

let uu____19498 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____19498) with
| true -> begin
(FStar_Util.print_string "No head_matching branch\n")
end
| uu____19504 -> begin
()
end));
(

let try_branches = (

let uu____19509 = (FStar_Util.prefix_until (fun b -> (not ((pat_discriminates b)))) branches)
in (match (uu____19509) with
| FStar_Pervasives_Native.Some (branches1, uu____19597, uu____19598) -> begin
branches1
end
| uu____19743 -> begin
branches
end))
in (

let uu____19798 = (FStar_Util.find_map try_branches (fun b -> (

let uu____19807 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____19807) with
| (p, uu____19811, uu____19812) -> begin
(try_solve_branch scrutinee p)
end))))
in (FStar_All.pipe_left (fun _19841 -> FStar_Util.Inr (_19841)) uu____19798)));
)
end
| FStar_Pervasives_Native.Some (b) -> begin
(

let uu____19871 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____19871) with
| (p, uu____19880, e) -> begin
((

let uu____19899 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____19899) with
| true -> begin
(

let uu____19904 = (FStar_Syntax_Print.pat_to_string p)
in (

let uu____19906 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print2 "Found head matching branch %s -> %s\n" uu____19904 uu____19906)))
end
| uu____19909 -> begin
()
end));
(

let uu____19911 = (try_solve_branch scrutinee p)
in (FStar_All.pipe_left (fun _19926 -> FStar_Util.Inr (_19926)) uu____19911));
)
end))
end)));
)
end)
end))
end
| uu____19927 -> begin
((

let uu____19949 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____19949) with
| true -> begin
(

let uu____19954 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____19956 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print2 "Heuristic not applicable: tag lhs=%s, rhs=%s\n" uu____19954 uu____19956)))
end
| uu____19959 -> begin
()
end));
FStar_Util.Inr (FStar_Pervasives_Native.None);
)
end));
)
end)))
in (

let rigid_rigid_delta = (fun env1 torig wl1 head1 head2 t1 t2 -> (

let orig = FStar_TypeChecker_Common.TProb (torig)
in ((

let uu____20002 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("RelDelta")))
in (match (uu____20002) with
| true -> begin
(

let uu____20007 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____20009 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____20011 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____20013 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n" uu____20007 uu____20009 uu____20011 uu____20013)))))
end
| uu____20016 -> begin
()
end));
(

let uu____20018 = (head_matches_delta env1 wl1 t1 t2)
in (match (uu____20018) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____20049), uu____20050) -> begin
(

let rec may_relate = (fun head3 -> (

let uu____20078 = (

let uu____20079 = (FStar_Syntax_Subst.compress head3)
in uu____20079.FStar_Syntax_Syntax.n)
in (match (uu____20078) with
| FStar_Syntax_Syntax.Tm_name (uu____20083) -> begin
true
end
| FStar_Syntax_Syntax.Tm_match (uu____20085) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____20110 = (FStar_TypeChecker_Env.delta_depth_of_fv env1 fv)
in (match (uu____20110) with
| FStar_Syntax_Syntax.Delta_equational_at_level (uu____20112) -> begin
true
end
| FStar_Syntax_Syntax.Delta_abstract (uu____20115) -> begin
(Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)
end
| uu____20116 -> begin
false
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____20119, uu____20120) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____20162) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____20168) -> begin
(may_relate t)
end
| uu____20173 -> begin
false
end)))
in (

let uu____20175 = (try_match_heuristic env1 orig wl1 t1 t2 o)
in (match (uu____20175) with
| FStar_Util.Inl (_defer_ok) -> begin
(

let uu____20188 = (FStar_Thunk.mkv "delaying match heuristic")
in (giveup_or_defer1 orig uu____20188))
end
| FStar_Util.Inr (FStar_Pervasives_Native.Some (wl2)) -> begin
(solve env1 wl2)
end
| FStar_Util.Inr (FStar_Pervasives_Native.None) -> begin
(

let uu____20198 = (((may_relate head1) || (may_relate head2)) && wl1.smt_ok)
in (match (uu____20198) with
| true -> begin
(

let uu____20201 = (guard_of_prob env1 wl1 problem t1 t2)
in (match (uu____20201) with
| (guard, wl2) -> begin
(

let uu____20208 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl2)
in (solve env1 uu____20208))
end))
end
| uu____20209 -> begin
(

let uu____20211 = (FStar_Thunk.mk (fun uu____20218 -> (

let uu____20219 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____20221 = (

let uu____20223 = (

let uu____20227 = (delta_depth_of_term env1 head1)
in (FStar_Util.bind_opt uu____20227 (fun x -> (

let uu____20234 = (FStar_Syntax_Print.delta_depth_to_string x)
in FStar_Pervasives_Native.Some (uu____20234)))))
in (FStar_Util.dflt "" uu____20223))
in (

let uu____20239 = (FStar_Syntax_Print.term_to_string head2)
in (

let uu____20241 = (

let uu____20243 = (

let uu____20247 = (delta_depth_of_term env1 head2)
in (FStar_Util.bind_opt uu____20247 (fun x -> (

let uu____20254 = (FStar_Syntax_Print.delta_depth_to_string x)
in FStar_Pervasives_Native.Some (uu____20254)))))
in (FStar_Util.dflt "" uu____20243))
in (FStar_Util.format4 "head mismatch (%s (%s) vs %s (%s))" uu____20219 uu____20221 uu____20239 uu____20241)))))))
in (giveup env1 uu____20211 orig))
end))
end)))
end
| (HeadMatch (true), uu____20260) when (Prims.op_disEquality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(match (wl1.smt_ok) with
| true -> begin
(

let uu____20275 = (guard_of_prob env1 wl1 problem t1 t2)
in (match (uu____20275) with
| (guard, wl2) -> begin
(

let uu____20282 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl2)
in (solve env1 uu____20282))
end))
end
| uu____20283 -> begin
(

let uu____20285 = (FStar_Thunk.mk (fun uu____20290 -> (

let uu____20291 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____20293 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "head mismatch for subtyping (%s vs %s)" uu____20291 uu____20293)))))
in (giveup env1 uu____20285 orig))
end)
end
| (uu____20296, FStar_Pervasives_Native.Some (t11, t21)) -> begin
(solve_t env1 (

let uu___2841_20310 = problem
in {FStar_TypeChecker_Common.pid = uu___2841_20310.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___2841_20310.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___2841_20310.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___2841_20310.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___2841_20310.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___2841_20310.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___2841_20310.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___2841_20310.FStar_TypeChecker_Common.rank}) wl1)
end
| (HeadMatch (need_unif), FStar_Pervasives_Native.None) -> begin
(rigid_heads_match env1 need_unif torig wl1 t1 t2)
end
| (FullMatch, FStar_Pervasives_Native.None) -> begin
(rigid_heads_match env1 false torig wl1 t1 t2)
end)
end));
)))
in (

let orig = FStar_TypeChecker_Common.TProb (problem)
in ((def_check_prob "solve_t\'.2" orig);
(

let uu____20337 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____20337) with
| true -> begin
(

let uu____20340 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____20340))
end
| uu____20341 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in ((

let uu____20346 = (

let uu____20349 = (p_scope orig)
in (FStar_List.map FStar_Pervasives_Native.fst uu____20349))
in (FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1" uu____20346 t1));
(

let uu____20368 = (

let uu____20371 = (p_scope orig)
in (FStar_List.map FStar_Pervasives_Native.fst uu____20371))
in (FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2" uu____20368 t2));
(

let uu____20390 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____20390) with
| true -> begin
(

let uu____20394 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____20396 = (

let uu____20398 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____20400 = (

let uu____20402 = (FStar_Syntax_Print.term_to_string t1)
in (Prims.op_Hat "::" uu____20402))
in (Prims.op_Hat uu____20398 uu____20400)))
in (

let uu____20405 = (

let uu____20407 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____20409 = (

let uu____20411 = (FStar_Syntax_Print.term_to_string t2)
in (Prims.op_Hat "::" uu____20411))
in (Prims.op_Hat uu____20407 uu____20409)))
in (FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n" uu____20394 uu____20396 uu____20405 (rel_to_string problem.FStar_TypeChecker_Common.relation)))))
end
| uu____20415 -> begin
()
end));
(

let r = (FStar_TypeChecker_Env.get_range env)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_delayed (uu____20418), uu____20419) -> begin
(failwith "Impossible: terms were not compressed")
end
| (uu____20443, FStar_Syntax_Syntax.Tm_delayed (uu____20444)) -> begin
(failwith "Impossible: terms were not compressed")
end
| (FStar_Syntax_Syntax.Tm_ascribed (uu____20468), uu____20469) -> begin
(

let uu____20496 = (

let uu___2872_20497 = problem
in (

let uu____20498 = (FStar_Syntax_Util.unascribe t1)
in {FStar_TypeChecker_Common.pid = uu___2872_20497.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____20498; FStar_TypeChecker_Common.relation = uu___2872_20497.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___2872_20497.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___2872_20497.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___2872_20497.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___2872_20497.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___2872_20497.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___2872_20497.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___2872_20497.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____20496 wl))
end
| (FStar_Syntax_Syntax.Tm_meta (uu____20499), uu____20500) -> begin
(

let uu____20507 = (

let uu___2878_20508 = problem
in (

let uu____20509 = (FStar_Syntax_Util.unmeta t1)
in {FStar_TypeChecker_Common.pid = uu___2878_20508.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____20509; FStar_TypeChecker_Common.relation = uu___2878_20508.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___2878_20508.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___2878_20508.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___2878_20508.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___2878_20508.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___2878_20508.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___2878_20508.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___2878_20508.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____20507 wl))
end
| (uu____20510, FStar_Syntax_Syntax.Tm_ascribed (uu____20511)) -> begin
(

let uu____20538 = (

let uu___2884_20539 = problem
in (

let uu____20540 = (FStar_Syntax_Util.unascribe t2)
in {FStar_TypeChecker_Common.pid = uu___2884_20539.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___2884_20539.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___2884_20539.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____20540; FStar_TypeChecker_Common.element = uu___2884_20539.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___2884_20539.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___2884_20539.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___2884_20539.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___2884_20539.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___2884_20539.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____20538 wl))
end
| (uu____20541, FStar_Syntax_Syntax.Tm_meta (uu____20542)) -> begin
(

let uu____20549 = (

let uu___2890_20550 = problem
in (

let uu____20551 = (FStar_Syntax_Util.unmeta t2)
in {FStar_TypeChecker_Common.pid = uu___2890_20550.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___2890_20550.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___2890_20550.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____20551; FStar_TypeChecker_Common.element = uu___2890_20550.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___2890_20550.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___2890_20550.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___2890_20550.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___2890_20550.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___2890_20550.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____20549 wl))
end
| (FStar_Syntax_Syntax.Tm_quoted (t11, uu____20553), FStar_Syntax_Syntax.Tm_quoted (t21, uu____20555)) -> begin
(

let uu____20564 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____20564))
end
| (FStar_Syntax_Syntax.Tm_bvar (uu____20565), uu____20566) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (uu____20568, FStar_Syntax_Syntax.Tm_bvar (uu____20569)) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (FStar_Syntax_Syntax.Tm_type (u1), FStar_Syntax_Syntax.Tm_type (u2)) -> begin
(solve_one_universe_eq env orig u1 u2 wl)
end
| (FStar_Syntax_Syntax.Tm_arrow (bs1, c1), FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) -> begin
(

let mk_c = (fun c uu___29_20639 -> (match (uu___29_20639) with
| [] -> begin
c
end
| bs -> begin
(

let uu____20667 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____20667))
end))
in (

let uu____20678 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____20678) with
| ((bs11, c11), (bs21, c21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun wl1 scope env1 subst1 -> (

let c12 = (FStar_Syntax_Subst.subst_comp subst1 c11)
in (

let c22 = (FStar_Syntax_Subst.subst_comp subst1 c21)
in (

let rel = (

let uu____20827 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____20827) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____20830 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (mk_c_problem wl1 scope orig c12 rel c22 FStar_Pervasives_Native.None "function co-domain"))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___30_20916 -> (match (uu___30_20916) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____20958 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____20958) with
| ((bs11, tbody11), (bs21, tbody21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun wl1 scope env1 subst1 -> (

let uu____21103 = (FStar_Syntax_Subst.subst subst1 tbody11)
in (

let uu____21104 = (FStar_Syntax_Subst.subst subst1 tbody21)
in (mk_t_problem wl1 scope orig uu____21103 problem.FStar_TypeChecker_Common.relation uu____21104 FStar_Pervasives_Native.None "lambda co-domain")))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (uu____21106), uu____21107) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____21138) -> begin
true
end
| uu____21158 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____21185 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____21197 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let force_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
t
end
| uu____21216 -> begin
(

let uu____21218 = (env.FStar_TypeChecker_Env.type_of (

let uu___2992_21226 = env
in {FStar_TypeChecker_Env.solver = uu___2992_21226.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___2992_21226.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___2992_21226.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___2992_21226.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___2992_21226.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___2992_21226.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___2992_21226.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___2992_21226.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___2992_21226.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___2992_21226.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___2992_21226.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___2992_21226.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___2992_21226.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___2992_21226.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___2992_21226.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___2992_21226.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___2992_21226.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___2992_21226.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___2992_21226.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___2992_21226.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___2992_21226.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___2992_21226.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___2992_21226.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___2992_21226.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___2992_21226.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___2992_21226.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___2992_21226.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___2992_21226.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___2992_21226.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___2992_21226.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___2992_21226.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___2992_21226.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___2992_21226.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___2992_21226.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___2992_21226.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___2992_21226.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___2992_21226.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___2992_21226.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___2992_21226.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___2992_21226.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___2992_21226.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___2992_21226.FStar_TypeChecker_Env.erasable_types_tab}) t)
in (match (uu____21218) with
| (uu____21231, ty, uu____21233) -> begin
(

let ty1 = (

let rec aux = (fun ty1 -> (

let ty2 = (FStar_TypeChecker_Normalize.unfold_whnf env ty1)
in (

let uu____21242 = (

let uu____21243 = (FStar_Syntax_Subst.compress ty2)
in uu____21243.FStar_Syntax_Syntax.n)
in (match (uu____21242) with
| FStar_Syntax_Syntax.Tm_refine (uu____21246) -> begin
(

let uu____21253 = (FStar_Syntax_Util.unrefine ty2)
in (aux uu____21253))
end
| uu____21254 -> begin
ty2
end))))
in (aux ty))
in (

let r1 = (FStar_TypeChecker_Normalize.eta_expand_with_type env t ty1)
in ((

let uu____21257 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____21257) with
| true -> begin
(

let uu____21262 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____21264 = (

let uu____21266 = (FStar_TypeChecker_Normalize.unfold_whnf env ty1)
in (FStar_Syntax_Print.term_to_string uu____21266))
in (

let uu____21267 = (FStar_Syntax_Print.term_to_string r1)
in (FStar_Util.print3 "force_eta of (%s) at type (%s) = %s\n" uu____21262 uu____21264 uu____21267))))
end
| uu____21270 -> begin
()
end));
r1;
)))
end))
end))
in (

let uu____21272 = (

let uu____21289 = (maybe_eta t1)
in (

let uu____21296 = (maybe_eta t2)
in ((uu____21289), (uu____21296))))
in (match (uu____21272) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___3013_21338 = problem
in {FStar_TypeChecker_Common.pid = uu___3013_21338.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___3013_21338.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___3013_21338.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___3013_21338.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___3013_21338.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___3013_21338.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___3013_21338.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___3013_21338.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____21359 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____21359) with
| true -> begin
(

let uu____21362 = (destruct_flex_t not_abs wl)
in (match (uu____21362) with
| (flex, wl1) -> begin
(solve_t_flex_rigid_eq env orig wl1 flex t_abs)
end))
end
| uu____21369 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___3030_21379 = problem
in {FStar_TypeChecker_Common.pid = uu___3030_21379.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___3030_21379.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___3030_21379.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___3030_21379.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___3030_21379.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___3030_21379.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___3030_21379.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___3030_21379.FStar_TypeChecker_Common.rank}) wl)
end
| uu____21380 -> begin
(

let uu____21382 = (FStar_Thunk.mkv "head tag mismatch: RHS is an abstraction")
in (giveup env uu____21382 orig))
end)))
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____21405 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____21405) with
| true -> begin
(

let uu____21408 = (destruct_flex_t not_abs wl)
in (match (uu____21408) with
| (flex, wl1) -> begin
(solve_t_flex_rigid_eq env orig wl1 flex t_abs)
end))
end
| uu____21415 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___3030_21425 = problem
in {FStar_TypeChecker_Common.pid = uu___3030_21425.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___3030_21425.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___3030_21425.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___3030_21425.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___3030_21425.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___3030_21425.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___3030_21425.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___3030_21425.FStar_TypeChecker_Common.rank}) wl)
end
| uu____21426 -> begin
(

let uu____21428 = (FStar_Thunk.mkv "head tag mismatch: RHS is an abstraction")
in (giveup env uu____21428 orig))
end)))
end))
end
| uu____21431 -> begin
(failwith "Impossible: at least one side is an abstraction")
end)))))
end
| (uu____21449, FStar_Syntax_Syntax.Tm_abs (uu____21450)) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____21481) -> begin
true
end
| uu____21501 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____21528 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____21540 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let force_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
t
end
| uu____21559 -> begin
(

let uu____21561 = (env.FStar_TypeChecker_Env.type_of (

let uu___2992_21569 = env
in {FStar_TypeChecker_Env.solver = uu___2992_21569.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___2992_21569.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___2992_21569.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___2992_21569.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___2992_21569.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___2992_21569.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___2992_21569.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___2992_21569.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___2992_21569.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___2992_21569.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___2992_21569.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___2992_21569.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___2992_21569.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___2992_21569.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___2992_21569.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___2992_21569.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___2992_21569.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___2992_21569.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___2992_21569.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___2992_21569.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___2992_21569.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___2992_21569.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___2992_21569.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___2992_21569.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___2992_21569.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___2992_21569.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___2992_21569.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___2992_21569.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___2992_21569.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___2992_21569.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___2992_21569.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___2992_21569.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___2992_21569.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___2992_21569.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___2992_21569.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___2992_21569.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___2992_21569.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___2992_21569.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___2992_21569.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___2992_21569.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___2992_21569.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___2992_21569.FStar_TypeChecker_Env.erasable_types_tab}) t)
in (match (uu____21561) with
| (uu____21574, ty, uu____21576) -> begin
(

let ty1 = (

let rec aux = (fun ty1 -> (

let ty2 = (FStar_TypeChecker_Normalize.unfold_whnf env ty1)
in (

let uu____21585 = (

let uu____21586 = (FStar_Syntax_Subst.compress ty2)
in uu____21586.FStar_Syntax_Syntax.n)
in (match (uu____21585) with
| FStar_Syntax_Syntax.Tm_refine (uu____21589) -> begin
(

let uu____21596 = (FStar_Syntax_Util.unrefine ty2)
in (aux uu____21596))
end
| uu____21597 -> begin
ty2
end))))
in (aux ty))
in (

let r1 = (FStar_TypeChecker_Normalize.eta_expand_with_type env t ty1)
in ((

let uu____21600 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____21600) with
| true -> begin
(

let uu____21605 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____21607 = (

let uu____21609 = (FStar_TypeChecker_Normalize.unfold_whnf env ty1)
in (FStar_Syntax_Print.term_to_string uu____21609))
in (

let uu____21610 = (FStar_Syntax_Print.term_to_string r1)
in (FStar_Util.print3 "force_eta of (%s) at type (%s) = %s\n" uu____21605 uu____21607 uu____21610))))
end
| uu____21613 -> begin
()
end));
r1;
)))
end))
end))
in (

let uu____21615 = (

let uu____21632 = (maybe_eta t1)
in (

let uu____21639 = (maybe_eta t2)
in ((uu____21632), (uu____21639))))
in (match (uu____21615) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___3013_21681 = problem
in {FStar_TypeChecker_Common.pid = uu___3013_21681.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___3013_21681.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___3013_21681.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___3013_21681.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___3013_21681.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___3013_21681.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___3013_21681.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___3013_21681.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____21702 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____21702) with
| true -> begin
(

let uu____21705 = (destruct_flex_t not_abs wl)
in (match (uu____21705) with
| (flex, wl1) -> begin
(solve_t_flex_rigid_eq env orig wl1 flex t_abs)
end))
end
| uu____21712 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___3030_21722 = problem
in {FStar_TypeChecker_Common.pid = uu___3030_21722.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___3030_21722.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___3030_21722.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___3030_21722.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___3030_21722.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___3030_21722.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___3030_21722.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___3030_21722.FStar_TypeChecker_Common.rank}) wl)
end
| uu____21723 -> begin
(

let uu____21725 = (FStar_Thunk.mkv "head tag mismatch: RHS is an abstraction")
in (giveup env uu____21725 orig))
end)))
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____21748 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____21748) with
| true -> begin
(

let uu____21751 = (destruct_flex_t not_abs wl)
in (match (uu____21751) with
| (flex, wl1) -> begin
(solve_t_flex_rigid_eq env orig wl1 flex t_abs)
end))
end
| uu____21758 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___3030_21768 = problem
in {FStar_TypeChecker_Common.pid = uu___3030_21768.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___3030_21768.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___3030_21768.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___3030_21768.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___3030_21768.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___3030_21768.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___3030_21768.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___3030_21768.FStar_TypeChecker_Common.rank}) wl)
end
| uu____21769 -> begin
(

let uu____21771 = (FStar_Thunk.mkv "head tag mismatch: RHS is an abstraction")
in (giveup env uu____21771 orig))
end)))
end))
end
| uu____21774 -> begin
(failwith "Impossible: at least one side is an abstraction")
end)))))
end
| (FStar_Syntax_Syntax.Tm_refine (x1, phi1), FStar_Syntax_Syntax.Tm_refine (x2, phi2)) -> begin
(

let uu____21804 = (

let uu____21809 = (head_matches_delta env wl x1.FStar_Syntax_Syntax.sort x2.FStar_Syntax_Syntax.sort)
in (match (uu____21809) with
| (FullMatch, FStar_Pervasives_Native.Some (t11, t21)) -> begin
(((

let uu___3053_21837 = x1
in {FStar_Syntax_Syntax.ppname = uu___3053_21837.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___3053_21837.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t11})), ((

let uu___3055_21839 = x2
in {FStar_Syntax_Syntax.ppname = uu___3055_21839.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___3055_21839.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t21})))
end
| (HeadMatch (uu____21840), FStar_Pervasives_Native.Some (t11, t21)) -> begin
(((

let uu___3053_21855 = x1
in {FStar_Syntax_Syntax.ppname = uu___3053_21855.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___3053_21855.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t11})), ((

let uu___3055_21857 = x2
in {FStar_Syntax_Syntax.ppname = uu___3055_21857.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___3055_21857.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t21})))
end
| uu____21858 -> begin
((x1), (x2))
end))
in (match (uu____21804) with
| (x11, x21) -> begin
(

let t11 = (FStar_Syntax_Util.refine x11 phi1)
in (

let t21 = (FStar_Syntax_Util.refine x21 phi2)
in (

let uu____21877 = (as_refinement false env t11)
in (match (uu____21877) with
| (x12, phi11) -> begin
(

let uu____21885 = (as_refinement false env t21)
in (match (uu____21885) with
| (x22, phi21) -> begin
((

let uu____21894 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____21894) with
| true -> begin
((

let uu____21899 = (FStar_Syntax_Print.bv_to_string x12)
in (

let uu____21901 = (FStar_Syntax_Print.term_to_string x12.FStar_Syntax_Syntax.sort)
in (

let uu____21903 = (FStar_Syntax_Print.term_to_string phi11)
in (FStar_Util.print3 "ref1 = (%s):(%s){%s}\n" uu____21899 uu____21901 uu____21903))));
(

let uu____21906 = (FStar_Syntax_Print.bv_to_string x22)
in (

let uu____21908 = (FStar_Syntax_Print.term_to_string x22.FStar_Syntax_Syntax.sort)
in (

let uu____21910 = (FStar_Syntax_Print.term_to_string phi21)
in (FStar_Util.print3 "ref2 = (%s):(%s){%s}\n" uu____21906 uu____21908 uu____21910))));
)
end
| uu____21913 -> begin
()
end));
(

let uu____21915 = (mk_t_problem wl [] orig x12.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x22.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (match (uu____21915) with
| (base_prob, wl1) -> begin
(

let x13 = (FStar_Syntax_Syntax.freshen_bv x12)
in (

let subst1 = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x13))))::[]
in (

let phi12 = (FStar_Syntax_Subst.subst subst1 phi11)
in (

let phi22 = (FStar_Syntax_Subst.subst subst1 phi21)
in (

let env1 = (FStar_TypeChecker_Env.push_bv env x13)
in (

let mk_imp1 = (fun imp phi13 phi23 -> (

let uu____21986 = (imp phi13 phi23)
in (FStar_All.pipe_right uu____21986 (guard_on_element wl1 problem x13))))
in (

let fallback = (fun uu____21998 -> (

let impl = (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp1 FStar_Syntax_Util.mk_iff phi12 phi22)
end
| uu____22005 -> begin
(mk_imp1 FStar_Syntax_Util.mk_imp phi12 phi22)
end)
in (

let guard = (FStar_Syntax_Util.mk_conj (p_guard base_prob) impl)
in ((

let uu____22011 = (

let uu____22014 = (p_scope orig)
in (FStar_List.map FStar_Pervasives_Native.fst uu____22014))
in (FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.1" uu____22011 (p_guard base_prob)));
(

let uu____22033 = (

let uu____22036 = (p_scope orig)
in (FStar_List.map FStar_Pervasives_Native.fst uu____22036))
in (FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.2" uu____22033 impl));
(

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl1)
in (

let uu____22055 = (attempt ((base_prob)::[]) wl2)
in (solve env1 uu____22055)));
))))
in (

let has_uvars = ((

let uu____22060 = (

let uu____22062 = (FStar_Syntax_Free.uvars phi12)
in (FStar_Util.set_is_empty uu____22062))
in (not (uu____22060))) || (

let uu____22066 = (

let uu____22068 = (FStar_Syntax_Free.uvars phi22)
in (FStar_Util.set_is_empty uu____22068))
in (not (uu____22066))))
in (match (((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) || ((not (env1.FStar_TypeChecker_Env.uvar_subtyping)) && has_uvars))) with
| true -> begin
(

let uu____22072 = (

let uu____22077 = (

let uu____22086 = (FStar_Syntax_Syntax.mk_binder x13)
in (uu____22086)::[])
in (mk_t_problem wl1 uu____22077 orig phi12 FStar_TypeChecker_Common.EQ phi22 FStar_Pervasives_Native.None "refinement formula"))
in (match (uu____22072) with
| (ref_prob, wl2) -> begin
(

let uu____22108 = (solve env1 (

let uu___3097_22110 = wl2
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___3097_22110.ctr; defer_ok = false; smt_ok = uu___3097_22110.smt_ok; umax_heuristic_ok = uu___3097_22110.umax_heuristic_ok; tcenv = uu___3097_22110.tcenv; wl_implicits = uu___3097_22110.wl_implicits}))
in (match (uu____22108) with
| Failed (prob, msg) -> begin
(match ((((not (env1.FStar_TypeChecker_Env.uvar_subtyping)) && has_uvars) || (not (wl2.smt_ok)))) with
| true -> begin
(giveup env1 msg prob)
end
| uu____22122 -> begin
(fallback ())
end)
end
| Success (uu____22124) -> begin
(

let guard = (

let uu____22132 = (FStar_All.pipe_right (p_guard ref_prob) (guard_on_element wl2 problem x13))
in (FStar_Syntax_Util.mk_conj (p_guard base_prob) uu____22132))
in (

let wl3 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl2)
in (

let wl4 = (

let uu___3108_22141 = wl3
in {attempting = uu___3108_22141.attempting; wl_deferred = uu___3108_22141.wl_deferred; ctr = (wl3.ctr + (Prims.parse_int "1")); defer_ok = uu___3108_22141.defer_ok; smt_ok = uu___3108_22141.smt_ok; umax_heuristic_ok = uu___3108_22141.umax_heuristic_ok; tcenv = uu___3108_22141.tcenv; wl_implicits = uu___3108_22141.wl_implicits})
in (

let uu____22143 = (attempt ((base_prob)::[]) wl4)
in (solve env1 uu____22143)))))
end))
end))
end
| uu____22144 -> begin
(fallback ())
end)))))))))
end));
)
end))
end))))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____22146), FStar_Syntax_Syntax.Tm_uvar (uu____22147)) -> begin
(

let uu____22172 = (destruct_flex_t t1 wl)
in (match (uu____22172) with
| (f1, wl1) -> begin
(

let uu____22179 = (destruct_flex_t t2 wl1)
in (match (uu____22179) with
| (f2, wl2) -> begin
(solve_t_flex_flex env orig wl2 f1 f2)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____22186); FStar_Syntax_Syntax.pos = uu____22187; FStar_Syntax_Syntax.vars = uu____22188}, uu____22189), FStar_Syntax_Syntax.Tm_uvar (uu____22190)) -> begin
(

let uu____22239 = (destruct_flex_t t1 wl)
in (match (uu____22239) with
| (f1, wl1) -> begin
(

let uu____22246 = (destruct_flex_t t2 wl1)
in (match (uu____22246) with
| (f2, wl2) -> begin
(solve_t_flex_flex env orig wl2 f1 f2)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____22253), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____22254); FStar_Syntax_Syntax.pos = uu____22255; FStar_Syntax_Syntax.vars = uu____22256}, uu____22257)) -> begin
(

let uu____22306 = (destruct_flex_t t1 wl)
in (match (uu____22306) with
| (f1, wl1) -> begin
(

let uu____22313 = (destruct_flex_t t2 wl1)
in (match (uu____22313) with
| (f2, wl2) -> begin
(solve_t_flex_flex env orig wl2 f1 f2)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____22320); FStar_Syntax_Syntax.pos = uu____22321; FStar_Syntax_Syntax.vars = uu____22322}, uu____22323), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____22324); FStar_Syntax_Syntax.pos = uu____22325; FStar_Syntax_Syntax.vars = uu____22326}, uu____22327)) -> begin
(

let uu____22400 = (destruct_flex_t t1 wl)
in (match (uu____22400) with
| (f1, wl1) -> begin
(

let uu____22407 = (destruct_flex_t t2 wl1)
in (match (uu____22407) with
| (f2, wl2) -> begin
(solve_t_flex_flex env orig wl2 f1 f2)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____22414), uu____22415) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(

let uu____22428 = (destruct_flex_t t1 wl)
in (match (uu____22428) with
| (f1, wl1) -> begin
(solve_t_flex_rigid_eq env orig wl1 f1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____22435); FStar_Syntax_Syntax.pos = uu____22436; FStar_Syntax_Syntax.vars = uu____22437}, uu____22438), uu____22439) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(

let uu____22476 = (destruct_flex_t t1 wl)
in (match (uu____22476) with
| (f1, wl1) -> begin
(solve_t_flex_rigid_eq env orig wl1 f1 t2)
end))
end
| (uu____22483, FStar_Syntax_Syntax.Tm_uvar (uu____22484)) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (uu____22497, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____22498); FStar_Syntax_Syntax.pos = uu____22499; FStar_Syntax_Syntax.vars = uu____22500}, uu____22501)) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____22538), FStar_Syntax_Syntax.Tm_arrow (uu____22539)) -> begin
(solve_t' env (

let uu___3208_22567 = problem
in {FStar_TypeChecker_Common.pid = uu___3208_22567.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___3208_22567.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___3208_22567.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___3208_22567.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___3208_22567.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___3208_22567.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___3208_22567.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___3208_22567.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___3208_22567.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____22568); FStar_Syntax_Syntax.pos = uu____22569; FStar_Syntax_Syntax.vars = uu____22570}, uu____22571), FStar_Syntax_Syntax.Tm_arrow (uu____22572)) -> begin
(solve_t' env (

let uu___3208_22624 = problem
in {FStar_TypeChecker_Common.pid = uu___3208_22624.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___3208_22624.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___3208_22624.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___3208_22624.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___3208_22624.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___3208_22624.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___3208_22624.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___3208_22624.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___3208_22624.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____22625, FStar_Syntax_Syntax.Tm_uvar (uu____22626)) -> begin
(

let uu____22639 = (attempt ((FStar_TypeChecker_Common.TProb (problem))::[]) wl)
in (solve env uu____22639))
end
| (uu____22640, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____22641); FStar_Syntax_Syntax.pos = uu____22642; FStar_Syntax_Syntax.vars = uu____22643}, uu____22644)) -> begin
(

let uu____22681 = (attempt ((FStar_TypeChecker_Common.TProb (problem))::[]) wl)
in (solve env uu____22681))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____22682), uu____22683) -> begin
(

let uu____22696 = (attempt ((FStar_TypeChecker_Common.TProb (problem))::[]) wl)
in (solve env uu____22696))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____22697); FStar_Syntax_Syntax.pos = uu____22698; FStar_Syntax_Syntax.vars = uu____22699}, uu____22700), uu____22701) -> begin
(

let uu____22738 = (attempt ((FStar_TypeChecker_Common.TProb (problem))::[]) wl)
in (solve env uu____22738))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____22739), uu____22740) -> begin
(

let t21 = (

let uu____22748 = (base_and_refinement env t2)
in (FStar_All.pipe_left force_refinement uu____22748))
in (solve_t env (

let uu___3243_22774 = problem
in {FStar_TypeChecker_Common.pid = uu___3243_22774.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___3243_22774.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___3243_22774.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___3243_22774.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___3243_22774.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___3243_22774.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___3243_22774.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___3243_22774.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___3243_22774.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____22775, FStar_Syntax_Syntax.Tm_refine (uu____22776)) -> begin
(

let t11 = (

let uu____22784 = (base_and_refinement env t1)
in (FStar_All.pipe_left force_refinement uu____22784))
in (solve_t env (

let uu___3250_22810 = problem
in {FStar_TypeChecker_Common.pid = uu___3250_22810.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___3250_22810.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___3250_22810.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___3250_22810.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___3250_22810.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___3250_22810.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___3250_22810.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___3250_22810.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___3250_22810.FStar_TypeChecker_Common.rank}) wl))
end
| (FStar_Syntax_Syntax.Tm_match (s1, brs1), FStar_Syntax_Syntax.Tm_match (s2, brs2)) -> begin
(

let by_smt = (fun uu____22892 -> (

let uu____22893 = (guard_of_prob env wl problem t1 t2)
in (match (uu____22893) with
| (guard, wl1) -> begin
(

let uu____22900 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl1)
in (solve env uu____22900))
end)))
in (

let rec solve_branches = (fun wl1 brs11 brs21 -> (match (((brs11), (brs21))) with
| ((br1)::rs1, (br2)::rs2) -> begin
(

let uu____23119 = br1
in (match (uu____23119) with
| (p1, w1, uu____23148) -> begin
(

let uu____23165 = br2
in (match (uu____23165) with
| (p2, w2, uu____23188) -> begin
(

let uu____23193 = (

let uu____23195 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (not (uu____23195)))
in (match (uu____23193) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____23220 -> begin
(

let uu____23222 = (FStar_Syntax_Subst.open_branch' br1)
in (match (uu____23222) with
| ((p11, w11, e1), s) -> begin
(

let uu____23259 = br2
in (match (uu____23259) with
| (p21, w21, e2) -> begin
(

let w22 = (FStar_Util.map_opt w21 (FStar_Syntax_Subst.subst s))
in (

let e21 = (FStar_Syntax_Subst.subst s e2)
in (

let scope = (

let uu____23292 = (FStar_Syntax_Syntax.pat_bvs p11)
in (FStar_All.pipe_left (FStar_List.map FStar_Syntax_Syntax.mk_binder) uu____23292))
in (

let uu____23297 = (match (((w11), (w22))) with
| (FStar_Pervasives_Native.Some (uu____23328), FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (uu____23349)) -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.Some ((([]), (wl1)))
end
| (FStar_Pervasives_Native.Some (w12), FStar_Pervasives_Native.Some (w23)) -> begin
(

let uu____23408 = (mk_t_problem wl1 scope orig w12 FStar_TypeChecker_Common.EQ w23 FStar_Pervasives_Native.None "when clause")
in (match (uu____23408) with
| (p, wl2) -> begin
FStar_Pervasives_Native.Some ((((((scope), (p)))::[]), (wl2)))
end))
end)
in (FStar_Util.bind_opt uu____23297 (fun uu____23480 -> (match (uu____23480) with
| (wprobs, wl2) -> begin
(

let uu____23517 = (mk_t_problem wl2 scope orig e1 FStar_TypeChecker_Common.EQ e21 FStar_Pervasives_Native.None "branch body")
in (match (uu____23517) with
| (prob, wl3) -> begin
((

let uu____23538 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl3.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____23538) with
| true -> begin
(

let uu____23543 = (prob_to_string env prob)
in (

let uu____23545 = (FStar_Syntax_Print.binders_to_string ", " scope)
in (FStar_Util.print2 "Created problem for branches %s with scope %s\n" uu____23543 uu____23545)))
end
| uu____23549 -> begin
()
end));
(

let uu____23551 = (solve_branches wl3 rs1 rs2)
in (FStar_Util.bind_opt uu____23551 (fun uu____23587 -> (match (uu____23587) with
| (r1, wl4) -> begin
FStar_Pervasives_Native.Some ((((((scope), (prob)))::(FStar_List.append wprobs r1)), (wl4)))
end))));
)
end))
end)))))))
end))
end))
end))
end))
end))
end
| ([], []) -> begin
FStar_Pervasives_Native.Some ((([]), (wl1)))
end
| uu____23716 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____23757 = (solve_branches wl brs1 brs2)
in (match (uu____23757) with
| FStar_Pervasives_Native.None -> begin
(match (wl.smt_ok) with
| true -> begin
(by_smt ())
end
| uu____23781 -> begin
(

let uu____23783 = (FStar_Thunk.mkv "Tm_match branches don\'t match")
in (giveup env uu____23783 orig))
end)
end
| FStar_Pervasives_Native.Some (sub_probs, wl1) -> begin
(

let uu____23810 = (mk_t_problem wl1 [] orig s1 FStar_TypeChecker_Common.EQ s2 FStar_Pervasives_Native.None "match scrutinee")
in (match (uu____23810) with
| (sc_prob, wl2) -> begin
(

let sub_probs1 = ((([]), (sc_prob)))::sub_probs
in (

let formula = (

let uu____23844 = (FStar_List.map (fun uu____23856 -> (match (uu____23856) with
| (scope, p) -> begin
(FStar_TypeChecker_Env.close_forall wl2.tcenv scope (p_guard p))
end)) sub_probs1)
in (FStar_Syntax_Util.mk_conj_l uu____23844))
in (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let wl3 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) [] wl2)
in (

let uu____23865 = (

let uu____23866 = (

let uu____23867 = (FStar_List.map FStar_Pervasives_Native.snd sub_probs1)
in (attempt uu____23867 (

let uu___3349_23875 = wl3
in {attempting = uu___3349_23875.attempting; wl_deferred = uu___3349_23875.wl_deferred; ctr = uu___3349_23875.ctr; defer_ok = uu___3349_23875.defer_ok; smt_ok = false; umax_heuristic_ok = uu___3349_23875.umax_heuristic_ok; tcenv = uu___3349_23875.tcenv; wl_implicits = uu___3349_23875.wl_implicits})))
in (solve env uu____23866))
in (match (uu____23865) with
| Success (ds, imp) -> begin
((FStar_Syntax_Unionfind.commit tx);
Success (((ds), (imp)));
)
end
| Failed (uu____23880) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(by_smt ());
)
end))))))
end))
end))))
end
| (FStar_Syntax_Syntax.Tm_match (uu____23886), uu____23887) -> begin
(

let head1 = (

let uu____23911 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____23911 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____23957 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____23957 FStar_Pervasives_Native.fst))
in ((

let uu____24003 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____24003) with
| true -> begin
(

let uu____24007 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____24009 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____24011 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____24007 uu____24009 uu____24011))))
end
| uu____24014 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____24025 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____24025)) && (

let uu____24029 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____24029))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____24046 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____24046 FStar_Syntax_Util.Equal)))))
in (

let uu____24047 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____24047) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____24051 = (equal t1 t2)
in (match (uu____24051) with
| true -> begin
(

let uu____24054 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____24054))
end
| uu____24055 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____24057 -> begin
(

let uu____24059 = (

let uu____24066 = (equal t1 t2)
in (match (uu____24066) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____24077 -> begin
(

let uu____24079 = (mk_eq2 wl env orig t1 t2)
in (match (uu____24079) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____24059) with
| (guard, wl1) -> begin
(

let uu____24100 = (solve_prob orig guard [] wl1)
in (solve env uu____24100))
end))
end)
end
| uu____24101 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____24103), uu____24104) -> begin
(

let head1 = (

let uu____24112 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____24112 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____24158 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____24158 FStar_Pervasives_Native.fst))
in ((

let uu____24204 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____24204) with
| true -> begin
(

let uu____24208 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____24210 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____24212 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____24208 uu____24210 uu____24212))))
end
| uu____24215 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____24226 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____24226)) && (

let uu____24230 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____24230))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____24247 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____24247 FStar_Syntax_Util.Equal)))))
in (

let uu____24248 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____24248) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____24252 = (equal t1 t2)
in (match (uu____24252) with
| true -> begin
(

let uu____24255 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____24255))
end
| uu____24256 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____24258 -> begin
(

let uu____24260 = (

let uu____24267 = (equal t1 t2)
in (match (uu____24267) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____24278 -> begin
(

let uu____24280 = (mk_eq2 wl env orig t1 t2)
in (match (uu____24280) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____24260) with
| (guard, wl1) -> begin
(

let uu____24301 = (solve_prob orig guard [] wl1)
in (solve env uu____24301))
end))
end)
end
| uu____24302 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (FStar_Syntax_Syntax.Tm_name (uu____24304), uu____24305) -> begin
(

let head1 = (

let uu____24307 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____24307 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____24353 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____24353 FStar_Pervasives_Native.fst))
in ((

let uu____24399 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____24399) with
| true -> begin
(

let uu____24403 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____24405 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____24407 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____24403 uu____24405 uu____24407))))
end
| uu____24410 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____24421 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____24421)) && (

let uu____24425 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____24425))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____24442 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____24442 FStar_Syntax_Util.Equal)))))
in (

let uu____24443 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____24443) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____24447 = (equal t1 t2)
in (match (uu____24447) with
| true -> begin
(

let uu____24450 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____24450))
end
| uu____24451 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____24453 -> begin
(

let uu____24455 = (

let uu____24462 = (equal t1 t2)
in (match (uu____24462) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____24473 -> begin
(

let uu____24475 = (mk_eq2 wl env orig t1 t2)
in (match (uu____24475) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____24455) with
| (guard, wl1) -> begin
(

let uu____24496 = (solve_prob orig guard [] wl1)
in (solve env uu____24496))
end))
end)
end
| uu____24497 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (FStar_Syntax_Syntax.Tm_constant (uu____24499), uu____24500) -> begin
(

let head1 = (

let uu____24502 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____24502 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____24548 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____24548 FStar_Pervasives_Native.fst))
in ((

let uu____24594 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____24594) with
| true -> begin
(

let uu____24598 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____24600 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____24602 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____24598 uu____24600 uu____24602))))
end
| uu____24605 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____24616 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____24616)) && (

let uu____24620 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____24620))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____24637 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____24637 FStar_Syntax_Util.Equal)))))
in (

let uu____24638 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____24638) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____24642 = (equal t1 t2)
in (match (uu____24642) with
| true -> begin
(

let uu____24645 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____24645))
end
| uu____24646 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____24648 -> begin
(

let uu____24650 = (

let uu____24657 = (equal t1 t2)
in (match (uu____24657) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____24668 -> begin
(

let uu____24670 = (mk_eq2 wl env orig t1 t2)
in (match (uu____24670) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____24650) with
| (guard, wl1) -> begin
(

let uu____24691 = (solve_prob orig guard [] wl1)
in (solve env uu____24691))
end))
end)
end
| uu____24692 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____24694), uu____24695) -> begin
(

let head1 = (

let uu____24697 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____24697 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____24737 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____24737 FStar_Pervasives_Native.fst))
in ((

let uu____24777 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____24777) with
| true -> begin
(

let uu____24781 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____24783 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____24785 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____24781 uu____24783 uu____24785))))
end
| uu____24788 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____24799 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____24799)) && (

let uu____24803 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____24803))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____24820 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____24820 FStar_Syntax_Util.Equal)))))
in (

let uu____24821 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____24821) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____24825 = (equal t1 t2)
in (match (uu____24825) with
| true -> begin
(

let uu____24828 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____24828))
end
| uu____24829 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____24831 -> begin
(

let uu____24833 = (

let uu____24840 = (equal t1 t2)
in (match (uu____24840) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____24851 -> begin
(

let uu____24853 = (mk_eq2 wl env orig t1 t2)
in (match (uu____24853) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____24833) with
| (guard, wl1) -> begin
(

let uu____24874 = (solve_prob orig guard [] wl1)
in (solve env uu____24874))
end))
end)
end
| uu____24875 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (FStar_Syntax_Syntax.Tm_app (uu____24877), uu____24878) -> begin
(

let head1 = (

let uu____24896 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____24896 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____24936 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____24936 FStar_Pervasives_Native.fst))
in ((

let uu____24976 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____24976) with
| true -> begin
(

let uu____24980 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____24982 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____24984 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____24980 uu____24982 uu____24984))))
end
| uu____24987 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____24998 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____24998)) && (

let uu____25002 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____25002))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____25019 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____25019 FStar_Syntax_Util.Equal)))))
in (

let uu____25020 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____25020) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____25024 = (equal t1 t2)
in (match (uu____25024) with
| true -> begin
(

let uu____25027 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____25027))
end
| uu____25028 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____25030 -> begin
(

let uu____25032 = (

let uu____25039 = (equal t1 t2)
in (match (uu____25039) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____25050 -> begin
(

let uu____25052 = (mk_eq2 wl env orig t1 t2)
in (match (uu____25052) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____25032) with
| (guard, wl1) -> begin
(

let uu____25073 = (solve_prob orig guard [] wl1)
in (solve env uu____25073))
end))
end)
end
| uu____25074 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (uu____25076, FStar_Syntax_Syntax.Tm_match (uu____25077)) -> begin
(

let head1 = (

let uu____25101 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____25101 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____25141 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____25141 FStar_Pervasives_Native.fst))
in ((

let uu____25181 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____25181) with
| true -> begin
(

let uu____25185 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____25187 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____25189 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____25185 uu____25187 uu____25189))))
end
| uu____25192 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____25203 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____25203)) && (

let uu____25207 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____25207))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____25224 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____25224 FStar_Syntax_Util.Equal)))))
in (

let uu____25225 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____25225) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____25229 = (equal t1 t2)
in (match (uu____25229) with
| true -> begin
(

let uu____25232 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____25232))
end
| uu____25233 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____25235 -> begin
(

let uu____25237 = (

let uu____25244 = (equal t1 t2)
in (match (uu____25244) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____25255 -> begin
(

let uu____25257 = (mk_eq2 wl env orig t1 t2)
in (match (uu____25257) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____25237) with
| (guard, wl1) -> begin
(

let uu____25278 = (solve_prob orig guard [] wl1)
in (solve env uu____25278))
end))
end)
end
| uu____25279 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (uu____25281, FStar_Syntax_Syntax.Tm_uinst (uu____25282)) -> begin
(

let head1 = (

let uu____25290 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____25290 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____25330 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____25330 FStar_Pervasives_Native.fst))
in ((

let uu____25370 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____25370) with
| true -> begin
(

let uu____25374 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____25376 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____25378 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____25374 uu____25376 uu____25378))))
end
| uu____25381 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____25392 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____25392)) && (

let uu____25396 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____25396))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____25413 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____25413 FStar_Syntax_Util.Equal)))))
in (

let uu____25414 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____25414) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____25418 = (equal t1 t2)
in (match (uu____25418) with
| true -> begin
(

let uu____25421 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____25421))
end
| uu____25422 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____25424 -> begin
(

let uu____25426 = (

let uu____25433 = (equal t1 t2)
in (match (uu____25433) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____25444 -> begin
(

let uu____25446 = (mk_eq2 wl env orig t1 t2)
in (match (uu____25446) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____25426) with
| (guard, wl1) -> begin
(

let uu____25467 = (solve_prob orig guard [] wl1)
in (solve env uu____25467))
end))
end)
end
| uu____25468 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (uu____25470, FStar_Syntax_Syntax.Tm_name (uu____25471)) -> begin
(

let head1 = (

let uu____25473 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____25473 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____25513 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____25513 FStar_Pervasives_Native.fst))
in ((

let uu____25553 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____25553) with
| true -> begin
(

let uu____25557 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____25559 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____25561 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____25557 uu____25559 uu____25561))))
end
| uu____25564 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____25575 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____25575)) && (

let uu____25579 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____25579))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____25596 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____25596 FStar_Syntax_Util.Equal)))))
in (

let uu____25597 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____25597) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____25601 = (equal t1 t2)
in (match (uu____25601) with
| true -> begin
(

let uu____25604 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____25604))
end
| uu____25605 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____25607 -> begin
(

let uu____25609 = (

let uu____25616 = (equal t1 t2)
in (match (uu____25616) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____25627 -> begin
(

let uu____25629 = (mk_eq2 wl env orig t1 t2)
in (match (uu____25629) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____25609) with
| (guard, wl1) -> begin
(

let uu____25650 = (solve_prob orig guard [] wl1)
in (solve env uu____25650))
end))
end)
end
| uu____25651 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (uu____25653, FStar_Syntax_Syntax.Tm_constant (uu____25654)) -> begin
(

let head1 = (

let uu____25656 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____25656 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____25696 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____25696 FStar_Pervasives_Native.fst))
in ((

let uu____25736 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____25736) with
| true -> begin
(

let uu____25740 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____25742 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____25744 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____25740 uu____25742 uu____25744))))
end
| uu____25747 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____25758 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____25758)) && (

let uu____25762 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____25762))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____25779 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____25779 FStar_Syntax_Util.Equal)))))
in (

let uu____25780 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____25780) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____25784 = (equal t1 t2)
in (match (uu____25784) with
| true -> begin
(

let uu____25787 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____25787))
end
| uu____25788 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____25790 -> begin
(

let uu____25792 = (

let uu____25799 = (equal t1 t2)
in (match (uu____25799) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____25810 -> begin
(

let uu____25812 = (mk_eq2 wl env orig t1 t2)
in (match (uu____25812) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____25792) with
| (guard, wl1) -> begin
(

let uu____25833 = (solve_prob orig guard [] wl1)
in (solve env uu____25833))
end))
end)
end
| uu____25834 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (uu____25836, FStar_Syntax_Syntax.Tm_fvar (uu____25837)) -> begin
(

let head1 = (

let uu____25839 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____25839 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____25885 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____25885 FStar_Pervasives_Native.fst))
in ((

let uu____25931 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____25931) with
| true -> begin
(

let uu____25935 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____25937 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____25939 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____25935 uu____25937 uu____25939))))
end
| uu____25942 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____25953 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____25953)) && (

let uu____25957 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____25957))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____25974 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____25974 FStar_Syntax_Util.Equal)))))
in (

let uu____25975 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____25975) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____25979 = (equal t1 t2)
in (match (uu____25979) with
| true -> begin
(

let uu____25982 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____25982))
end
| uu____25983 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____25985 -> begin
(

let uu____25987 = (

let uu____25994 = (equal t1 t2)
in (match (uu____25994) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____26005 -> begin
(

let uu____26007 = (mk_eq2 wl env orig t1 t2)
in (match (uu____26007) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____25987) with
| (guard, wl1) -> begin
(

let uu____26028 = (solve_prob orig guard [] wl1)
in (solve env uu____26028))
end))
end)
end
| uu____26029 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (uu____26031, FStar_Syntax_Syntax.Tm_app (uu____26032)) -> begin
(

let head1 = (

let uu____26050 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____26050 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____26090 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____26090 FStar_Pervasives_Native.fst))
in ((

let uu____26130 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____26130) with
| true -> begin
(

let uu____26134 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____26136 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____26138 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____26134 uu____26136 uu____26138))))
end
| uu____26141 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____26152 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____26152)) && (

let uu____26156 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____26156))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____26173 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____26173 FStar_Syntax_Util.Equal)))))
in (

let uu____26174 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____26174) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____26178 = (equal t1 t2)
in (match (uu____26178) with
| true -> begin
(

let uu____26181 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____26181))
end
| uu____26182 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____26184 -> begin
(

let uu____26186 = (

let uu____26193 = (equal t1 t2)
in (match (uu____26193) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____26204 -> begin
(

let uu____26206 = (mk_eq2 wl env orig t1 t2)
in (match (uu____26206) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____26186) with
| (guard, wl1) -> begin
(

let uu____26227 = (solve_prob orig guard [] wl1)
in (solve env uu____26227))
end))
end)
end
| uu____26228 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (FStar_Syntax_Syntax.Tm_let (uu____26230), FStar_Syntax_Syntax.Tm_let (uu____26231)) -> begin
(

let uu____26258 = (FStar_Syntax_Util.term_eq t1 t2)
in (match (uu____26258) with
| true -> begin
(

let uu____26261 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____26261))
end
| uu____26262 -> begin
(

let uu____26264 = (FStar_Thunk.mkv "Tm_let mismatch")
in (giveup env uu____26264 orig))
end))
end
| (FStar_Syntax_Syntax.Tm_let (uu____26267), uu____26268) -> begin
(

let uu____26282 = (

let uu____26288 = (

let uu____26290 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____26292 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____26294 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____26296 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)" uu____26290 uu____26292 uu____26294 uu____26296)))))
in ((FStar_Errors.Fatal_UnificationNotWellFormed), (uu____26288)))
in (FStar_Errors.raise_error uu____26282 t1.FStar_Syntax_Syntax.pos))
end
| (uu____26300, FStar_Syntax_Syntax.Tm_let (uu____26301)) -> begin
(

let uu____26315 = (

let uu____26321 = (

let uu____26323 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____26325 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____26327 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____26329 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)" uu____26323 uu____26325 uu____26327 uu____26329)))))
in ((FStar_Errors.Fatal_UnificationNotWellFormed), (uu____26321)))
in (FStar_Errors.raise_error uu____26315 t1.FStar_Syntax_Syntax.pos))
end
| uu____26333 -> begin
(

let uu____26338 = (FStar_Thunk.mkv "head tag mismatch")
in (giveup env uu____26338 orig))
end));
)))
end));
))))));
))
and solve_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (

let c1 = problem.FStar_TypeChecker_Common.lhs
in (

let c2 = problem.FStar_TypeChecker_Common.rhs
in (

let orig = FStar_TypeChecker_Common.CProb (problem)
in (

let sub_prob = (fun wl1 t1 rel t2 reason -> (mk_t_problem wl1 [] orig t1 rel t2 FStar_Pervasives_Native.None reason))
in (

let solve_eq = (fun c1_comp c2_comp g_lift -> ((

let uu____26404 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____26404) with
| true -> begin
(

let uu____26409 = (

let uu____26411 = (FStar_Syntax_Syntax.mk_Comp c1_comp)
in (FStar_Syntax_Print.comp_to_string uu____26411))
in (

let uu____26412 = (

let uu____26414 = (FStar_Syntax_Syntax.mk_Comp c2_comp)
in (FStar_Syntax_Print.comp_to_string uu____26414))
in (FStar_Util.print2 "solve_c is using an equality constraint (%s vs %s)\n" uu____26409 uu____26412)))
end
| uu____26416 -> begin
()
end));
(

let uu____26418 = (

let uu____26420 = (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)
in (not (uu____26420)))
in (match (uu____26418) with
| true -> begin
(

let uu____26423 = (FStar_Thunk.mk (fun uu____26428 -> (

let uu____26429 = (FStar_Syntax_Print.lid_to_string c1_comp.FStar_Syntax_Syntax.effect_name)
in (

let uu____26431 = (FStar_Syntax_Print.lid_to_string c2_comp.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible effects: %s <> %s" uu____26429 uu____26431)))))
in (giveup env uu____26423 orig))
end
| uu____26434 -> begin
(match ((Prims.op_disEquality (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args))) with
| true -> begin
(

let uu____26453 = (FStar_Thunk.mk (fun uu____26458 -> (

let uu____26459 = (FStar_Syntax_Print.args_to_string c1_comp.FStar_Syntax_Syntax.effect_args)
in (

let uu____26461 = (FStar_Syntax_Print.args_to_string c2_comp.FStar_Syntax_Syntax.effect_args)
in (FStar_Util.format2 "incompatible effect arguments: %s <> %s" uu____26459 uu____26461)))))
in (giveup env uu____26453 orig))
end
| uu____26464 -> begin
(

let uu____26466 = (sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ FStar_TypeChecker_Common.EQ c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type")
in (match (uu____26466) with
| (ret_sub_prob, wl1) -> begin
(

let uu____26474 = (FStar_List.fold_right2 (fun uu____26511 uu____26512 uu____26513 -> (match (((uu____26511), (uu____26512), (uu____26513))) with
| ((a1, uu____26557), (a2, uu____26559), (arg_sub_probs, wl2)) -> begin
(

let uu____26592 = (sub_prob wl2 a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (match (uu____26592) with
| (p, wl3) -> begin
(((p)::arg_sub_probs), (wl3))
end))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args (([]), (wl1)))
in (match (uu____26474) with
| (arg_sub_probs, wl2) -> begin
(

let sub_probs = (

let uu____26619 = (

let uu____26622 = (FStar_All.pipe_right g_lift.FStar_TypeChecker_Common.deferred (FStar_List.map FStar_Pervasives_Native.snd))
in (FStar_List.append arg_sub_probs uu____26622))
in (ret_sub_prob)::uu____26619)
in (

let guard = (

let guard = (

let uu____26644 = (FStar_List.map p_guard sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____26644))
in (match (g_lift.FStar_TypeChecker_Common.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
guard
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(FStar_Syntax_Util.mk_conj guard f)
end))
in (

let wl3 = (

let uu___3489_26653 = wl2
in {attempting = uu___3489_26653.attempting; wl_deferred = uu___3489_26653.wl_deferred; ctr = uu___3489_26653.ctr; defer_ok = uu___3489_26653.defer_ok; smt_ok = uu___3489_26653.smt_ok; umax_heuristic_ok = uu___3489_26653.umax_heuristic_ok; tcenv = uu___3489_26653.tcenv; wl_implicits = (FStar_List.append g_lift.FStar_TypeChecker_Common.implicits wl2.wl_implicits)})
in (

let wl4 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl3)
in (

let uu____26655 = (attempt sub_probs wl4)
in (solve env uu____26655))))))
end))
end))
end)
end));
))
in (

let solve_layered_sub = (fun c11 edge c21 -> ((

let uu____26673 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____26673) with
| true -> begin
(

let uu____26678 = (

let uu____26680 = (FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp)
in (FStar_All.pipe_right uu____26680 FStar_Syntax_Print.comp_to_string))
in (

let uu____26682 = (

let uu____26684 = (FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp)
in (FStar_All.pipe_right uu____26684 FStar_Syntax_Print.comp_to_string))
in (FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n" uu____26678 uu____26682)))
end
| uu____26687 -> begin
()
end));
(

let uu____26689 = (

let uu____26694 = (

let uu____26699 = (FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp)
in (FStar_All.pipe_right uu____26699 (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp env)))
in (FStar_All.pipe_right uu____26694 (fun uu____26716 -> (match (uu____26716) with
| (c, g) -> begin
(

let uu____26727 = (FStar_Syntax_Util.comp_to_comp_typ c)
in ((uu____26727), (g)))
end))))
in (match (uu____26689) with
| (c12, g_lift) -> begin
((

let uu____26731 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____26731) with
| true -> begin
(

let uu____26736 = (

let uu____26738 = (FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp)
in (FStar_All.pipe_right uu____26738 FStar_Syntax_Print.comp_to_string))
in (

let uu____26740 = (

let uu____26742 = (FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp)
in (FStar_All.pipe_right uu____26742 FStar_Syntax_Print.comp_to_string))
in (FStar_Util.print2 "solve_layered_sub after lift c1: %s and c2: %s\n" uu____26736 uu____26740)))
end
| uu____26745 -> begin
()
end));
(match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(solve_eq c12 c21 g_lift)
end
| uu____26748 -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let wl1 = (

let uu___3509_26752 = wl
in {attempting = uu___3509_26752.attempting; wl_deferred = uu___3509_26752.wl_deferred; ctr = uu___3509_26752.ctr; defer_ok = uu___3509_26752.defer_ok; smt_ok = uu___3509_26752.smt_ok; umax_heuristic_ok = uu___3509_26752.umax_heuristic_ok; tcenv = uu___3509_26752.tcenv; wl_implicits = (FStar_List.append g_lift.FStar_TypeChecker_Common.implicits wl.wl_implicits)})
in (

let uu____26753 = (

let is_uvar1 = (fun t -> (

let uu____26767 = (

let uu____26768 = (FStar_Syntax_Subst.compress t)
in uu____26768.FStar_Syntax_Syntax.n)
in (match (uu____26767) with
| FStar_Syntax_Syntax.Tm_uvar (uu____26772) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____26786); FStar_Syntax_Syntax.pos = uu____26787; FStar_Syntax_Syntax.vars = uu____26788}, uu____26789) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____26807); FStar_Syntax_Syntax.pos = uu____26808; FStar_Syntax_Syntax.vars = uu____26809}, uu____26810) -> begin
true
end
| uu____26848 -> begin
false
end)))
in (FStar_List.fold_right2 (fun uu____26881 uu____26882 uu____26883 -> (match (((uu____26881), (uu____26882), (uu____26883))) with
| ((a1, uu____26927), (a2, uu____26929), (is_sub_probs, wl2)) -> begin
(

let uu____26962 = (is_uvar1 a1)
in (match (uu____26962) with
| true -> begin
(

let uu____26971 = (sub_prob wl2 a1 FStar_TypeChecker_Common.EQ a2 "l.h.s. effect index uvar")
in (match (uu____26971) with
| (p, wl3) -> begin
(((p)::is_sub_probs), (wl3))
end))
end
| uu____26987 -> begin
((is_sub_probs), (wl2))
end))
end)) c12.FStar_Syntax_Syntax.effect_args c21.FStar_Syntax_Syntax.effect_args (([]), (wl1))))
in (match (uu____26753) with
| (is_sub_probs, wl2) -> begin
(

let uu____26999 = (sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ "result type")
in (match (uu____26999) with
| (ret_sub_prob, wl3) -> begin
(

let uu____27007 = (

let uu____27012 = (

let uu____27013 = (FStar_All.pipe_right c21.FStar_Syntax_Syntax.effect_name (FStar_TypeChecker_Env.get_effect_decl env))
in (FStar_All.pipe_right uu____27013 FStar_Syntax_Util.get_stronger_vc_combinator))
in (FStar_All.pipe_right uu____27012 (fun ts -> (FStar_TypeChecker_Env.inst_tscheme_with ts c21.FStar_Syntax_Syntax.comp_univs))))
in (match (uu____27007) with
| (uu____27020, stronger_t) -> begin
(

let stronger_t_shape_error = (fun s -> (

let uu____27031 = (FStar_Ident.string_of_lid c21.FStar_Syntax_Syntax.effect_name)
in (

let uu____27033 = (FStar_Syntax_Print.term_to_string stronger_t)
in (FStar_Util.format3 "Unexpected shape of stronger for %s, reason: %s (t:%s)" uu____27031 s uu____27033))))
in (

let uu____27036 = (

let uu____27065 = (

let uu____27066 = (FStar_Syntax_Subst.compress stronger_t)
in uu____27066.FStar_Syntax_Syntax.n)
in (match (uu____27065) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_List.length bs) >= (Prims.parse_int "2")) -> begin
(

let uu____27126 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____27126) with
| ((a)::bs1, c3) -> begin
(

let uu____27182 = (

let uu____27201 = (FStar_All.pipe_right bs1 (FStar_List.splitAt ((FStar_List.length bs1) - (Prims.parse_int "1"))))
in (FStar_All.pipe_right uu____27201 (fun uu____27305 -> (match (uu____27305) with
| (l1, l2) -> begin
(

let uu____27378 = (FStar_List.hd l2)
in ((l1), (uu____27378)))
end))))
in (match (uu____27182) with
| (rest_bs, f_b) -> begin
((a), (rest_bs), (f_b), (c3))
end))
end))
end
| uu____27483 -> begin
(

let uu____27484 = (

let uu____27490 = (stronger_t_shape_error "not an arrow or not enough binders")
in ((FStar_Errors.Fatal_UnexpectedExpressionType), (uu____27490)))
in (FStar_Errors.raise_error uu____27484 r))
end))
in (match (uu____27036) with
| (a_b, rest_bs, f_b, stronger_c) -> begin
(

let uu____27566 = (

let uu____27573 = (

let uu____27574 = (

let uu____27575 = (

let uu____27582 = (FStar_All.pipe_right a_b FStar_Pervasives_Native.fst)
in ((uu____27582), (c21.FStar_Syntax_Syntax.result_typ)))
in FStar_Syntax_Syntax.NT (uu____27575))
in (uu____27574)::[])
in (FStar_TypeChecker_Env.uvars_for_binders env rest_bs uu____27573 (fun b -> (

let uu____27598 = (FStar_Syntax_Print.binder_to_string b)
in (

let uu____27600 = (FStar_Ident.string_of_lid c21.FStar_Syntax_Syntax.effect_name)
in (

let uu____27602 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "implicit for binder %s in stronger of %s at %s" uu____27598 uu____27600 uu____27602))))) r))
in (match (uu____27566) with
| (rest_bs_uvars, g_uvars) -> begin
(

let wl4 = (

let uu___3583_27612 = wl3
in {attempting = uu___3583_27612.attempting; wl_deferred = uu___3583_27612.wl_deferred; ctr = uu___3583_27612.ctr; defer_ok = uu___3583_27612.defer_ok; smt_ok = uu___3583_27612.smt_ok; umax_heuristic_ok = uu___3583_27612.umax_heuristic_ok; tcenv = uu___3583_27612.tcenv; wl_implicits = (FStar_List.append g_uvars.FStar_TypeChecker_Common.implicits wl3.wl_implicits)})
in (

let substs = (FStar_List.map2 (fun b t -> (

let uu____27637 = (

let uu____27644 = (FStar_All.pipe_right b FStar_Pervasives_Native.fst)
in ((uu____27644), (t)))
in FStar_Syntax_Syntax.NT (uu____27637))) ((a_b)::rest_bs) ((c21.FStar_Syntax_Syntax.result_typ)::rest_bs_uvars))
in (

let uu____27661 = (

let f_sort_is = (

let uu____27671 = (

let uu____27672 = (

let uu____27675 = (

let uu____27676 = (FStar_All.pipe_right f_b FStar_Pervasives_Native.fst)
in uu____27676.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Subst.compress uu____27675))
in uu____27672.FStar_Syntax_Syntax.n)
in (match (uu____27671) with
| FStar_Syntax_Syntax.Tm_app (uu____27687, (uu____27688)::is) -> begin
(

let uu____27730 = (FStar_All.pipe_right is (FStar_List.map FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____27730 (FStar_List.map (FStar_Syntax_Subst.subst substs))))
end
| uu____27763 -> begin
(

let uu____27764 = (

let uu____27770 = (stronger_t_shape_error "type of f is not a repr type")
in ((FStar_Errors.Fatal_UnexpectedExpressionType), (uu____27770)))
in (FStar_Errors.raise_error uu____27764 r))
end))
in (

let uu____27776 = (FStar_All.pipe_right c12.FStar_Syntax_Syntax.effect_args (FStar_List.map FStar_Pervasives_Native.fst))
in (FStar_List.fold_left2 (fun uu____27811 f_sort_i c1_i -> (match (uu____27811) with
| (ps, wl5) -> begin
(

let uu____27832 = (sub_prob wl5 f_sort_i FStar_TypeChecker_Common.EQ c1_i "indices of c1")
in (match (uu____27832) with
| (p, wl6) -> begin
(((FStar_List.append ps ((p)::[]))), (wl6))
end))
end)) (([]), (wl4)) f_sort_is uu____27776)))
in (match (uu____27661) with
| (f_sub_probs, wl5) -> begin
(

let stronger_ct = (

let uu____27857 = (FStar_All.pipe_right stronger_c (FStar_Syntax_Subst.subst_comp substs))
in (FStar_All.pipe_right uu____27857 FStar_Syntax_Util.comp_to_comp_typ))
in (

let uu____27858 = (

let g_sort_is = (

let uu____27868 = (

let uu____27869 = (FStar_Syntax_Subst.compress stronger_ct.FStar_Syntax_Syntax.result_typ)
in uu____27869.FStar_Syntax_Syntax.n)
in (match (uu____27868) with
| FStar_Syntax_Syntax.Tm_app (uu____27874, (uu____27875)::is) -> begin
(FStar_All.pipe_right is (FStar_List.map FStar_Pervasives_Native.fst))
end
| uu____27943 -> begin
(

let uu____27944 = (

let uu____27950 = (stronger_t_shape_error "return type is not a repr type")
in ((FStar_Errors.Fatal_UnexpectedExpressionType), (uu____27950)))
in (FStar_Errors.raise_error uu____27944 r))
end))
in (

let uu____27956 = (FStar_All.pipe_right c21.FStar_Syntax_Syntax.effect_args (FStar_List.map FStar_Pervasives_Native.fst))
in (FStar_List.fold_left2 (fun uu____27991 g_sort_i c2_i -> (match (uu____27991) with
| (ps, wl6) -> begin
(

let uu____28012 = (sub_prob wl6 g_sort_i FStar_TypeChecker_Common.EQ c2_i "indices of c2")
in (match (uu____28012) with
| (p, wl7) -> begin
(((FStar_List.append ps ((p)::[]))), (wl7))
end))
end)) (([]), (wl5)) g_sort_is uu____27956)))
in (match (uu____27858) with
| (g_sub_probs, wl6) -> begin
(

let fml = (

let uu____28039 = (

let uu____28044 = (FStar_List.hd stronger_ct.FStar_Syntax_Syntax.comp_univs)
in (

let uu____28045 = (

let uu____28046 = (FStar_List.hd stronger_ct.FStar_Syntax_Syntax.effect_args)
in (FStar_Pervasives_Native.fst uu____28046))
in ((uu____28044), (uu____28045))))
in (match (uu____28039) with
| (u, wp) -> begin
(

let trivial_post = (

let ts = (

let uu____28073 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.NoDelta)::[]) env FStar_Parser_Const.trivial_pure_post_lid)
in (FStar_All.pipe_right uu____28073 FStar_Util.must))
in (

let uu____28090 = (FStar_TypeChecker_Env.inst_tscheme_with ts ((u)::[]))
in (match (uu____28090) with
| (uu____28095, t) -> begin
(

let uu____28097 = (

let uu____28102 = (

let uu____28103 = (FStar_All.pipe_right stronger_ct.FStar_Syntax_Syntax.result_typ FStar_Syntax_Syntax.as_arg)
in (uu____28103)::[])
in (FStar_Syntax_Syntax.mk_Tm_app t uu____28102))
in (uu____28097 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end)))
in (

let uu____28136 = (

let uu____28141 = (

let uu____28142 = (FStar_All.pipe_right trivial_post FStar_Syntax_Syntax.as_arg)
in (uu____28142)::[])
in (FStar_Syntax_Syntax.mk_Tm_app wp uu____28141))
in (uu____28136 FStar_Pervasives_Native.None FStar_Range.dummyRange)))
end))
in (

let sub_probs = (

let uu____28178 = (

let uu____28181 = (

let uu____28184 = (

let uu____28187 = (FStar_All.pipe_right g_lift.FStar_TypeChecker_Common.deferred (FStar_List.map FStar_Pervasives_Native.snd))
in (FStar_List.append g_sub_probs uu____28187))
in (FStar_List.append f_sub_probs uu____28184))
in (FStar_List.append is_sub_probs uu____28181))
in (ret_sub_prob)::uu____28178)
in (

let guard = (

let guard = (

let uu____28211 = (FStar_List.map p_guard sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____28211))
in (match (g_lift.FStar_TypeChecker_Common.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
guard
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(FStar_Syntax_Util.mk_conj guard f)
end))
in (

let wl7 = (

let uu____28222 = (

let uu____28225 = (FStar_Syntax_Util.mk_conj guard fml)
in (FStar_All.pipe_left (fun _28228 -> FStar_Pervasives_Native.Some (_28228)) uu____28225))
in (solve_prob orig uu____28222 [] wl6))
in (

let uu____28229 = (attempt sub_probs wl7)
in (solve env uu____28229))))))
end)))
end))))
end))
end)))
end))
end))
end))))
end);
)
end));
))
in (

let solve_sub = (fun c11 edge c21 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let lift_c1 = (fun uu____28252 -> (

let univs1 = (match (c11.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
(

let uu____28254 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (uu____28254)::[])
end
| x -> begin
x
end)
in (

let c12 = (

let uu___3654_28257 = c11
in {FStar_Syntax_Syntax.comp_univs = univs1; FStar_Syntax_Syntax.effect_name = uu___3654_28257.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___3654_28257.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___3654_28257.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___3654_28257.FStar_Syntax_Syntax.flags})
in (

let uu____28258 = (

let uu____28263 = (FStar_All.pipe_right (

let uu___3657_28265 = c12
in {FStar_Syntax_Syntax.comp_univs = univs1; FStar_Syntax_Syntax.effect_name = uu___3657_28265.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___3657_28265.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___3657_28265.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___3657_28265.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
in (FStar_All.pipe_right uu____28263 (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp env)))
in (FStar_All.pipe_right uu____28258 (fun uu____28279 -> (match (uu____28279) with
| (c, g) -> begin
(

let uu____28286 = (

let uu____28288 = (FStar_TypeChecker_Env.is_trivial g)
in (not (uu____28288)))
in (match (uu____28286) with
| true -> begin
(

let uu____28291 = (

let uu____28297 = (

let uu____28299 = (FStar_Ident.string_of_lid c12.FStar_Syntax_Syntax.effect_name)
in (

let uu____28301 = (FStar_Ident.string_of_lid c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard" uu____28299 uu____28301)))
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____28297)))
in (FStar_Errors.raise_error uu____28291 r))
end
| uu____28305 -> begin
(FStar_Syntax_Util.comp_to_comp_typ c)
end))
end)))))))
in (

let uu____28307 = (FStar_TypeChecker_Env.is_layered_effect env c21.FStar_Syntax_Syntax.effect_name)
in (match (uu____28307) with
| true -> begin
(solve_layered_sub c11 edge c21)
end
| uu____28310 -> begin
(match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____28313 = (lift_c1 ())
in (solve_eq uu____28313 c21 FStar_TypeChecker_Env.trivial_guard))
end
| uu____28314 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___31_28322 -> (match (uu___31_28322) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| uu____28327 -> begin
false
end))))
in (

let uu____28329 = (match (((c11.FStar_Syntax_Syntax.effect_args), (c21.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____28359))::uu____28360, ((wp2, uu____28362))::uu____28363) -> begin
((wp1), (wp2))
end
| uu____28436 -> begin
(

let uu____28461 = (

let uu____28467 = (

let uu____28469 = (FStar_Syntax_Print.lid_to_string c11.FStar_Syntax_Syntax.effect_name)
in (

let uu____28471 = (FStar_Syntax_Print.lid_to_string c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____28469 uu____28471)))
in ((FStar_Errors.Fatal_ExpectNormalizedEffect), (uu____28467)))
in (FStar_Errors.raise_error uu____28461 env.FStar_TypeChecker_Env.range))
end)
in (match (uu____28329) with
| (wpc1, wpc2) -> begin
(

let uu____28481 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____28481) with
| true -> begin
(

let uu____28484 = (problem_using_guard orig c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ FStar_Pervasives_Native.None "result type")
in (solve_t env uu____28484 wl))
end
| uu____28486 -> begin
(

let uu____28488 = (

let uu____28495 = (FStar_TypeChecker_Env.effect_decl_opt env c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.must uu____28495))
in (match (uu____28488) with
| (c2_decl, qualifiers) -> begin
(

let uu____28516 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____28516) with
| true -> begin
(

let c1_repr = (

let uu____28523 = (

let uu____28524 = (

let uu____28525 = (lift_c1 ())
in (FStar_Syntax_Syntax.mk_Comp uu____28525))
in (

let uu____28526 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____28524 uu____28526)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::[]) env uu____28523))
in (

let c2_repr = (

let uu____28528 = (

let uu____28529 = (FStar_Syntax_Syntax.mk_Comp c21)
in (

let uu____28530 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____28529 uu____28530)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::[]) env uu____28528))
in (

let uu____28531 = (

let uu____28536 = (

let uu____28538 = (FStar_Syntax_Print.term_to_string c1_repr)
in (

let uu____28540 = (FStar_Syntax_Print.term_to_string c2_repr)
in (FStar_Util.format2 "sub effect repr: %s <: %s" uu____28538 uu____28540)))
in (sub_prob wl c1_repr problem.FStar_TypeChecker_Common.relation c2_repr uu____28536))
in (match (uu____28531) with
| (prob, wl1) -> begin
(

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some ((p_guard prob))) [] wl1)
in (

let uu____28546 = (attempt ((prob)::[]) wl2)
in (solve env uu____28546)))
end))))
end
| uu____28547 -> begin
(

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____28555 -> begin
(

let wpc1_2 = (

let uu____28566 = (lift_c1 ())
in (FStar_All.pipe_right uu____28566 (fun ct -> (FStar_List.hd ct.FStar_Syntax_Syntax.effect_args))))
in (match (is_null_wp_2) with
| true -> begin
((

let uu____28589 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____28589) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____28595 -> begin
()
end));
(

let c1_univ = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (

let trivial = (

let uu____28599 = (FStar_All.pipe_right c2_decl FStar_Syntax_Util.get_wp_trivial_combinator)
in (match (uu____28599) with
| FStar_Pervasives_Native.None -> begin
(failwith "Rel doesn\'t yet handle undefined trivial combinator in an effect")
end
| FStar_Pervasives_Native.Some (t) -> begin
t
end))
in (

let uu____28606 = (

let uu____28613 = (

let uu____28614 = (

let uu____28631 = (FStar_TypeChecker_Env.inst_effect_fun_with ((c1_univ)::[]) env c2_decl trivial)
in (

let uu____28634 = (

let uu____28645 = (FStar_Syntax_Syntax.as_arg c11.FStar_Syntax_Syntax.result_typ)
in (uu____28645)::(wpc1_2)::[])
in ((uu____28631), (uu____28634))))
in FStar_Syntax_Syntax.Tm_app (uu____28614))
in (FStar_Syntax_Syntax.mk uu____28613))
in (uu____28606 FStar_Pervasives_Native.None r))));
)
end
| uu____28690 -> begin
(

let c2_univ = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (

let stronger = (FStar_All.pipe_right c2_decl FStar_Syntax_Util.get_stronger_vc_combinator)
in (

let uu____28694 = (

let uu____28701 = (

let uu____28702 = (

let uu____28719 = (FStar_TypeChecker_Env.inst_effect_fun_with ((c2_univ)::[]) env c2_decl stronger)
in (

let uu____28722 = (

let uu____28733 = (FStar_Syntax_Syntax.as_arg c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____28742 = (

let uu____28753 = (FStar_Syntax_Syntax.as_arg wpc2)
in (uu____28753)::(wpc1_2)::[])
in (uu____28733)::uu____28742))
in ((uu____28719), (uu____28722))))
in FStar_Syntax_Syntax.Tm_app (uu____28702))
in (FStar_Syntax_Syntax.mk uu____28701))
in (uu____28694 FStar_Pervasives_Native.None r))))
end))
end)
in ((

let uu____28807 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____28807) with
| true -> begin
(

let uu____28812 = (

let uu____28814 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Simplify)::[]) env g)
in (FStar_Syntax_Print.term_to_string uu____28814))
in (FStar_Util.print1 "WP guard (simplifed) is (%s)\n" uu____28812))
end
| uu____28816 -> begin
()
end));
(

let uu____28818 = (sub_prob wl c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ "result type")
in (match (uu____28818) with
| (base_prob, wl1) -> begin
(

let wl2 = (

let uu____28827 = (

let uu____28830 = (FStar_Syntax_Util.mk_conj (p_guard base_prob) g)
in (FStar_All.pipe_left (fun _28833 -> FStar_Pervasives_Native.Some (_28833)) uu____28830))
in (solve_prob orig uu____28827 [] wl1))
in (

let uu____28834 = (attempt ((base_prob)::[]) wl2)
in (solve env uu____28834)))
end));
))
end))
end))
end))
end)))
end)
end)))))
in (

let uu____28835 = (FStar_Util.physical_equality c1 c2)
in (match (uu____28835) with
| true -> begin
(

let uu____28838 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____28838))
end
| uu____28839 -> begin
((

let uu____28842 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____28842) with
| true -> begin
(

let uu____28847 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____28849 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____28847 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____28849)))
end
| uu____28852 -> begin
()
end));
(

let uu____28854 = (

let uu____28863 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____28866 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____28863), (uu____28866))))
in (match (uu____28854) with
| (c11, c21) -> begin
(match (((c11.FStar_Syntax_Syntax.n), (c21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____28884), FStar_Syntax_Syntax.Total (t2, uu____28886)) when (FStar_TypeChecker_Env.non_informative env t2) -> begin
(

let uu____28903 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____28903 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____28905), FStar_Syntax_Syntax.Total (uu____28906)) -> begin
(

let uu____28923 = (FStar_Thunk.mkv "incompatible monad ordering: GTot </: Tot")
in (giveup env uu____28923 orig))
end
| (FStar_Syntax_Syntax.Total (t1, uu____28927), FStar_Syntax_Syntax.Total (t2, uu____28929)) -> begin
(

let uu____28946 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____28946 wl))
end
| (FStar_Syntax_Syntax.GTotal (t1, uu____28949), FStar_Syntax_Syntax.GTotal (t2, uu____28951)) -> begin
(

let uu____28968 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____28968 wl))
end
| (FStar_Syntax_Syntax.Total (t1, uu____28971), FStar_Syntax_Syntax.GTotal (t2, uu____28973)) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB) -> begin
(

let uu____28990 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____28990 wl))
end
| (FStar_Syntax_Syntax.Total (t1, uu____28993), FStar_Syntax_Syntax.GTotal (t2, uu____28995)) -> begin
(

let uu____29012 = (FStar_Thunk.mkv "GTot =/= Tot")
in (giveup env uu____29012 orig))
end
| (FStar_Syntax_Syntax.GTotal (uu____29015), FStar_Syntax_Syntax.Comp (uu____29016)) -> begin
(

let uu____29025 = (

let uu___3781_29028 = problem
in (

let uu____29031 = (

let uu____29032 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____29032))
in {FStar_TypeChecker_Common.pid = uu___3781_29028.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____29031; FStar_TypeChecker_Common.relation = uu___3781_29028.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___3781_29028.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___3781_29028.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___3781_29028.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___3781_29028.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___3781_29028.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___3781_29028.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___3781_29028.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____29025 wl))
end
| (FStar_Syntax_Syntax.Total (uu____29033), FStar_Syntax_Syntax.Comp (uu____29034)) -> begin
(

let uu____29043 = (

let uu___3781_29046 = problem
in (

let uu____29049 = (

let uu____29050 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____29050))
in {FStar_TypeChecker_Common.pid = uu___3781_29046.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____29049; FStar_TypeChecker_Common.relation = uu___3781_29046.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___3781_29046.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___3781_29046.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___3781_29046.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___3781_29046.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___3781_29046.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___3781_29046.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___3781_29046.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____29043 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____29051), FStar_Syntax_Syntax.GTotal (uu____29052)) -> begin
(

let uu____29061 = (

let uu___3793_29064 = problem
in (

let uu____29067 = (

let uu____29068 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____29068))
in {FStar_TypeChecker_Common.pid = uu___3793_29064.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___3793_29064.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___3793_29064.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____29067; FStar_TypeChecker_Common.element = uu___3793_29064.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___3793_29064.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___3793_29064.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___3793_29064.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___3793_29064.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___3793_29064.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____29061 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____29069), FStar_Syntax_Syntax.Total (uu____29070)) -> begin
(

let uu____29079 = (

let uu___3793_29082 = problem
in (

let uu____29085 = (

let uu____29086 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____29086))
in {FStar_TypeChecker_Common.pid = uu___3793_29082.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___3793_29082.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___3793_29082.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____29085; FStar_TypeChecker_Common.element = uu___3793_29082.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___3793_29082.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___3793_29082.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___3793_29082.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___3793_29082.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___3793_29082.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____29079 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____29087), FStar_Syntax_Syntax.Comp (uu____29088)) -> begin
(

let uu____29089 = ((((FStar_Syntax_Util.is_ml_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) || ((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_total_comp c21))) || (((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB)))
in (match (uu____29089) with
| true -> begin
(

let uu____29092 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c11) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c21) FStar_Pervasives_Native.None "result type")
in (solve_t env uu____29092 wl))
end
| uu____29094 -> begin
(

let c1_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (

let c2_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____29099 = (

let uu____29104 = (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)
in (match (uu____29104) with
| true -> begin
((c1_comp), (c2_comp))
end
| uu____29111 -> begin
(

let uu____29113 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let uu____29114 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((uu____29113), (uu____29114))))
end))
in (match (uu____29099) with
| (c1_comp1, c2_comp1) -> begin
(solve_eq c1_comp1 c2_comp1 FStar_TypeChecker_Env.trivial_guard)
end))
end
| uu____29117 -> begin
(

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((

let uu____29122 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____29122) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c12.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c22.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____29128 -> begin
()
end));
(

let uu____29130 = (FStar_TypeChecker_Env.monad_leq env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____29130) with
| FStar_Pervasives_Native.None -> begin
(

let uu____29133 = (FStar_Thunk.mk (fun uu____29138 -> (

let uu____29139 = (FStar_Syntax_Print.lid_to_string c12.FStar_Syntax_Syntax.effect_name)
in (

let uu____29141 = (FStar_Syntax_Print.lid_to_string c22.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____29139 uu____29141)))))
in (giveup env uu____29133 orig))
end
| FStar_Pervasives_Native.Some (edge) -> begin
(solve_sub c12 edge c22)
end));
)))
end)))
end))
end)
end));
)
end))))))))))


let print_pending_implicits : FStar_TypeChecker_Common.guard_t  ->  Prims.string = (fun g -> (

let uu____29152 = (FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits (FStar_List.map (fun i -> (FStar_Syntax_Print.term_to_string i.FStar_TypeChecker_Common.imp_tm))))
in (FStar_All.pipe_right uu____29152 (FStar_String.concat ", "))))


let ineqs_to_string : (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.string = (fun ineqs -> (

let vars = (

let uu____29202 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs) (FStar_List.map FStar_Syntax_Print.univ_to_string))
in (FStar_All.pipe_right uu____29202 (FStar_String.concat ", ")))
in (

let ineqs1 = (

let uu____29227 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs) (FStar_List.map (fun uu____29258 -> (match (uu____29258) with
| (u1, u2) -> begin
(

let uu____29266 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____29268 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "%s < %s" uu____29266 uu____29268)))
end))))
in (FStar_All.pipe_right uu____29227 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Common.guard_f), (g.FStar_TypeChecker_Common.deferred), (g.FStar_TypeChecker_Common.univ_ineqs))) with
| (FStar_TypeChecker_Common.Trivial, [], (uu____29305, [])) when (

let uu____29332 = (FStar_Options.print_implicits ())
in (not (uu____29332))) -> begin
"{}"
end
| uu____29335 -> begin
(

let form = (match (g.FStar_TypeChecker_Common.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____29362 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)) || (FStar_Options.print_implicits ()))
in (match (uu____29362) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____29369 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____29374 = (FStar_List.map (fun uu____29387 -> (match (uu____29387) with
| (uu____29394, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Common.deferred)
in (FStar_All.pipe_right uu____29374 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (

let uu____29405 = (ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs)
in (FStar_Util.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n" form carry uu____29405 imps)))))
end))


let new_t_problem : worklist  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  (FStar_TypeChecker_Common.prob * worklist) = (fun wl env lhs rel rhs elt loc -> (

let reason = (

let uu____29462 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))))
in (match (uu____29462) with
| true -> begin
(

let uu____29470 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____29472 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29470 (rel_to_string rel) uu____29472)))
end
| uu____29475 -> begin
"TOP"
end))
in (

let uu____29478 = (new_problem wl env lhs rel rhs elt loc reason)
in (match (uu____29478) with
| (p, wl1) -> begin
((def_check_prob (Prims.op_Hat "new_t_problem." reason) (FStar_TypeChecker_Common.TProb (p)));
((FStar_TypeChecker_Common.TProb (p)), (wl1));
)
end))))


let new_t_prob : worklist  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv * worklist) = (fun wl env t1 rel t2 -> (

let x = (

let uu____29538 = (

let uu____29541 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _29544 -> FStar_Pervasives_Native.Some (_29544)) uu____29541))
in (FStar_Syntax_Syntax.new_bv uu____29538 t1))
in (

let uu____29545 = (

let uu____29550 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some (x)) uu____29550))
in (match (uu____29545) with
| (p, wl1) -> begin
((p), (x), (wl1))
end))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * lstring)  ->  (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)  ->  (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option = (fun env probs err -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in ((

let uu____29608 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelBench")))
in (match (uu____29608) with
| true -> begin
(

let uu____29613 = (FStar_Common.string_of_list (fun p -> (FStar_Util.string_of_int (p_pid p))) probs.attempting)
in (FStar_Util.print1 "solving problems %s {\n" uu____29613))
end
| uu____29618 -> begin
()
end));
(

let uu____29620 = (FStar_Util.record_time (fun uu____29627 -> (solve env probs)))
in (match (uu____29620) with
| (sol, ms) -> begin
((

let uu____29639 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelBench")))
in (match (uu____29639) with
| true -> begin
(

let uu____29644 = (FStar_Util.string_of_int ms)
in (FStar_Util.print1 "} solved in %s ms\n" uu____29644))
end
| uu____29647 -> begin
()
end));
(match (sol) with
| Success (deferred, implicits) -> begin
(

let uu____29657 = (FStar_Util.record_time (fun uu____29664 -> (FStar_Syntax_Unionfind.commit tx)))
in (match (uu____29657) with
| ((), ms1) -> begin
((

let uu____29675 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelBench")))
in (match (uu____29675) with
| true -> begin
(

let uu____29680 = (FStar_Util.string_of_int ms1)
in (FStar_Util.print1 "committed in %s ms\n" uu____29680))
end
| uu____29683 -> begin
()
end));
FStar_Pervasives_Native.Some (((deferred), (implicits)));
)
end))
end
| Failed (d, s) -> begin
((

let uu____29692 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))))
in (match (uu____29692) with
| true -> begin
(

let uu____29699 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____29699))
end
| uu____29702 -> begin
()
end));
(

let result = (err ((d), (s)))
in ((FStar_Syntax_Unionfind.rollback tx);
result;
));
)
end);
)
end));
)))


let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.guard_t  ->  FStar_TypeChecker_Common.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Common.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
((

let uu____29725 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____29725) with
| true -> begin
(

let uu____29730 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____29730))
end
| uu____29733 -> begin
()
end));
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.NoFullNorm)::[]) env f)
in ((

let uu____29737 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____29737) with
| true -> begin
(

let uu____29742 = (FStar_Syntax_Print.term_to_string f1)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____29742))
end
| uu____29745 -> begin
()
end));
(

let f2 = (

let uu____29748 = (

let uu____29749 = (FStar_Syntax_Util.unmeta f1)
in uu____29749.FStar_Syntax_Syntax.n)
in (match (uu____29748) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____29753 -> begin
FStar_TypeChecker_Common.NonTrivial (f1)
end))
in (

let uu___3910_29754 = g
in {FStar_TypeChecker_Common.guard_f = f2; FStar_TypeChecker_Common.deferred = uu___3910_29754.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = uu___3910_29754.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu___3910_29754.FStar_TypeChecker_Common.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (deferred, implicits) -> begin
(

let uu____29797 = (

let uu____29798 = (

let uu____29799 = (FStar_All.pipe_right (p_guard prob) (fun _29800 -> FStar_TypeChecker_Common.NonTrivial (_29800)))
in {FStar_TypeChecker_Common.guard_f = uu____29799; FStar_TypeChecker_Common.deferred = deferred; FStar_TypeChecker_Common.univ_ineqs = (([]), ([])); FStar_TypeChecker_Common.implicits = implicits})
in (simplify_guard env uu____29798))
in (FStar_All.pipe_left (fun _29807 -> FStar_Pervasives_Native.Some (_29807)) uu____29797))
end))


let with_guard_no_simp : 'Auu____29817 . 'Auu____29817  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____29840 = (

let uu____29841 = (FStar_All.pipe_right (p_guard prob) (fun _29842 -> FStar_TypeChecker_Common.NonTrivial (_29842)))
in {FStar_TypeChecker_Common.guard_f = uu____29841; FStar_TypeChecker_Common.deferred = d; FStar_TypeChecker_Common.univ_ineqs = (([]), ([])); FStar_TypeChecker_Common.implicits = []})
in FStar_Pervasives_Native.Some (uu____29840))
end))


let try_teq : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option = (fun smt_ok env t1 t2 -> ((

let uu____29875 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____29875) with
| true -> begin
(

let uu____29880 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____29882 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s {\n" uu____29880 uu____29882)))
end
| uu____29885 -> begin
()
end));
(

let uu____29887 = (

let uu____29892 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None uu____29892))
in (match (uu____29887) with
| (prob, wl) -> begin
(

let g = (

let uu____29900 = (solve_and_commit env (singleton wl prob smt_ok) (fun uu____29908 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob) uu____29900))
in ((

let uu____29926 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____29926) with
| true -> begin
(

let uu____29931 = (FStar_Common.string_of_option (guard_to_string env) g)
in (FStar_Util.print1 "} res = %s\n" uu____29931))
end
| uu____29934 -> begin
()
end));
g;
))
end));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.guard_t = (fun env t1 t2 -> (

let uu____29952 = (try_teq true env t1 t2)
in (match (uu____29952) with
| FStar_Pervasives_Native.None -> begin
((

let uu____29957 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____29958 = (FStar_TypeChecker_Err.basic_type_error env FStar_Pervasives_Native.None t2 t1)
in (FStar_Errors.log_issue uu____29957 uu____29958)));
FStar_TypeChecker_Common.trivial_guard;
)
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____29966 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____29966) with
| true -> begin
(

let uu____29971 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____29973 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____29975 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____29971 uu____29973 uu____29975))))
end
| uu____29978 -> begin
()
end));
g;
)
end)))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun env e t1 t2 -> (

let uu____30001 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____30002 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t2 t1)
in (FStar_Errors.log_issue uu____30001 uu____30002))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option = (fun env c1 c2 -> (

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____30028 -> begin
FStar_TypeChecker_Common.SUB
end)
in ((

let uu____30031 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____30031) with
| true -> begin
(

let uu____30036 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____30038 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n" uu____30036 uu____30038 (match ((Prims.op_Equality rel FStar_TypeChecker_Common.EQ)) with
| true -> begin
"EQ"
end
| uu____30044 -> begin
"SUB"
end))))
end
| uu____30047 -> begin
()
end));
(

let uu____30049 = (

let uu____30056 = (FStar_TypeChecker_Env.get_range env)
in (new_problem (empty_worklist env) env c1 rel c2 FStar_Pervasives_Native.None uu____30056 "sub_comp"))
in (match (uu____30049) with
| (prob, wl) -> begin
(

let prob1 = FStar_TypeChecker_Common.CProb (prob)
in ((def_check_prob "sub_comp" prob1);
(

let uu____30069 = (FStar_Util.record_time (fun uu____30081 -> (

let uu____30082 = (solve_and_commit env (singleton wl prob1 true) (fun uu____30091 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob1) uu____30082))))
in (match (uu____30069) with
| (r, ms) -> begin
((

let uu____30119 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelBench")))
in (match (uu____30119) with
| true -> begin
(

let uu____30124 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____30126 = (FStar_Syntax_Print.comp_to_string c2)
in (

let uu____30128 = (FStar_Util.string_of_int ms)
in (FStar_Util.print4 "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n" uu____30124 uu____30126 (match ((Prims.op_Equality rel FStar_TypeChecker_Common.EQ)) with
| true -> begin
"EQ"
end
| uu____30134 -> begin
"SUB"
end) uu____30128))))
end
| uu____30137 -> begin
()
end));
r;
)
end));
))
end));
)))


let solve_universe_inequalities' : FStar_Syntax_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  unit = (fun tx env uu____30166 -> (match (uu____30166) with
| (variables, ineqs) -> begin
(

let fail1 = (fun u1 u2 -> ((FStar_Syntax_Unionfind.rollback tx);
(

let uu____30209 = (

let uu____30215 = (

let uu____30217 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____30219 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Universe %s and %s are incompatible" uu____30217 uu____30219)))
in ((FStar_Errors.Fatal_IncompatibleUniverse), (uu____30215)))
in (

let uu____30223 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____30209 uu____30223)));
))
in (

let equiv1 = (fun v1 v' -> (

let uu____30236 = (

let uu____30241 = (FStar_Syntax_Subst.compress_univ v1)
in (

let uu____30242 = (FStar_Syntax_Subst.compress_univ v')
in ((uu____30241), (uu____30242))))
in (match (uu____30236) with
| (FStar_Syntax_Syntax.U_unif (v0), FStar_Syntax_Syntax.U_unif (v0')) -> begin
(FStar_Syntax_Unionfind.univ_equiv v0 v0')
end
| uu____30262 -> begin
false
end)))
in (

let sols = (FStar_All.pipe_right variables (FStar_List.collect (fun v1 -> (

let uu____30293 = (FStar_Syntax_Subst.compress_univ v1)
in (match (uu____30293) with
| FStar_Syntax_Syntax.U_unif (uu____30300) -> begin
(

let lower_bounds_of_v = (FStar_All.pipe_right ineqs (FStar_List.collect (fun uu____30329 -> (match (uu____30329) with
| (u, v') -> begin
(

let uu____30338 = (equiv1 v1 v')
in (match (uu____30338) with
| true -> begin
(

let uu____30343 = (FStar_All.pipe_right variables (FStar_Util.for_some (equiv1 u)))
in (match (uu____30343) with
| true -> begin
[]
end
| uu____30351 -> begin
(u)::[]
end))
end
| uu____30353 -> begin
[]
end))
end))))
in (

let lb = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max (lower_bounds_of_v)))
in (((lb), (v1)))::[]))
end
| uu____30364 -> begin
[]
end)))))
in (

let uu____30369 = (

let wl = (

let uu___4003_30373 = (empty_worklist env)
in {attempting = uu___4003_30373.attempting; wl_deferred = uu___4003_30373.wl_deferred; ctr = uu___4003_30373.ctr; defer_ok = false; smt_ok = uu___4003_30373.smt_ok; umax_heuristic_ok = uu___4003_30373.umax_heuristic_ok; tcenv = uu___4003_30373.tcenv; wl_implicits = uu___4003_30373.wl_implicits})
in (FStar_All.pipe_right sols (FStar_List.map (fun uu____30392 -> (match (uu____30392) with
| (lb, v1) -> begin
(

let uu____30399 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl lb v1)
in (match (uu____30399) with
| USolved (wl1) -> begin
()
end
| uu____30402 -> begin
(fail1 lb v1)
end))
end)))))
in (

let rec check_ineq = (fun uu____30413 -> (match (uu____30413) with
| (u, v1) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u)
in (

let v2 = (FStar_TypeChecker_Normalize.normalize_universe env v1)
in (match (((u1), (v2))) with
| (FStar_Syntax_Syntax.U_zero, uu____30425) -> begin
true
end
| (FStar_Syntax_Syntax.U_succ (u0), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u0), (v0)))
end
| (FStar_Syntax_Syntax.U_name (u0), FStar_Syntax_Syntax.U_name (v0)) -> begin
(FStar_Ident.ident_equals u0 v0)
end
| (FStar_Syntax_Syntax.U_unif (u0), FStar_Syntax_Syntax.U_unif (v0)) -> begin
(FStar_Syntax_Unionfind.univ_equiv u0 v0)
end
| (FStar_Syntax_Syntax.U_name (uu____30449), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_unif (uu____30451), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_max (us), uu____30462) -> begin
(FStar_All.pipe_right us (FStar_Util.for_all (fun u2 -> (check_ineq ((u2), (v2))))))
end
| (uu____30470, FStar_Syntax_Syntax.U_max (vs)) -> begin
(FStar_All.pipe_right vs (FStar_Util.for_some (fun v3 -> (check_ineq ((u1), (v3))))))
end
| uu____30479 -> begin
false
end)))
end))
in (

let uu____30485 = (FStar_All.pipe_right ineqs (FStar_Util.for_all (fun uu____30502 -> (match (uu____30502) with
| (u, v1) -> begin
(

let uu____30510 = (check_ineq ((u), (v1)))
in (match (uu____30510) with
| true -> begin
true
end
| uu____30515 -> begin
((

let uu____30518 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____30518) with
| true -> begin
(

let uu____30523 = (FStar_Syntax_Print.univ_to_string u)
in (

let uu____30525 = (FStar_Syntax_Print.univ_to_string v1)
in (FStar_Util.print2 "%s </= %s" uu____30523 uu____30525)))
end
| uu____30528 -> begin
()
end));
false;
)
end))
end))))
in (match (uu____30485) with
| true -> begin
()
end
| uu____30532 -> begin
((

let uu____30535 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____30535) with
| true -> begin
((

let uu____30541 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Partially solved inequality constraints are: %s\n" uu____30541));
(FStar_Syntax_Unionfind.rollback tx);
(

let uu____30553 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Original solved inequality constraints are: %s\n" uu____30553));
)
end
| uu____30564 -> begin
()
end));
(

let uu____30566 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_FailToSolveUniverseInEquality), ("Failed to solve universe inequalities for inductives")) uu____30566));
)
end)))))))
end))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  unit = (fun env ineqs -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Syntax_Unionfind.commit tx);
)))


let try_solve_deferred_constraints : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.guard_t  ->  FStar_TypeChecker_Common.guard_t = (fun defer_ok env g -> (

let fail1 = (fun uu____30639 -> (match (uu____30639) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ErrorInSolveDeferredConstraints), (msg)) (p_loc d)))
end))
in (

let wl = (

let uu___4080_30662 = (wl_of_guard env g.FStar_TypeChecker_Common.deferred)
in {attempting = uu___4080_30662.attempting; wl_deferred = uu___4080_30662.wl_deferred; ctr = uu___4080_30662.ctr; defer_ok = defer_ok; smt_ok = uu___4080_30662.smt_ok; umax_heuristic_ok = uu___4080_30662.umax_heuristic_ok; tcenv = uu___4080_30662.tcenv; wl_implicits = uu___4080_30662.wl_implicits})
in ((

let uu____30665 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____30665) with
| true -> begin
(

let uu____30670 = (FStar_Util.string_of_bool defer_ok)
in (

let uu____30672 = (wl_to_string wl)
in (

let uu____30674 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Common.implicits))
in (FStar_Util.print3 "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n" uu____30670 uu____30672 uu____30674))))
end
| uu____30677 -> begin
()
end));
(

let g1 = (

let uu____30680 = (solve_and_commit env wl fail1)
in (match (uu____30680) with
| FStar_Pervasives_Native.Some ((uu____30687)::uu____30688, uu____30689) when (not (defer_ok)) -> begin
(failwith "Impossible: Unexpected deferred constraints remain")
end
| FStar_Pervasives_Native.Some (deferred, imps) -> begin
(

let uu___4095_30718 = g
in {FStar_TypeChecker_Common.guard_f = uu___4095_30718.FStar_TypeChecker_Common.guard_f; FStar_TypeChecker_Common.deferred = deferred; FStar_TypeChecker_Common.univ_ineqs = uu___4095_30718.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = (FStar_List.append g.FStar_TypeChecker_Common.implicits imps)})
end
| uu____30719 -> begin
(failwith "Impossible: should have raised a failure already")
end))
in ((solve_universe_inequalities env g1.FStar_TypeChecker_Common.univ_ineqs);
(

let uu___4100_30728 = g1
in {FStar_TypeChecker_Common.guard_f = uu___4100_30728.FStar_TypeChecker_Common.guard_f; FStar_TypeChecker_Common.deferred = uu___4100_30728.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = (([]), ([])); FStar_TypeChecker_Common.implicits = uu___4100_30728.FStar_TypeChecker_Common.implicits});
));
))))


let solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.guard_t  ->  FStar_TypeChecker_Common.guard_t = (fun env g -> (try_solve_deferred_constraints false env g))


let solve_some_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.guard_t  ->  FStar_TypeChecker_Common.guard_t = (fun env g -> (try_solve_deferred_constraints true env g))


let discharge_guard' : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.guard_t  ->  Prims.bool  ->  FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option = (fun use_env_range_msg env g use_smt -> (

let debug1 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTQuery")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Tac"))))
in (

let g1 = (solve_deferred_constraints env g)
in (

let ret_g = (

let uu___4112_30805 = g1
in {FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Common.deferred = uu___4112_30805.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = uu___4112_30805.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu___4112_30805.FStar_TypeChecker_Common.implicits})
in (

let uu____30806 = (

let uu____30808 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____30808)))
in (match (uu____30806) with
| true -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| uu____30813 -> begin
(match (g1.FStar_TypeChecker_Common.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((match (debug1) with
| true -> begin
(

let uu____30820 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____30821 = (

let uu____30823 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____30823))
in (FStar_Errors.diag uu____30820 uu____30821)))
end
| uu____30826 -> begin
()
end);
(

let vc1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.Primops)::[]) env vc)
in ((match (debug1) with
| true -> begin
(

let uu____30831 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____30832 = (

let uu____30834 = (FStar_Syntax_Print.term_to_string vc1)
in (FStar_Util.format1 "After normalization VC=\n%s\n" uu____30834))
in (FStar_Errors.diag uu____30831 uu____30832)))
end
| uu____30837 -> begin
()
end);
(

let uu____30840 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Env.def_check_closed_in_env uu____30840 "discharge_guard\'" env vc1));
(

let uu____30842 = (FStar_TypeChecker_Common.check_trivial vc1)
in (match (uu____30842) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc2) -> begin
(match ((not (use_smt))) with
| true -> begin
((match (debug1) with
| true -> begin
(

let uu____30851 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____30852 = (

let uu____30854 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Cannot solve without SMT : %s\n" uu____30854))
in (FStar_Errors.diag uu____30851 uu____30852)))
end
| uu____30857 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end
| uu____30859 -> begin
((match (debug1) with
| true -> begin
(

let uu____30864 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____30865 = (

let uu____30867 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____30867))
in (FStar_Errors.diag uu____30864 uu____30865)))
end
| uu____30870 -> begin
()
end);
(

let vcs = (

let uu____30881 = (FStar_Options.use_tactics ())
in (match (uu____30881) with
| true -> begin
(FStar_Options.with_saved_options (fun uu____30903 -> ((

let uu____30905 = (FStar_Options.set_options "--no_tactics")
in (FStar_All.pipe_left (fun a1 -> ()) uu____30905));
(

let vcs = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.preprocess env vc2)
in (FStar_All.pipe_right vcs (FStar_List.map (fun uu____30949 -> (match (uu____30949) with
| (env1, goal, opts) -> begin
(

let uu____30965 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.Primops)::[]) env1 goal)
in ((env1), (uu____30965), (opts)))
end)))));
)))
end
| uu____30966 -> begin
(

let uu____30968 = (

let uu____30975 = (FStar_Options.peek ())
in ((env), (vc2), (uu____30975)))
in (uu____30968)::[])
end))
in (FStar_All.pipe_right vcs (FStar_List.iter (fun uu____31008 -> (match (uu____31008) with
| (env1, goal, opts) -> begin
(

let uu____31018 = (FStar_TypeChecker_Common.check_trivial goal)
in (match (uu____31018) with
| FStar_TypeChecker_Common.Trivial -> begin
(match (debug1) with
| true -> begin
(FStar_Util.print_string "Goal completely solved by tactic\n")
end
| uu____31022 -> begin
()
end)
end
| FStar_TypeChecker_Common.NonTrivial (goal1) -> begin
((FStar_Options.push ());
(FStar_Options.set opts);
(match (debug1) with
| true -> begin
(

let uu____31029 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____31030 = (

let uu____31032 = (FStar_Syntax_Print.term_to_string goal1)
in (

let uu____31034 = (FStar_TypeChecker_Env.string_of_proof_ns env1)
in (FStar_Util.format2 "Trying to solve:\n> %s\nWith proof_ns:\n %s\n" uu____31032 uu____31034)))
in (FStar_Errors.diag uu____31029 uu____31030)))
end
| uu____31037 -> begin
()
end);
(match (debug1) with
| true -> begin
(

let uu____31041 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____31042 = (

let uu____31044 = (FStar_Syntax_Print.term_to_string goal1)
in (FStar_Util.format1 "Before calling solver VC=\n%s\n" uu____31044))
in (FStar_Errors.diag uu____31041 uu____31042)))
end
| uu____31047 -> begin
()
end);
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env1 goal1);
(FStar_Options.pop ());
)
end))
end)))));
FStar_Pervasives_Native.Some (ret_g);
)
end)
end));
));
)
end)
end))))))


let discharge_guard_no_smt : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.guard_t  ->  FStar_TypeChecker_Common.guard_t = (fun env g -> (

let uu____31062 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____31062) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____31071 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ExpectTrivialPreCondition), ("Expected a trivial pre-condition")) uu____31071))
end)))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.guard_t  ->  FStar_TypeChecker_Common.guard_t = (fun env g -> (

let uu____31085 = (discharge_guard' FStar_Pervasives_Native.None env g true)
in (match (uu____31085) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end)))


let teq_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> (

let uu____31115 = (try_teq false env t1 t2)
in (match (uu____31115) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (g) -> begin
(discharge_guard' FStar_Pervasives_Native.None env g false)
end)))


let resolve_implicits' : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  Prims.bool  ->  FStar_TypeChecker_Common.guard_t  ->  FStar_TypeChecker_Common.guard_t = (fun env must_total forcelax g -> (

let rec unresolved = (fun ctx_u -> (

let uu____31159 = (FStar_Syntax_Unionfind.find ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____31159) with
| FStar_Pervasives_Native.Some (r) -> begin
(match (ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____31172) -> begin
(

let uu____31185 = (

let uu____31186 = (FStar_Syntax_Subst.compress r)
in uu____31186.FStar_Syntax_Syntax.n)
in (match (uu____31185) with
| FStar_Syntax_Syntax.Tm_uvar (ctx_u', uu____31191) -> begin
(unresolved ctx_u')
end
| uu____31208 -> begin
false
end))
end)
end
| FStar_Pervasives_Native.None -> begin
true
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____31232 = acc
in (match (uu____31232) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____31243 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd1)::tl1 -> begin
(

let uu____31251 = hd1
in (match (uu____31251) with
| {FStar_TypeChecker_Common.imp_reason = reason; FStar_TypeChecker_Common.imp_uvar = ctx_u; FStar_TypeChecker_Common.imp_tm = tm; FStar_TypeChecker_Common.imp_range = r} -> begin
(match ((Prims.op_Equality ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check FStar_Syntax_Syntax.Allow_unresolved)) with
| true -> begin
(until_fixpoint ((out), (true)) tl1)
end
| uu____31260 -> begin
(

let uu____31262 = (unresolved ctx_u)
in (match (uu____31262) with
| true -> begin
(match (ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta) with
| FStar_Pervasives_Native.None -> begin
(until_fixpoint (((hd1)::out), (changed)) tl1)
end
| FStar_Pervasives_Native.Some (env_dyn, tau) -> begin
(

let env1 = (FStar_Dyn.undyn env_dyn)
in ((

let uu____31286 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("Tac")))
in (match (uu____31286) with
| true -> begin
(

let uu____31290 = (FStar_Syntax_Print.ctx_uvar_to_string ctx_u)
in (FStar_Util.print1 "Running tactic for meta-arg %s\n" uu____31290))
end
| uu____31293 -> begin
()
end));
(

let t = (env1.FStar_TypeChecker_Env.synth_hook env1 hd1.FStar_TypeChecker_Common.imp_uvar.FStar_Syntax_Syntax.ctx_uvar_typ tau)
in (

let extra = (

let uu____31299 = (teq_nosmt env1 t tm)
in (match (uu____31299) with
| FStar_Pervasives_Native.None -> begin
(failwith "resolve_implicits: unifying with an unresolved uvar failed?")
end
| FStar_Pervasives_Native.Some (g1) -> begin
g1.FStar_TypeChecker_Common.implicits
end))
in (

let ctx_u1 = (

let uu___4224_31309 = ctx_u
in {FStar_Syntax_Syntax.ctx_uvar_head = uu___4224_31309.FStar_Syntax_Syntax.ctx_uvar_head; FStar_Syntax_Syntax.ctx_uvar_gamma = uu___4224_31309.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_Syntax_Syntax.ctx_uvar_binders = uu___4224_31309.FStar_Syntax_Syntax.ctx_uvar_binders; FStar_Syntax_Syntax.ctx_uvar_typ = uu___4224_31309.FStar_Syntax_Syntax.ctx_uvar_typ; FStar_Syntax_Syntax.ctx_uvar_reason = uu___4224_31309.FStar_Syntax_Syntax.ctx_uvar_reason; FStar_Syntax_Syntax.ctx_uvar_should_check = uu___4224_31309.FStar_Syntax_Syntax.ctx_uvar_should_check; FStar_Syntax_Syntax.ctx_uvar_range = uu___4224_31309.FStar_Syntax_Syntax.ctx_uvar_range; FStar_Syntax_Syntax.ctx_uvar_meta = FStar_Pervasives_Native.None})
in (

let hd2 = (

let uu___4227_31317 = hd1
in {FStar_TypeChecker_Common.imp_reason = uu___4227_31317.FStar_TypeChecker_Common.imp_reason; FStar_TypeChecker_Common.imp_uvar = ctx_u1; FStar_TypeChecker_Common.imp_tm = uu___4227_31317.FStar_TypeChecker_Common.imp_tm; FStar_TypeChecker_Common.imp_range = uu___4227_31317.FStar_TypeChecker_Common.imp_range})
in (until_fixpoint ((out), (true)) ((hd2)::(FStar_List.append extra tl1)))))));
))
end)
end
| uu____31320 -> begin
(match ((Prims.op_Equality ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check FStar_Syntax_Syntax.Allow_untyped)) with
| true -> begin
(until_fixpoint ((out), (true)) tl1)
end
| uu____31325 -> begin
(

let env1 = (

let uu___4231_31328 = env
in {FStar_TypeChecker_Env.solver = uu___4231_31328.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___4231_31328.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___4231_31328.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_TypeChecker_Env.gamma_sig = uu___4231_31328.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___4231_31328.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___4231_31328.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___4231_31328.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___4231_31328.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___4231_31328.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___4231_31328.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___4231_31328.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___4231_31328.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___4231_31328.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___4231_31328.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___4231_31328.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___4231_31328.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___4231_31328.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___4231_31328.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___4231_31328.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___4231_31328.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___4231_31328.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___4231_31328.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___4231_31328.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___4231_31328.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___4231_31328.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___4231_31328.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___4231_31328.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___4231_31328.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___4231_31328.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___4231_31328.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___4231_31328.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___4231_31328.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___4231_31328.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___4231_31328.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___4231_31328.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___4231_31328.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___4231_31328.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___4231_31328.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___4231_31328.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___4231_31328.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___4231_31328.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___4231_31328.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___4231_31328.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___4231_31328.FStar_TypeChecker_Env.erasable_types_tab})
in (

let tm1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env1 tm)
in (

let env2 = (match (forcelax) with
| true -> begin
(

let uu___4236_31332 = env1
in {FStar_TypeChecker_Env.solver = uu___4236_31332.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___4236_31332.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___4236_31332.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___4236_31332.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___4236_31332.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___4236_31332.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___4236_31332.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___4236_31332.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___4236_31332.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___4236_31332.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___4236_31332.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___4236_31332.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___4236_31332.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___4236_31332.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___4236_31332.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___4236_31332.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___4236_31332.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___4236_31332.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___4236_31332.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___4236_31332.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___4236_31332.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___4236_31332.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___4236_31332.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___4236_31332.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___4236_31332.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___4236_31332.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___4236_31332.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___4236_31332.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___4236_31332.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___4236_31332.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___4236_31332.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___4236_31332.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___4236_31332.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___4236_31332.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___4236_31332.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___4236_31332.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___4236_31332.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___4236_31332.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___4236_31332.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___4236_31332.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___4236_31332.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___4236_31332.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___4236_31332.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___4236_31332.FStar_TypeChecker_Env.erasable_types_tab})
end
| uu____31334 -> begin
env1
end)
in ((

let uu____31337 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____31337) with
| true -> begin
(

let uu____31342 = (FStar_Syntax_Print.uvar_to_string ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____31344 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____31346 = (FStar_Syntax_Print.term_to_string ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (

let uu____31348 = (FStar_Range.string_of_range r)
in (FStar_Util.print5 "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n" uu____31342 uu____31344 uu____31346 reason uu____31348)))))
end
| uu____31351 -> begin
()
end));
(

let g1 = (FStar_All.try_with (fun uu___4242_31355 -> (match (()) with
| () -> begin
(env2.FStar_TypeChecker_Env.check_type_of must_total env2 tm1 ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
end)) (fun uu___4241_31359 -> (match (uu___4241_31359) with
| e when (FStar_Errors.handleable e) -> begin
((

let uu____31362 = (

let uu____31372 = (

let uu____31380 = (

let uu____31382 = (FStar_Syntax_Print.uvar_to_string ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____31384 = (FStar_TypeChecker_Normalize.term_to_string env2 tm1)
in (

let uu____31386 = (FStar_TypeChecker_Normalize.term_to_string env2 ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format3 "Failed while checking implicit %s set to %s of expected type %s" uu____31382 uu____31384 uu____31386))))
in ((FStar_Errors.Error_BadImplicit), (uu____31380), (r)))
in (uu____31372)::[])
in (FStar_Errors.add_errors uu____31362));
(FStar_Exn.raise e);
)
end)))
in (

let g' = (

let uu____31405 = (discharge_guard' (FStar_Pervasives_Native.Some ((fun uu____31416 -> (

let uu____31417 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____31419 = (FStar_Range.string_of_range r)
in (

let uu____31421 = (FStar_Range.string_of_range tm1.FStar_Syntax_Syntax.pos)
in (FStar_Util.format4 "%s (Introduced at %s for %s resolved at %s)" uu____31417 uu____31419 reason uu____31421))))))) env2 g1 true)
in (match (uu____31405) with
| FStar_Pervasives_Native.Some (g2) -> begin
g2
end
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end))
in (until_fixpoint (((FStar_List.append g'.FStar_TypeChecker_Common.implicits out)), (true)) tl1)));
))))
end)
end))
end)
end))
end)
end)))
in (

let uu___4254_31429 = g
in (

let uu____31430 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Common.implicits)
in {FStar_TypeChecker_Common.guard_f = uu___4254_31429.FStar_TypeChecker_Common.guard_f; FStar_TypeChecker_Common.deferred = uu___4254_31429.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = uu___4254_31429.FStar_TypeChecker_Common.univ_ineqs; FStar_TypeChecker_Common.implicits = uu____31430})))))


let resolve_implicits : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.guard_t  ->  FStar_TypeChecker_Common.guard_t = (fun env g -> (resolve_implicits' env ((not (env.FStar_TypeChecker_Env.phase1)) && (not (env.FStar_TypeChecker_Env.lax))) false g))


let resolve_implicits_tac : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.guard_t  ->  FStar_TypeChecker_Common.guard_t = (fun env g -> (resolve_implicits' env false true g))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.guard_t  ->  unit = (fun env g -> (

let g1 = (

let uu____31470 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____31470 (resolve_implicits env)))
in (match (g1.FStar_TypeChecker_Common.implicits) with
| [] -> begin
(

let uu____31471 = (discharge_guard env g1)
in (FStar_All.pipe_left (fun a2 -> ()) uu____31471))
end
| (imp)::uu____31473 -> begin
(

let uu____31476 = (

let uu____31482 = (

let uu____31484 = (FStar_Syntax_Print.uvar_to_string imp.FStar_TypeChecker_Common.imp_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____31486 = (FStar_TypeChecker_Normalize.term_to_string env imp.FStar_TypeChecker_Common.imp_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format3 "Failed to resolve implicit argument %s of type %s introduced for %s" uu____31484 uu____31486 imp.FStar_TypeChecker_Common.imp_reason)))
in ((FStar_Errors.Fatal_FailToResolveImplicitArgument), (uu____31482)))
in (FStar_Errors.raise_error uu____31476 imp.FStar_TypeChecker_Common.imp_range))
end)))


let teq_force : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun env t1 t2 -> (

let uu____31506 = (teq env t1 t2)
in (force_trivial_guard env uu____31506)))


let teq_nosmt_force : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____31525 = (teq_nosmt env t1 t2)
in (match (uu____31525) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g) -> begin
((force_trivial_guard env g);
true;
)
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Common.guard_t = (fun u1 u2 -> (

let uu___4279_31544 = FStar_TypeChecker_Common.trivial_guard
in {FStar_TypeChecker_Common.guard_f = uu___4279_31544.FStar_TypeChecker_Common.guard_f; FStar_TypeChecker_Common.deferred = uu___4279_31544.FStar_TypeChecker_Common.deferred; FStar_TypeChecker_Common.univ_ineqs = (([]), ((((u1), (u2)))::[])); FStar_TypeChecker_Common.implicits = uu___4279_31544.FStar_TypeChecker_Common.implicits}))


let check_subtyping : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Common.guard_t) FStar_Pervasives_Native.option = (fun env t1 t2 -> ((

let uu____31580 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____31580) with
| true -> begin
(

let uu____31585 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____31587 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31585 uu____31587)))
end
| uu____31590 -> begin
()
end));
(

let uu____31592 = (new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____31592) with
| (prob, x, wl) -> begin
(

let g = (

let uu____31611 = (solve_and_commit env (singleton wl prob true) (fun uu____31620 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob) uu____31611))
in ((

let uu____31638 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____31638) with
| true -> begin
(

let uu____31643 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____31645 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____31647 = (

let uu____31649 = (FStar_Util.must g)
in (guard_to_string env uu____31649))
in (FStar_Util.print3 "check_subtyping succeeded: %s <: %s\n\tguard is %s\n" uu____31643 uu____31645 uu____31647))))
end
| uu____31651 -> begin
()
end));
(match (g) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (g1) -> begin
FStar_Pervasives_Native.Some (((x), (g1)))
end);
))
end));
))


let get_subtyping_predicate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> (

let uu____31686 = (check_subtyping env t1 t2)
in (match (uu____31686) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (x, g) -> begin
(

let uu____31705 = (

let uu____31706 = (FStar_Syntax_Syntax.mk_binder x)
in (FStar_TypeChecker_Env.abstract_guard uu____31706 g))
in FStar_Pervasives_Native.Some (uu____31705))
end)))


let get_subtyping_prop : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> (

let uu____31725 = (check_subtyping env t1 t2)
in (match (uu____31725) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (x, g) -> begin
(

let uu____31744 = (

let uu____31745 = (

let uu____31746 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____31746)::[])
in (FStar_TypeChecker_Env.close_guard env uu____31745 g))
in FStar_Pervasives_Native.Some (uu____31744))
end)))


let subtype_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> ((

let uu____31784 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____31784) with
| true -> begin
(

let uu____31789 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____31791 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____31789 uu____31791)))
end
| uu____31794 -> begin
()
end));
(

let uu____31796 = (new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____31796) with
| (prob, x, wl) -> begin
(

let g = (

let uu____31811 = (solve_and_commit env (singleton wl prob false) (fun uu____31820 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob) uu____31811))
in (match (g) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (g1) -> begin
(

let g2 = (

let uu____31841 = (

let uu____31842 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____31842)::[])
in (FStar_TypeChecker_Env.close_guard env uu____31841 g1))
in (discharge_guard' FStar_Pervasives_Native.None env g2 false))
end))
end));
))


let subtype_nosmt_force : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____31883 = (subtype_nosmt env t1 t2)
in (match (uu____31883) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g) -> begin
((force_trivial_guard env g);
true;
)
end)))






open Prims
open FStar_Pervasives

let print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar  ->  Prims.string = (fun ctx_uvar -> (FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar))

type uvi =
| TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)


let uu___is_TERM : uvi  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TERM (_0) -> begin
true
end
| uu____34 -> begin
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
| uu____64 -> begin
false
end))


let __proj__UNIV__item___0 : uvi  ->  (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe) = (fun projectee -> (match (projectee) with
| UNIV (_0) -> begin
_0
end))

type worklist =
{attempting : FStar_TypeChecker_Common.probs; wl_deferred : (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list; ctr : Prims.int; defer_ok : Prims.bool; smt_ok : Prims.bool; umax_heuristic_ok : Prims.bool; tcenv : FStar_TypeChecker_Env.env; wl_implicits : FStar_TypeChecker_Env.implicits}


let __proj__Mkworklist__item__attempting : worklist  ->  FStar_TypeChecker_Common.probs = (fun projectee -> (match (projectee) with
| {attempting = attempting; wl_deferred = wl_deferred; ctr = ctr; defer_ok = defer_ok; smt_ok = smt_ok; umax_heuristic_ok = umax_heuristic_ok; tcenv = tcenv; wl_implicits = wl_implicits} -> begin
attempting
end))


let __proj__Mkworklist__item__wl_deferred : worklist  ->  (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list = (fun projectee -> (match (projectee) with
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


let __proj__Mkworklist__item__wl_implicits : worklist  ->  FStar_TypeChecker_Env.implicits = (fun projectee -> (match (projectee) with
| {attempting = attempting; wl_deferred = wl_deferred; ctr = ctr; defer_ok = defer_ok; smt_ok = smt_ok; umax_heuristic_ok = umax_heuristic_ok; tcenv = tcenv; wl_implicits = wl_implicits} -> begin
wl_implicits
end))


let new_uvar : Prims.string  ->  worklist  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.binding Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.should_check_uvar  ->  (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term * worklist) = (fun reason wl r gamma binders k should_check -> (

let ctx_uvar = (

let uu____388 = (FStar_Syntax_Unionfind.fresh ())
in {FStar_Syntax_Syntax.ctx_uvar_head = uu____388; FStar_Syntax_Syntax.ctx_uvar_gamma = gamma; FStar_Syntax_Syntax.ctx_uvar_binders = binders; FStar_Syntax_Syntax.ctx_uvar_typ = k; FStar_Syntax_Syntax.ctx_uvar_reason = reason; FStar_Syntax_Syntax.ctx_uvar_should_check = should_check; FStar_Syntax_Syntax.ctx_uvar_range = r})
in ((FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r true gamma binders);
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((ctx_uvar), ((([]), (FStar_Syntax_Syntax.NoUseRange)))))) FStar_Pervasives_Native.None r)
in (

let imp = {FStar_TypeChecker_Env.imp_reason = reason; FStar_TypeChecker_Env.imp_uvar = ctx_uvar; FStar_TypeChecker_Env.imp_tm = t; FStar_TypeChecker_Env.imp_range = r; FStar_TypeChecker_Env.imp_meta = FStar_Pervasives_Native.None}
in ((ctx_uvar), (t), ((

let uu___354_423 = wl
in {attempting = uu___354_423.attempting; wl_deferred = uu___354_423.wl_deferred; ctr = uu___354_423.ctr; defer_ok = uu___354_423.defer_ok; smt_ok = uu___354_423.smt_ok; umax_heuristic_ok = uu___354_423.umax_heuristic_ok; tcenv = uu___354_423.tcenv; wl_implicits = (imp)::wl.wl_implicits})))));
)))


let copy_uvar : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  worklist  ->  (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term * worklist) = (fun u bs t wl -> (

let env = (

let uu___355_455 = wl.tcenv
in {FStar_TypeChecker_Env.solver = uu___355_455.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___355_455.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___355_455.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = u.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_TypeChecker_Env.gamma_sig = uu___355_455.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___355_455.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___355_455.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___355_455.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___355_455.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___355_455.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___355_455.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___355_455.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___355_455.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___355_455.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___355_455.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___355_455.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___355_455.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___355_455.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___355_455.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___355_455.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___355_455.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___355_455.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___355_455.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___355_455.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___355_455.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___355_455.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___355_455.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___355_455.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___355_455.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___355_455.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___355_455.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___355_455.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___355_455.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___355_455.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___355_455.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___355_455.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___355_455.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___355_455.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___355_455.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___355_455.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___355_455.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___355_455.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___355_455.FStar_TypeChecker_Env.nbe})
in (

let env1 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____457 = (FStar_TypeChecker_Env.all_binders env1)
in (new_uvar u.FStar_Syntax_Syntax.ctx_uvar_reason wl u.FStar_Syntax_Syntax.ctx_uvar_range env1.FStar_TypeChecker_Env.gamma uu____457 t u.FStar_Syntax_Syntax.ctx_uvar_should_check)))))

type solution =
| Success of (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits)
| Failed of (FStar_TypeChecker_Common.prob * Prims.string)


let uu___is_Success : solution  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
true
end
| uu____494 -> begin
false
end))


let __proj__Success__item___0 : solution  ->  (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits) = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
_0
end))


let uu___is_Failed : solution  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Failed (_0) -> begin
true
end
| uu____524 -> begin
false
end))


let __proj__Failed__item___0 : solution  ->  (FStar_TypeChecker_Common.prob * Prims.string) = (fun projectee -> (match (projectee) with
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
| uu____549 -> begin
false
end))


let uu___is_CONTRAVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CONTRAVARIANT -> begin
true
end
| uu____555 -> begin
false
end))


let uu___is_INVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| INVARIANT -> begin
true
end
| uu____561 -> begin
false
end))


type tprob =
FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem


type cprob =
FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem


type 'a problem_t =
'a FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun uu___322_576 -> (match (uu___322_576) with
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

let uu____582 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____582) with
| (head1, args) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(

let uu____643 = (FStar_Syntax_Print.ctx_uvar_to_string u)
in (

let uu____644 = (match ((FStar_Pervasives_Native.fst s)) with
| [] -> begin
""
end
| s1 -> begin
(

let uu____656 = (

let uu____657 = (FStar_List.hd s1)
in (FStar_Syntax_Print.subst_to_string uu____657))
in (FStar_Util.format1 "@<%s>" uu____656))
end)
in (

let uu____660 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "%s%s %s" uu____643 uu____644 uu____660))))
end
| uu____661 -> begin
(FStar_Syntax_Print.term_to_string t)
end)
end)))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env uu___323_671 -> (match (uu___323_671) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____675 = (

let uu____678 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____679 = (

let uu____682 = (term_to_string p.FStar_TypeChecker_Common.lhs)
in (

let uu____683 = (

let uu____686 = (

let uu____689 = (term_to_string p.FStar_TypeChecker_Common.rhs)
in (uu____689)::[])
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::uu____686)
in (uu____682)::uu____683))
in (uu____678)::uu____679))
in (FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____675))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____693 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____694 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____695 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____693 uu____694 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____695))))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env uu___324_705 -> (match (uu___324_705) with
| UNIV (u, t) -> begin
(

let x = (

let uu____709 = (FStar_Options.hide_uvar_nums ())
in (match (uu____709) with
| true -> begin
"?"
end
| uu____710 -> begin
(

let uu____711 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____711 FStar_Util.string_of_int))
end))
in (

let uu____712 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x uu____712)))
end
| TERM (u, t) -> begin
(

let x = (

let uu____716 = (FStar_Options.hide_uvar_nums ())
in (match (uu____716) with
| true -> begin
"?"
end
| uu____717 -> begin
(

let uu____718 = (FStar_Syntax_Unionfind.uvar_id u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_right uu____718 FStar_Util.string_of_int))
end))
in (

let uu____719 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x uu____719)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (

let uu____734 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right uu____734 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (

let uu____748 = (

let uu____751 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right uu____751 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right uu____748 (FStar_String.concat ", "))))


let args_to_string : 'Auu____764 . (FStar_Syntax_Syntax.term * 'Auu____764) Prims.list  ->  Prims.string = (fun args -> (

let uu____782 = (FStar_All.pipe_right args (FStar_List.map (fun uu____800 -> (match (uu____800) with
| (x, uu____806) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____782 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = true; smt_ok = true; umax_heuristic_ok = true; tcenv = env; wl_implicits = []})


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> ((

let uu____836 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____836) with
| true -> begin
(

let uu____837 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason uu____837))
end
| uu____838 -> begin
()
end));
Failed (((prob), (reason)));
))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun uu___325_843 -> (match (uu___325_843) with
| FStar_TypeChecker_Common.EQ -> begin
FStar_TypeChecker_Common.EQ
end
| FStar_TypeChecker_Common.SUB -> begin
FStar_TypeChecker_Common.SUBINV
end
| FStar_TypeChecker_Common.SUBINV -> begin
FStar_TypeChecker_Common.SUB
end))


let invert : 'Auu____848 . 'Auu____848 FStar_TypeChecker_Common.problem  ->  'Auu____848 FStar_TypeChecker_Common.problem = (fun p -> (

let uu___356_860 = p
in {FStar_TypeChecker_Common.pid = uu___356_860.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = uu___356_860.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___356_860.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___356_860.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___356_860.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___356_860.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___356_860.FStar_TypeChecker_Common.rank}))


let maybe_invert : 'Auu____867 . 'Auu____867 FStar_TypeChecker_Common.problem  ->  'Auu____867 FStar_TypeChecker_Common.problem = (fun p -> (match ((Prims.op_Equality p.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUBINV)) with
| true -> begin
(invert p)
end
| uu____879 -> begin
p
end))


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___326_884 -> (match (uu___326_884) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_1 -> FStar_TypeChecker_Common.TProb (_0_1)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_2 -> FStar_TypeChecker_Common.CProb (_0_2)))
end))


let make_prob_eq : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___327_899 -> (match (uu___327_899) with
| FStar_TypeChecker_Common.TProb (p) -> begin
FStar_TypeChecker_Common.TProb ((

let uu___357_905 = p
in {FStar_TypeChecker_Common.pid = uu___357_905.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___357_905.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___357_905.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___357_905.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___357_905.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___357_905.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___357_905.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___357_905.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___357_905.FStar_TypeChecker_Common.rank}))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
FStar_TypeChecker_Common.CProb ((

let uu___358_913 = p
in {FStar_TypeChecker_Common.pid = uu___358_913.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___358_913.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___358_913.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___358_913.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___358_913.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___358_913.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___358_913.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___358_913.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___358_913.FStar_TypeChecker_Common.rank}))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel uu___328_925 -> (match (uu___328_925) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun uu___329_930 -> (match (uu___329_930) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun uu___330_941 -> (match (uu___330_941) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun uu___331_954 -> (match (uu___331_954) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun uu___332_967 -> (match (uu___332_967) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_element : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option = (fun uu___333_980 -> (match (uu___333_980) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.element
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.element
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term = (fun uu___334_993 -> (match (uu___334_993) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_guard_uvar : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.ctx_uvar = (fun uu___335_1004 -> (match (uu___335_1004) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard_uvar
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard_uvar
end))


let def_scope_wf : 'Auu____1019 . Prims.string  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.bv * 'Auu____1019) Prims.list  ->  unit = (fun msg rng r -> (

let uu____1047 = (

let uu____1048 = (FStar_Options.defensive ())
in (not (uu____1048)))
in (match (uu____1047) with
| true -> begin
()
end
| uu____1049 -> begin
(

let rec aux = (fun prev next -> (match (next) with
| [] -> begin
()
end
| ((bv, uu____1082))::bs -> begin
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

let uu____1128 = (match ((p_element prob)) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____1152 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1152)::[])
end)
in (FStar_List.append p.FStar_TypeChecker_Common.logical_guard_uvar.FStar_Syntax_Syntax.ctx_uvar_binders uu____1128))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____1180 = (match ((p_element prob)) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____1204 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1204)::[])
end)
in (FStar_List.append p.FStar_TypeChecker_Common.logical_guard_uvar.FStar_Syntax_Syntax.ctx_uvar_binders uu____1180))
end)
in ((def_scope_wf "p_scope" (p_loc prob) r);
r;
)))


let def_check_scoped : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  unit = (fun msg prob phi -> (

let uu____1247 = (

let uu____1248 = (FStar_Options.defensive ())
in (not (uu____1248)))
in (match (uu____1247) with
| true -> begin
()
end
| uu____1249 -> begin
(

let uu____1250 = (

let uu____1253 = (p_scope prob)
in (FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst) uu____1253))
in (FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg uu____1250 phi))
end)))


let def_check_scoped_comp : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  unit = (fun msg prob comp -> (

let uu____1299 = (

let uu____1300 = (FStar_Options.defensive ())
in (not (uu____1300)))
in (match (uu____1299) with
| true -> begin
()
end
| uu____1301 -> begin
(

let uu____1302 = (FStar_Syntax_Util.arrow [] comp)
in (def_check_scoped msg prob uu____1302))
end)))


let def_check_prob : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  unit = (fun msg prob -> (

let uu____1319 = (

let uu____1320 = (FStar_Options.defensive ())
in (not (uu____1320)))
in (match (uu____1319) with
| true -> begin
()
end
| uu____1321 -> begin
(

let msgf = (fun m -> (

let uu____1328 = (

let uu____1329 = (

let uu____1330 = (FStar_Util.string_of_int (p_pid prob))
in (Prims.strcat uu____1330 (Prims.strcat "." m)))
in (Prims.strcat "." uu____1329))
in (Prims.strcat msg uu____1328)))
in ((

let uu____1332 = (msgf "scope")
in (

let uu____1333 = (p_scope prob)
in (def_scope_wf uu____1332 (p_loc prob) uu____1333)));
(

let uu____1345 = (msgf "guard")
in (def_check_scoped uu____1345 prob (p_guard prob)));
(match (prob) with
| FStar_TypeChecker_Common.TProb (p) -> begin
((

let uu____1350 = (msgf "lhs")
in (def_check_scoped uu____1350 prob p.FStar_TypeChecker_Common.lhs));
(

let uu____1351 = (msgf "rhs")
in (def_check_scoped uu____1351 prob p.FStar_TypeChecker_Common.rhs));
)
end
| FStar_TypeChecker_Common.CProb (p) -> begin
((

let uu____1356 = (msgf "lhs")
in (def_check_scoped_comp uu____1356 prob p.FStar_TypeChecker_Common.lhs));
(

let uu____1357 = (msgf "rhs")
in (def_check_scoped_comp uu____1357 prob p.FStar_TypeChecker_Common.rhs));
)
end);
))
end)))


let singleton : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun wl prob smt_ok -> (

let uu___359_1373 = wl
in {attempting = (prob)::[]; wl_deferred = uu___359_1373.wl_deferred; ctr = uu___359_1373.ctr; defer_ok = uu___359_1373.defer_ok; smt_ok = smt_ok; umax_heuristic_ok = uu___359_1373.umax_heuristic_ok; tcenv = uu___359_1373.tcenv; wl_implicits = uu___359_1373.wl_implicits}))


let wl_of_guard : 'Auu____1380 . FStar_TypeChecker_Env.env  ->  ('Auu____1380 * FStar_TypeChecker_Common.prob) Prims.list  ->  worklist = (fun env g -> (

let uu___360_1403 = (empty_worklist env)
in (

let uu____1404 = (FStar_List.map FStar_Pervasives_Native.snd g)
in {attempting = uu____1404; wl_deferred = uu___360_1403.wl_deferred; ctr = uu___360_1403.ctr; defer_ok = uu___360_1403.defer_ok; smt_ok = uu___360_1403.smt_ok; umax_heuristic_ok = uu___360_1403.umax_heuristic_ok; tcenv = uu___360_1403.tcenv; wl_implicits = uu___360_1403.wl_implicits})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu___361_1424 = wl
in {attempting = uu___361_1424.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = uu___361_1424.ctr; defer_ok = uu___361_1424.defer_ok; smt_ok = uu___361_1424.smt_ok; umax_heuristic_ok = uu___361_1424.umax_heuristic_ok; tcenv = uu___361_1424.tcenv; wl_implicits = uu___361_1424.wl_implicits}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> ((FStar_List.iter (def_check_prob "attempt") probs);
(

let uu___362_1446 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = uu___362_1446.wl_deferred; ctr = uu___362_1446.ctr; defer_ok = uu___362_1446.defer_ok; smt_ok = uu___362_1446.smt_ok; umax_heuristic_ok = uu___362_1446.umax_heuristic_ok; tcenv = uu___362_1446.tcenv; wl_implicits = uu___362_1446.wl_implicits});
))


let mk_eq2 : 'Auu____1459 . worklist  ->  FStar_TypeChecker_Env.env  ->  'Auu____1459  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * worklist) = (fun wl env prob t1 t2 -> (

let uu____1493 = (FStar_Syntax_Util.type_u ())
in (match (uu____1493) with
| (t_type, u) -> begin
(

let binders = (FStar_TypeChecker_Env.all_binders env)
in (

let uu____1505 = (new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos env.FStar_TypeChecker_Env.gamma binders t_type FStar_Syntax_Syntax.Allow_unresolved)
in (match (uu____1505) with
| (uu____1516, tt, wl1) -> begin
(

let uu____1519 = (FStar_Syntax_Util.mk_eq2 u tt t1 t2)
in ((uu____1519), (wl1)))
end)))
end)))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___336_1524 -> (match (uu___336_1524) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _0_3 -> FStar_TypeChecker_Common.TProb (_0_3)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _0_4 -> FStar_TypeChecker_Common.CProb (_0_4)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> (

let uu____1540 = (FStar_All.pipe_right (p_reason p) FStar_List.length)
in (Prims.op_Equality uu____1540 (Prims.parse_int "1"))))


let next_pid : unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____1550 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
)))


let mk_problem : 'Auu____1644 . worklist  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_TypeChecker_Common.prob  ->  'Auu____1644  ->  FStar_TypeChecker_Common.rel  ->  'Auu____1644  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  Prims.string  ->  ('Auu____1644 FStar_TypeChecker_Common.problem * worklist) = (fun wl scope orig lhs rel rhs elt reason -> (

let scope1 = (match (elt) with
| FStar_Pervasives_Native.None -> begin
scope
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____1729 = (

let uu____1738 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1738)::[])
in (FStar_List.append scope uu____1729))
end)
in (

let bs = (FStar_List.append (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders scope1)
in (

let gamma = (

let uu____1781 = (

let uu____1784 = (FStar_List.map (fun b -> FStar_Syntax_Syntax.Binding_var ((FStar_Pervasives_Native.fst b))) scope1)
in (FStar_List.rev uu____1784))
in (FStar_List.append uu____1781 (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma))
in (

let uu____1803 = (new_uvar (Prims.strcat "mk_problem: logical guard for " reason) wl FStar_Range.dummyRange gamma bs FStar_Syntax_Util.ktype0 FStar_Syntax_Syntax.Allow_untyped)
in (match (uu____1803) with
| (ctx_uvar, lg, wl1) -> begin
(

let prob = (

let uu____1822 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____1822; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = lg; FStar_TypeChecker_Common.logical_guard_uvar = ctx_uvar; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})
in ((prob), (wl1)))
end))))))


let mk_t_problem : worklist  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_TypeChecker_Common.prob * worklist) = (fun wl scope orig lhs rel rhs elt reason -> ((def_check_prob (Prims.strcat reason ".mk_t.arg") orig);
(

let uu____1890 = (mk_problem wl scope orig lhs rel rhs elt reason)
in (match (uu____1890) with
| (p, wl1) -> begin
((def_check_prob (Prims.strcat reason ".mk_t") (FStar_TypeChecker_Common.TProb (p)));
((FStar_TypeChecker_Common.TProb (p)), (wl1));
)
end));
))


let mk_c_problem : worklist  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_TypeChecker_Common.prob * worklist) = (fun wl scope orig lhs rel rhs elt reason -> ((def_check_prob (Prims.strcat reason ".mk_c.arg") orig);
(

let uu____1973 = (mk_problem wl scope orig lhs rel rhs elt reason)
in (match (uu____1973) with
| (p, wl1) -> begin
((def_check_prob (Prims.strcat reason ".mk_c") (FStar_TypeChecker_Common.CProb (p)));
((FStar_TypeChecker_Common.CProb (p)), (wl1));
)
end));
))


let new_problem : 'Auu____2009 . worklist  ->  FStar_TypeChecker_Env.env  ->  'Auu____2009  ->  FStar_TypeChecker_Common.rel  ->  'Auu____2009  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  Prims.string  ->  ('Auu____2009 FStar_TypeChecker_Common.problem * worklist) = (fun wl env lhs rel rhs subject loc reason -> (

let lg_ty = (match (subject) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let bs = (

let uu____2075 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2075)::[])
in (

let uu____2094 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow bs uu____2094)))
end)
in (

let uu____2097 = (

let uu____2104 = (FStar_TypeChecker_Env.all_binders env)
in (new_uvar (Prims.strcat "new_problem: logical guard for " reason) (

let uu___363_2114 = wl
in {attempting = uu___363_2114.attempting; wl_deferred = uu___363_2114.wl_deferred; ctr = uu___363_2114.ctr; defer_ok = uu___363_2114.defer_ok; smt_ok = uu___363_2114.smt_ok; umax_heuristic_ok = uu___363_2114.umax_heuristic_ok; tcenv = env; wl_implicits = uu___363_2114.wl_implicits}) loc env.FStar_TypeChecker_Env.gamma uu____2104 lg_ty FStar_Syntax_Syntax.Allow_untyped))
in (match (uu____2097) with
| (ctx_uvar, lg, wl1) -> begin
(

let lg1 = (match (subject) with
| FStar_Pervasives_Native.None -> begin
lg
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____2126 = (

let uu____2131 = (

let uu____2132 = (

let uu____2141 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____2141))
in (uu____2132)::[])
in (FStar_Syntax_Syntax.mk_Tm_app lg uu____2131))
in (uu____2126 FStar_Pervasives_Native.None loc))
end)
in (

let prob = (

let uu____2171 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____2171; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = subject; FStar_TypeChecker_Common.logical_guard = lg1; FStar_TypeChecker_Common.logical_guard_uvar = ctx_uvar; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})
in ((prob), (wl1))))
end))))


let problem_using_guard : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  Prims.string  ->  FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem = (fun orig lhs rel rhs elt reason -> (

let p = (

let uu____2213 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____2213; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.logical_guard_uvar = (p_guard_uvar orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})
in ((def_check_prob reason (FStar_TypeChecker_Common.TProb (p)));
p;
)))


let guard_on_element : 'Auu____2225 . worklist  ->  'Auu____2225 FStar_TypeChecker_Common.problem  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun wl problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| FStar_Pervasives_Native.None -> begin
(

let u = (wl.tcenv.FStar_TypeChecker_Env.universe_of wl.tcenv x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Util.mk_forall u x phi))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____2258 = (

let uu____2261 = (

let uu____2262 = (

let uu____2269 = (FStar_Syntax_Syntax.bv_to_name e)
in ((x), (uu____2269)))
in FStar_Syntax_Syntax.NT (uu____2262))
in (uu____2261)::[])
in (FStar_Syntax_Subst.subst uu____2258 phi))
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (

let uu____2289 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))))
in (match (uu____2289) with
| true -> begin
(

let uu____2290 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (

let uu____2291 = (prob_to_string env d)
in (

let uu____2292 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" uu____2290 uu____2291 uu____2292 s))))
end
| uu____2295 -> begin
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
| uu____2298 -> begin
(failwith "impossible")
end)
in (

let uu____2299 = (match (d1) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____2311 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (

let uu____2312 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((uu____2311), (uu____2312))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____2316 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (

let uu____2317 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((uu____2316), (uu____2317))))
end)
in (match (uu____2299) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___337_2335 -> (match (uu___337_2335) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Syntax_Unionfind.univ_union u u')
end
| uu____2347 -> begin
(FStar_Syntax_Unionfind.univ_change u t)
end)
end
| TERM (u, t) -> begin
((

let uu____2351 = (FStar_List.map FStar_Pervasives_Native.fst u.FStar_Syntax_Syntax.ctx_uvar_binders)
in (FStar_TypeChecker_Env.def_check_closed_in t.FStar_Syntax_Syntax.pos "commit" uu____2351 t));
(FStar_Syntax_Util.set_uvar u.FStar_Syntax_Syntax.ctx_uvar_head t);
)
end)))))


let find_term_uvar : FStar_Syntax_Syntax.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun uv s -> (FStar_Util.find_map s (fun uu___338_2380 -> (match (uu___338_2380) with
| UNIV (uu____2383) -> begin
FStar_Pervasives_Native.None
end
| TERM (u, t) -> begin
(

let uu____2390 = (FStar_Syntax_Unionfind.equiv uv u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____2390) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____2393 -> begin
FStar_Pervasives_Native.None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe_uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun u s -> (FStar_Util.find_map s (fun uu___339_2414 -> (match (uu___339_2414) with
| UNIV (u', t) -> begin
(

let uu____2419 = (FStar_Syntax_Unionfind.univ_equiv u u')
in (match (uu____2419) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____2422 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____2423 -> begin
FStar_Pervasives_Native.None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____2434 = (

let uu____2435 = (

let uu____2436 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::[]) env uu____2436))
in (FStar_Syntax_Subst.compress uu____2435))
in (FStar_All.pipe_right uu____2434 FStar_Syntax_Util.unlazy_emb)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____2447 = (

let uu____2448 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress uu____2448))
in (FStar_All.pipe_right uu____2447 FStar_Syntax_Util.unlazy_emb)))


let norm_arg : 'Auu____2455 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * 'Auu____2455)  ->  (FStar_Syntax_Syntax.term * 'Auu____2455) = (fun env t -> (

let uu____2478 = (sn env (FStar_Pervasives_Native.fst t))
in ((uu____2478), ((FStar_Pervasives_Native.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____2529 -> (match (uu____2529) with
| (x, imp) -> begin
(

let uu____2548 = (

let uu___364_2549 = x
in (

let uu____2550 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___364_2549.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___364_2549.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2550}))
in ((uu____2548), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____2573 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____2573))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____2577 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____2577))
end
| uu____2580 -> begin
u2
end)))
in (

let uu____2581 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2581))))


let base_and_refinement_maybe_delta : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option) = (fun should_delta env t1 -> (

let norm_refinement = (fun env1 t -> (

let steps = (match (should_delta) with
| true -> begin
(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]
end
| uu____2619 -> begin
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
| uu____2692 -> begin
(

let uu____2693 = (norm_refinement env t12)
in (match (uu____2693) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x1, phi1); FStar_Syntax_Syntax.pos = uu____2708; FStar_Syntax_Syntax.vars = uu____2709} -> begin
((x1.FStar_Syntax_Syntax.sort), (FStar_Pervasives_Native.Some (((x1), (phi1)))))
end
| tt -> begin
(

let uu____2733 = (

let uu____2734 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____2735 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" uu____2734 uu____2735)))
in (failwith uu____2733))
end))
end)
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____2749 = (FStar_Syntax_Util.unfold_lazy i)
in (aux norm1 uu____2749))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____2750) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____2783 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____2785 = (

let uu____2786 = (FStar_Syntax_Subst.compress t1')
in uu____2786.FStar_Syntax_Syntax.n)
in (match (uu____2785) with
| FStar_Syntax_Syntax.Tm_refine (uu____2801) -> begin
(aux true t1')
end
| uu____2808 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2823) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____2850 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____2852 = (

let uu____2853 = (FStar_Syntax_Subst.compress t1')
in uu____2853.FStar_Syntax_Syntax.n)
in (match (uu____2852) with
| FStar_Syntax_Syntax.Tm_refine (uu____2868) -> begin
(aux true t1')
end
| uu____2875 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_app (uu____2890) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____2933 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____2935 = (

let uu____2936 = (FStar_Syntax_Subst.compress t1')
in uu____2936.FStar_Syntax_Syntax.n)
in (match (uu____2935) with
| FStar_Syntax_Syntax.Tm_refine (uu____2951) -> begin
(aux true t1')
end
| uu____2958 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_type (uu____2973) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_constant (uu____2988) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_name (uu____3003) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3018) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3033) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_abs (uu____3062) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_quoted (uu____3095) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3116) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_let (uu____3143) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_match (uu____3170) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_meta (uu____3207) -> begin
(

let uu____3214 = (

let uu____3215 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3216 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3215 uu____3216)))
in (failwith uu____3214))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3229) -> begin
(

let uu____3256 = (

let uu____3257 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3258 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3257 uu____3258)))
in (failwith uu____3256))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____3271) -> begin
(

let uu____3294 = (

let uu____3295 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3296 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3295 uu____3296)))
in (failwith uu____3294))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____3309 = (

let uu____3310 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3311 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3310 uu____3311)))
in (failwith uu____3309))
end)))
in (

let uu____3324 = (whnf env t1)
in (aux false uu____3324)))))


let base_and_refinement : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option) = (fun env t -> (base_and_refinement_maybe_delta false env t))


let normalize_refinement : FStar_TypeChecker_Env.steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun steps env t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____3380 = (base_and_refinement env t)
in (FStar_All.pipe_right uu____3380 FStar_Pervasives_Native.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (

let uu____3420 = (FStar_Syntax_Syntax.null_bv t)
in ((uu____3420), (FStar_Syntax_Util.t_true))))


let as_refinement : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun delta1 env t -> (

let uu____3444 = (base_and_refinement_maybe_delta delta1 env t)
in (match (uu____3444) with
| (t_base, refinement) -> begin
(match (refinement) with
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end
| FStar_Pervasives_Native.Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term = (fun uu____3503 -> (match (uu____3503) with
| (t_base, refopt) -> begin
(

let uu____3534 = (match (refopt) with
| FStar_Pervasives_Native.Some (y, phi) -> begin
((y), (phi))
end
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end)
in (match (uu____3534) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl prob -> (prob_to_string wl.tcenv prob))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (

let uu____3572 = (

let uu____3575 = (

let uu____3578 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____3601 -> (match (uu____3601) with
| (uu____3608, uu____3609, x) -> begin
x
end))))
in (FStar_List.append wl.attempting uu____3578))
in (FStar_List.map (wl_prob_to_string wl) uu____3575))
in (FStar_All.pipe_right uu____3572 (FStar_String.concat "\n\t"))))


type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)


let flex_t_to_string : 'Auu____3623 . ('Auu____3623 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)  ->  Prims.string = (fun uu____3634 -> (match (uu____3634) with
| (uu____3641, c, args) -> begin
(

let uu____3644 = (print_ctx_uvar c)
in (

let uu____3645 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "%s [%s]" uu____3644 uu____3645)))
end))


let is_flex : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____3651 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____3651) with
| (head1, _args) -> begin
(

let uu____3694 = (

let uu____3695 = (FStar_Syntax_Subst.compress head1)
in uu____3695.FStar_Syntax_Syntax.n)
in (match (uu____3694) with
| FStar_Syntax_Syntax.Tm_uvar (uu____3698) -> begin
true
end
| uu____3711 -> begin
false
end))
end)))


let flex_uvar_head : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.ctx_uvar = (fun t -> (

let uu____3717 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____3717) with
| (head1, _args) -> begin
(

let uu____3760 = (

let uu____3761 = (FStar_Syntax_Subst.compress head1)
in uu____3761.FStar_Syntax_Syntax.n)
in (match (uu____3760) with
| FStar_Syntax_Syntax.Tm_uvar (u, uu____3765) -> begin
u
end
| uu____3782 -> begin
(failwith "Not a flex-uvar")
end))
end)))


let destruct_flex_t : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  worklist  ->  (flex_t * worklist) = (fun t wl -> (

let uu____3805 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____3805) with
| (head1, args) -> begin
(

let uu____3852 = (

let uu____3853 = (FStar_Syntax_Subst.compress head1)
in uu____3853.FStar_Syntax_Syntax.n)
in (match (uu____3852) with
| FStar_Syntax_Syntax.Tm_uvar (uv, ([], uu____3861)) -> begin
((((t), (uv), (args))), (wl))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, s) -> begin
(

let uu____3894 = (FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma (FStar_List.partition (fun uu___340_3919 -> (match (uu___340_3919) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let t_x = (FStar_Syntax_Syntax.bv_to_name x)
in (

let t_x' = (FStar_Syntax_Subst.subst' s t_x)
in (

let uu____3923 = (

let uu____3924 = (FStar_Syntax_Subst.compress t_x')
in uu____3924.FStar_Syntax_Syntax.n)
in (match (uu____3923) with
| FStar_Syntax_Syntax.Tm_name (y) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| uu____3928 -> begin
false
end))))
end
| uu____3929 -> begin
true
end))))
in (match (uu____3894) with
| (new_gamma, dom_binders_rev) -> begin
(

let dom_binders = (

let uu____3953 = (FStar_List.collect (fun uu___341_3965 -> (match (uu___341_3965) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let uu____3969 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3969)::[])
end
| uu____3970 -> begin
[]
end)) dom_binders_rev)
in (FStar_All.pipe_right uu____3953 FStar_List.rev))
in (

let uu____3993 = (

let uu____4000 = (

let uu____4009 = (FStar_All.pipe_right new_gamma (FStar_List.collect (fun uu___342_4031 -> (match (uu___342_4031) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let uu____4035 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4035)::[])
end
| uu____4036 -> begin
[]
end))))
in (FStar_All.pipe_right uu____4009 FStar_List.rev))
in (

let uu____4059 = (

let uu____4062 = (FStar_Syntax_Syntax.mk_Total uv.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Syntax_Util.arrow dom_binders uu____4062))
in (new_uvar (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason "; force delayed") wl t.FStar_Syntax_Syntax.pos new_gamma uu____4000 uu____4059 uv.FStar_Syntax_Syntax.ctx_uvar_should_check)))
in (match (uu____3993) with
| (v1, t_v, wl1) -> begin
(

let args_sol = (FStar_List.map (fun uu____4097 -> (match (uu____4097) with
| (x, i) -> begin
(

let uu____4116 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____4116), (i)))
end)) dom_binders)
in (

let sol = (FStar_Syntax_Syntax.mk_Tm_app t_v args_sol FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let args_sol_s = (FStar_List.map (fun uu____4147 -> (match (uu____4147) with
| (a, i) -> begin
(

let uu____4166 = (FStar_Syntax_Subst.subst' s a)
in ((uu____4166), (i)))
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
| uu____4188 -> begin
(failwith "Not a flex-uvar")
end))
end)))


let u_abs : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____4208 = (

let uu____4231 = (

let uu____4232 = (FStar_Syntax_Subst.compress k)
in uu____4232.FStar_Syntax_Syntax.n)
in (match (uu____4231) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((Prims.op_Equality (FStar_List.length bs) (FStar_List.length ys))) with
| true -> begin
(

let uu____4313 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (uu____4313)))
end
| uu____4346 -> begin
(

let uu____4347 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____4347) with
| (ys', t1, uu____4380) -> begin
(

let uu____4385 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t1))), (uu____4385)))
end))
end)
end
| uu____4424 -> begin
(

let uu____4425 = (

let uu____4430 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____4430)))
in ((((ys), (t))), (uu____4425)))
end))
in (match (uu____4208) with
| ((ys1, t1), (xs, c)) -> begin
(match ((Prims.op_disEquality (FStar_List.length xs) (FStar_List.length ys1))) with
| true -> begin
(FStar_Syntax_Util.abs ys1 t1 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None []))))
end
| uu____4521 -> begin
(

let c1 = (

let uu____4523 = (FStar_Syntax_Util.rename_binders xs ys1)
in (FStar_Syntax_Subst.subst_comp uu____4523 c))
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

let uu____4597 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____4597) with
| true -> begin
(

let uu____4598 = (FStar_Util.string_of_int (p_pid prob))
in (

let uu____4599 = (print_ctx_uvar uv)
in (

let uu____4600 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" uu____4598 uu____4599 uu____4600))))
end
| uu____4601 -> begin
()
end));
(

let phi2 = (FStar_Syntax_Util.abs xs phi1 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in ((

let uu____4606 = (

let uu____4607 = (FStar_Util.string_of_int (p_pid prob))
in (Prims.strcat "solve_prob\'.sol." uu____4607))
in (

let uu____4608 = (

let uu____4611 = (p_scope prob)
in (FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst) uu____4611))
in (FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) uu____4606 uu____4608 phi2)));
(FStar_Syntax_Util.set_uvar uv.FStar_Syntax_Syntax.ctx_uvar_head phi2);
));
))
in (

let uv = (p_guard_uvar prob)
in (

let fail1 = (fun uu____4644 -> (

let uu____4645 = (

let uu____4646 = (FStar_Syntax_Print.ctx_uvar_to_string uv)
in (

let uu____4647 = (FStar_Syntax_Print.term_to_string (p_guard prob))
in (FStar_Util.format2 "Impossible: this instance %s has already been assigned a solution\n%s\n" uu____4646 uu____4647)))
in (failwith uu____4645)))
in (

let args_as_binders = (fun args -> (FStar_All.pipe_right args (FStar_List.collect (fun uu____4711 -> (match (uu____4711) with
| (a, i) -> begin
(

let uu____4732 = (

let uu____4733 = (FStar_Syntax_Subst.compress a)
in uu____4733.FStar_Syntax_Syntax.n)
in (match (uu____4732) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(((x), (i)))::[]
end
| uu____4759 -> begin
((fail1 ());
[];
)
end))
end)))))
in (

let wl1 = (

let g = (whnf wl.tcenv (p_guard prob))
in (

let uu____4769 = (

let uu____4770 = (is_flex g)
in (not (uu____4770)))
in (match (uu____4769) with
| true -> begin
(match (resolve_ok) with
| true -> begin
wl
end
| uu____4771 -> begin
((fail1 ());
wl;
)
end)
end
| uu____4773 -> begin
(

let uu____4774 = (destruct_flex_t g wl)
in (match (uu____4774) with
| ((uu____4779, uv1, args), wl1) -> begin
((

let uu____4784 = (args_as_binders args)
in (assign_solution uu____4784 uv1 phi));
wl1;
)
end))
end)))
in ((commit uvis);
(

let uu___365_4786 = wl1
in {attempting = uu___365_4786.attempting; wl_deferred = uu___365_4786.wl_deferred; ctr = (wl1.ctr + (Prims.parse_int "1")); defer_ok = uu___365_4786.defer_ok; smt_ok = uu___365_4786.smt_ok; umax_heuristic_ok = uu___365_4786.umax_heuristic_ok; tcenv = uu___365_4786.tcenv; wl_implicits = uu___365_4786.wl_implicits});
)))))));
))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____4807 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____4807) with
| true -> begin
(

let uu____4808 = (FStar_Util.string_of_int pid)
in (

let uu____4809 = (

let uu____4810 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right uu____4810 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with [%s]\n" uu____4808 uu____4809)))
end
| uu____4815 -> begin
()
end));
(commit sol);
(

let uu___366_4817 = wl
in {attempting = uu___366_4817.attempting; wl_deferred = uu___366_4817.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___366_4817.defer_ok; smt_ok = uu___366_4817.smt_ok; umax_heuristic_ok = uu___366_4817.umax_heuristic_ok; tcenv = uu___366_4817.tcenv; wl_implicits = uu___366_4817.wl_implicits});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> ((def_check_prob "solve_prob.prob" prob);
(FStar_Util.iter_opt logical_guard (def_check_scoped "solve_prob.guard" prob));
(

let conj_guard1 = (fun t g -> (match (((t), (g))) with
| (uu____4879, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (FStar_Pervasives_Native.None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
FStar_Pervasives_Native.Some (f)
end
| (FStar_Pervasives_Native.Some (t1), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(

let uu____4907 = (FStar_Syntax_Util.mk_conj t1 f)
in FStar_Pervasives_Native.Some (uu____4907))
end))
in ((

let uu____4913 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____4913) with
| true -> begin
(

let uu____4914 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (

let uu____4915 = (

let uu____4916 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right uu____4916 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____4914 uu____4915)))
end
| uu____4921 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
));
))


let occurs : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool) = (fun uk t -> (

let uvars1 = (

let uu____4941 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right uu____4941 FStar_Util.set_elements))
in (

let occurs = (FStar_All.pipe_right uvars1 (FStar_Util.for_some (fun uv -> (FStar_Syntax_Unionfind.equiv uv.FStar_Syntax_Syntax.ctx_uvar_head uk.FStar_Syntax_Syntax.ctx_uvar_head))))
in ((uvars1), (occurs)))))


let occurs_check : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool * Prims.string FStar_Pervasives_Native.option) = (fun uk t -> (

let uu____4975 = (occurs uk t)
in (match (uu____4975) with
| (uvars1, occurs1) -> begin
(

let msg = (match ((not (occurs1))) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5003 -> begin
(

let uu____5004 = (

let uu____5005 = (FStar_Syntax_Print.uvar_to_string uk.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____5006 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" uu____5005 uu____5006)))
in FStar_Pervasives_Native.Some (uu____5004))
end)
in ((uvars1), ((not (occurs1))), (msg)))
end)))


let rec maximal_prefix : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.binders)) = (fun bs bs' -> (match (((bs), (bs'))) with
| (((b, i))::bs_tail, ((b', i'))::bs'_tail) -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
(

let uu____5119 = (maximal_prefix bs_tail bs'_tail)
in (match (uu____5119) with
| (pfx, rest) -> begin
(((((b), (i)))::pfx), (rest))
end))
end
| uu____5158 -> begin
(([]), (((bs), (bs'))))
end)
end
| uu____5169 -> begin
(([]), (((bs), (bs'))))
end))


let extend_gamma : FStar_Syntax_Syntax.gamma  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binding Prims.list = (fun g bs -> (FStar_List.fold_left (fun g1 uu____5225 -> (match (uu____5225) with
| (x, uu____5237) -> begin
(FStar_Syntax_Syntax.Binding_var (x))::g1
end)) g bs))


let gamma_until : FStar_Syntax_Syntax.gamma  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binding Prims.list = (fun g bs -> (

let uu____5254 = (FStar_List.last bs)
in (match (uu____5254) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (x, uu____5278) -> begin
(

let uu____5289 = (FStar_Util.prefix_until (fun uu___343_5304 -> (match (uu___343_5304) with
| FStar_Syntax_Syntax.Binding_var (x') -> begin
(FStar_Syntax_Syntax.bv_eq x x')
end
| uu____5306 -> begin
false
end)) g)
in (match (uu____5289) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____5319, bx, rest) -> begin
(bx)::rest
end))
end)))


let restrict_ctx : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.ctx_uvar  ->  worklist  ->  worklist = (fun tgt src wl -> (

let uu____5355 = (maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders src.FStar_Syntax_Syntax.ctx_uvar_binders)
in (match (uu____5355) with
| (pfx, uu____5365) -> begin
(

let g = (gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx)
in (

let uu____5377 = (new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl src.FStar_Syntax_Syntax.ctx_uvar_range g pfx src.FStar_Syntax_Syntax.ctx_uvar_typ src.FStar_Syntax_Syntax.ctx_uvar_should_check)
in (match (uu____5377) with
| (uu____5384, src', wl1) -> begin
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
| uu____5496 -> begin
out
end)) FStar_Syntax_Syntax.no_names g)
in (

let uu____5497 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____5561 uu____5562 -> (match (((uu____5561), (uu____5562))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____5665 = (

let uu____5666 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation uu____5666))
in (match (uu____5665) with
| true -> begin
((isect), (isect_set))
end
| uu____5691 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____5695 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____5695) with
| true -> begin
(

let uu____5710 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (uu____5710)))
end
| uu____5731 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (ctx_binders))))
in (match (uu____5497) with
| (isect, uu____5759) -> begin
(FStar_List.rev isect)
end))))))


let binders_eq : 'Auu____5794 'Auu____5795 . (FStar_Syntax_Syntax.bv * 'Auu____5794) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____5795) Prims.list  ->  Prims.bool = (fun v1 v2 -> ((Prims.op_Equality (FStar_List.length v1) (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____5852 uu____5853 -> (match (((uu____5852), (uu____5853))) with
| ((a, uu____5871), (b, uu____5873)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let name_exists_in_binders : 'Auu____5888 . FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.bv * 'Auu____5888) Prims.list  ->  Prims.bool = (fun x bs -> (FStar_Util.for_some (fun uu____5918 -> (match (uu____5918) with
| (y, uu____5924) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end)) bs))


let pat_vars : 'Auu____5933 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____5933) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option = (fun env ctx args -> (

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

let uu____6095 = ((name_exists_in_binders a seen) || (name_exists_in_binders a ctx))
in (match (uu____6095) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____6116 -> begin
(aux ((((a), (i)))::seen) args2)
end))
end
| uu____6125 -> begin
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
| uu____6172 -> begin
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
| uu____6210 -> begin
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
| uu____6223 -> begin
false
end))


let string_of_match_result : match_result  ->  Prims.string = (fun uu___344_6228 -> (match (uu___344_6228) with
| MisMatch (d1, d2) -> begin
(

let uu____6239 = (

let uu____6240 = (FStar_Common.string_of_option FStar_Syntax_Print.delta_depth_to_string d1)
in (

let uu____6241 = (

let uu____6242 = (

let uu____6243 = (FStar_Common.string_of_option FStar_Syntax_Print.delta_depth_to_string d2)
in (Prims.strcat uu____6243 ")"))
in (Prims.strcat ") (" uu____6242))
in (Prims.strcat uu____6240 uu____6241)))
in (Prims.strcat "MisMatch (" uu____6239))
end
| HeadMatch (u) -> begin
(

let uu____6245 = (FStar_Util.string_of_bool u)
in (Prims.strcat "HeadMatch " uu____6245))
end
| FullMatch -> begin
"FullMatch"
end))


let head_match : match_result  ->  match_result = (fun uu___345_6250 -> (match (uu___345_6250) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| HeadMatch (true) -> begin
HeadMatch (true)
end
| uu____6265 -> begin
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
| uu____6278 -> begin
FStar_Syntax_Syntax.delta_constant
end)
end
| FStar_Syntax_Syntax.Delta_constant_at_level (i) when (i > (Prims.parse_int "0")) -> begin
(

let uu____6280 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____6280) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Syntax.delta_constant
end
| uu____6291 -> begin
d
end))
end
| d1 -> begin
d1
end)))


let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____6314) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____6323) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____6349 = (FStar_Syntax_Util.unfold_lazy i)
in (delta_depth_of_term env uu____6349))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_bvar (uu____6350) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_name (uu____6351) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uvar (uu____6352) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_let (uu____6365) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_match (uu____6378) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____6402) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____6408, uu____6409) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____6451) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____6476; FStar_Syntax_Syntax.index = uu____6477; FStar_Syntax_Syntax.sort = t2}, uu____6479) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_constant (uu____6486) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)
end
| FStar_Syntax_Syntax.Tm_type (uu____6487) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____6488) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____6503) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)
end
| FStar_Syntax_Syntax.Tm_abs (uu____6510) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____6530 = (fv_delta_depth env fv)
in FStar_Pervasives_Native.Some (uu____6530))
end)))


let rec head_matches : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  match_result = (fun env t1 t2 -> (

let t11 = (FStar_Syntax_Util.unmeta t1)
in (

let t21 = (FStar_Syntax_Util.unmeta t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_lazy ({FStar_Syntax_Syntax.blob = uu____6548; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding (uu____6549); FStar_Syntax_Syntax.ltyp = uu____6550; FStar_Syntax_Syntax.rng = uu____6551}), uu____6552) -> begin
(

let uu____6563 = (FStar_Syntax_Util.unlazy t11)
in (head_matches env uu____6563 t21))
end
| (uu____6564, FStar_Syntax_Syntax.Tm_lazy ({FStar_Syntax_Syntax.blob = uu____6565; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding (uu____6566); FStar_Syntax_Syntax.ltyp = uu____6567; FStar_Syntax_Syntax.rng = uu____6568})) -> begin
(

let uu____6579 = (FStar_Syntax_Util.unlazy t21)
in (head_matches env t11 uu____6579))
end
| (FStar_Syntax_Syntax.Tm_name (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(match ((FStar_Syntax_Syntax.bv_eq x y)) with
| true -> begin
FullMatch
end
| uu____6582 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____6589 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____6589) with
| true -> begin
FullMatch
end
| uu____6590 -> begin
(

let uu____6591 = (

let uu____6600 = (

let uu____6603 = (fv_delta_depth env f)
in FStar_Pervasives_Native.Some (uu____6603))
in (

let uu____6604 = (

let uu____6607 = (fv_delta_depth env g)
in FStar_Pervasives_Native.Some (uu____6607))
in ((uu____6600), (uu____6604))))
in MisMatch (uu____6591))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____6613), FStar_Syntax_Syntax.Tm_uinst (g, uu____6615)) -> begin
(

let uu____6624 = (head_matches env f g)
in (FStar_All.pipe_right uu____6624 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____6627 = (FStar_Const.eq_const c d)
in (match (uu____6627) with
| true -> begin
FullMatch
end
| uu____6628 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, uu____6634), FStar_Syntax_Syntax.Tm_uvar (uv', uu____6636)) -> begin
(

let uu____6669 = (FStar_Syntax_Unionfind.equiv uv.FStar_Syntax_Syntax.ctx_uvar_head uv'.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____6669) with
| true -> begin
FullMatch
end
| uu____6670 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____6676), FStar_Syntax_Syntax.Tm_refine (y, uu____6678)) -> begin
(

let uu____6687 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____6687 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____6689), uu____6690) -> begin
(

let uu____6695 = (head_matches env x.FStar_Syntax_Syntax.sort t21)
in (FStar_All.pipe_right uu____6695 head_match))
end
| (uu____6696, FStar_Syntax_Syntax.Tm_refine (x, uu____6698)) -> begin
(

let uu____6703 = (head_matches env t11 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____6703 head_match))
end
| (FStar_Syntax_Syntax.Tm_type (uu____6704), FStar_Syntax_Syntax.Tm_type (uu____6705)) -> begin
HeadMatch (false)
end
| (FStar_Syntax_Syntax.Tm_arrow (uu____6706), FStar_Syntax_Syntax.Tm_arrow (uu____6707)) -> begin
HeadMatch (false)
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____6737), FStar_Syntax_Syntax.Tm_app (head', uu____6739)) -> begin
(

let uu____6788 = (head_matches env head1 head')
in (FStar_All.pipe_right uu____6788 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____6790), uu____6791) -> begin
(

let uu____6816 = (head_matches env head1 t21)
in (FStar_All.pipe_right uu____6816 head_match))
end
| (uu____6817, FStar_Syntax_Syntax.Tm_app (head1, uu____6819)) -> begin
(

let uu____6844 = (head_matches env t11 head1)
in (FStar_All.pipe_right uu____6844 head_match))
end
| (FStar_Syntax_Syntax.Tm_let (uu____6845), FStar_Syntax_Syntax.Tm_let (uu____6846)) -> begin
HeadMatch (true)
end
| (FStar_Syntax_Syntax.Tm_match (uu____6871), FStar_Syntax_Syntax.Tm_match (uu____6872)) -> begin
HeadMatch (true)
end
| uu____6917 -> begin
(

let uu____6922 = (

let uu____6931 = (delta_depth_of_term env t11)
in (

let uu____6934 = (delta_depth_of_term env t21)
in ((uu____6931), (uu____6934))))
in MisMatch (uu____6922))
end))))


let head_matches_delta : FStar_TypeChecker_Env.env  ->  worklist  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (match_result * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) FStar_Pervasives_Native.option) = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let head1 = (FStar_Syntax_Util.head_of t)
in ((

let uu____6999 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelDelta")))
in (match (uu____6999) with
| true -> begin
(

let uu____7000 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____7001 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.print2 "Head of %s is %s\n" uu____7000 uu____7001)))
end
| uu____7002 -> begin
()
end));
(

let uu____7003 = (

let uu____7004 = (FStar_Syntax_Util.un_uinst head1)
in uu____7004.FStar_Syntax_Syntax.n)
in (match (uu____7003) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____7010 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____7010) with
| FStar_Pervasives_Native.None -> begin
((

let uu____7024 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelDelta")))
in (match (uu____7024) with
| true -> begin
(

let uu____7025 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.print1 "No definition found for %s\n" uu____7025))
end
| uu____7026 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (uu____7027) -> begin
(

let basic_steps = (FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]
in (

let steps = (match (wl.smt_ok) with
| true -> begin
basic_steps
end
| uu____7040 -> begin
(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::basic_steps
end)
in (

let t' = (FStar_TypeChecker_Normalize.normalize steps env t)
in (

let uu____7042 = (

let uu____7043 = (FStar_Syntax_Util.eq_tm t t')
in (Prims.op_Equality uu____7043 FStar_Syntax_Util.Equal))
in (match (uu____7042) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7046 -> begin
((

let uu____7048 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelDelta")))
in (match (uu____7048) with
| true -> begin
(

let uu____7049 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____7050 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Inlined %s to %s\n" uu____7049 uu____7050)))
end
| uu____7051 -> begin
()
end));
FStar_Pervasives_Native.Some (t');
)
end)))))
end))
end
| uu____7052 -> begin
FStar_Pervasives_Native.None
end));
)))
in (

let success = (fun d r t11 t21 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (((t11), (t21)))
end
| uu____7100 -> begin
FStar_Pervasives_Native.None
end))))
in (

let fail1 = (fun d r t11 t21 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (((t11), (t21)))
end
| uu____7152 -> begin
FStar_Pervasives_Native.None
end))))
in (

let rec aux = (fun retry n_delta t11 t21 -> (

let r = (head_matches env t11 t21)
in ((

let uu____7190 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelDelta")))
in (match (uu____7190) with
| true -> begin
(

let uu____7191 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____7192 = (FStar_Syntax_Print.term_to_string t21)
in (

let uu____7193 = (string_of_match_result r)
in (FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7191 uu____7192 uu____7193))))
end
| uu____7194 -> begin
()
end));
(

let reduce_one_and_try_again = (fun d1 d2 -> (

let d1_greater_than_d2 = (FStar_TypeChecker_Common.delta_depth_greater_than d1 d2)
in (

let uu____7217 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Env.UnfoldUntil (d2))::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::[]) env t11)
in ((t1'), (t21)))
end
| uu____7227 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Env.UnfoldUntil (d1))::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::[]) env t21)
in ((t11), (t2')))
end)
in (match (uu____7217) with
| (t12, t22) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
end))))
in (

let reduce_both_and_try_again = (fun d r1 -> (

let uu____7262 = (FStar_TypeChecker_Common.decr_delta_depth d)
in (match (uu____7262) with
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
| MisMatch (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational_at_level (uu____7294)), uu____7295) -> begin
(match ((not (retry))) with
| true -> begin
(fail1 n_delta r t11 t21)
end
| uu____7312 -> begin
(

let uu____7313 = (

let uu____7322 = (maybe_inline t11)
in (

let uu____7325 = (maybe_inline t21)
in ((uu____7322), (uu____7325))))
in (match (uu____7313) with
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
| MisMatch (uu____7362, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational_at_level (uu____7363))) -> begin
(match ((not (retry))) with
| true -> begin
(fail1 n_delta r t11 t21)
end
| uu____7380 -> begin
(

let uu____7381 = (

let uu____7390 = (maybe_inline t11)
in (

let uu____7393 = (maybe_inline t21)
in ((uu____7390), (uu____7393))))
in (match (uu____7381) with
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
| MisMatch (uu____7442) -> begin
(fail1 n_delta r t11 t21)
end
| uu____7451 -> begin
(success n_delta r t11 t21)
end)));
)))
in (

let r = (aux true (Prims.parse_int "0") t1 t2)
in ((

let uu____7464 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelDelta")))
in (match (uu____7464) with
| true -> begin
(

let uu____7465 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____7466 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____7467 = (string_of_match_result (FStar_Pervasives_Native.fst r))
in (

let uu____7474 = (match ((FStar_Option.isNone (FStar_Pervasives_Native.snd r))) with
| true -> begin
"None"
end
| uu____7485 -> begin
(

let uu____7486 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd r) FStar_Util.must)
in (FStar_All.pipe_right uu____7486 (fun uu____7520 -> (match (uu____7520) with
| (t11, t21) -> begin
(

let uu____7527 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____7528 = (

let uu____7529 = (FStar_Syntax_Print.term_to_string t21)
in (Prims.strcat "; " uu____7529))
in (Prims.strcat uu____7527 uu____7528)))
end))))
end)
in (FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n" uu____7465 uu____7466 uu____7467 uu____7474)))))
end
| uu____7530 -> begin
()
end));
r;
)))))))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____7541 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____7541 FStar_Pervasives_Native.fst)))


let rank_t_num : FStar_TypeChecker_Common.rank_t  ->  Prims.int = (fun uu___346_7554 -> (match (uu___346_7554) with
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

let uu___367_7591 = p
in (

let uu____7594 = (whnf tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____7595 = (whnf tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___367_7591.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____7594; FStar_TypeChecker_Common.relation = uu___367_7591.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____7595; FStar_TypeChecker_Common.element = uu___367_7591.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___367_7591.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___367_7591.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___367_7591.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___367_7591.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___367_7591.FStar_TypeChecker_Common.rank}))))


let compress_prob : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun tcenv p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p1) -> begin
(

let uu____7609 = (compress_tprob tcenv p1)
in (FStar_All.pipe_right uu____7609 (fun _0_5 -> FStar_TypeChecker_Common.TProb (_0_5))))
end
| FStar_TypeChecker_Common.CProb (uu____7614) -> begin
p
end))


let rank : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob) = (fun tcenv pr -> (

let prob = (

let uu____7636 = (compress_prob tcenv pr)
in (FStar_All.pipe_right uu____7636 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____7644 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____7644) with
| (lh, lhs_args) -> begin
(

let uu____7691 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____7691) with
| (rh, rhs_args) -> begin
(

let uu____7738 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____7751), FStar_Syntax_Syntax.Tm_uvar (uu____7752)) -> begin
(match (((lhs_args), (rhs_args))) with
| ([], []) when (Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
((FStar_TypeChecker_Common.Flex_flex_pattern_eq), (tp))
end
| uu____7841 -> begin
((FStar_TypeChecker_Common.Flex_flex), (tp))
end)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____7868), uu____7869) when (Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
((FStar_TypeChecker_Common.Flex_rigid_eq), (tp))
end
| (uu____7884, FStar_Syntax_Syntax.Tm_uvar (uu____7885)) when (Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
((FStar_TypeChecker_Common.Flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____7900), FStar_Syntax_Syntax.Tm_arrow (uu____7901)) -> begin
((FStar_TypeChecker_Common.Flex_rigid_eq), ((

let uu___368_7931 = tp
in {FStar_TypeChecker_Common.pid = uu___368_7931.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___368_7931.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___368_7931.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___368_7931.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___368_7931.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___368_7931.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___368_7931.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___368_7931.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___368_7931.FStar_TypeChecker_Common.rank})))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____7934), FStar_Syntax_Syntax.Tm_type (uu____7935)) -> begin
((FStar_TypeChecker_Common.Flex_rigid_eq), ((

let uu___368_7951 = tp
in {FStar_TypeChecker_Common.pid = uu___368_7951.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___368_7951.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___368_7951.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___368_7951.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___368_7951.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___368_7951.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___368_7951.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___368_7951.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___368_7951.FStar_TypeChecker_Common.rank})))
end
| (FStar_Syntax_Syntax.Tm_type (uu____7954), FStar_Syntax_Syntax.Tm_uvar (uu____7955)) -> begin
((FStar_TypeChecker_Common.Flex_rigid_eq), ((

let uu___368_7971 = tp
in {FStar_TypeChecker_Common.pid = uu___368_7971.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___368_7971.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___368_7971.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___368_7971.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___368_7971.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___368_7971.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___368_7971.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___368_7971.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___368_7971.FStar_TypeChecker_Common.rank})))
end
| (uu____7974, FStar_Syntax_Syntax.Tm_uvar (uu____7975)) -> begin
((FStar_TypeChecker_Common.Rigid_flex), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____7990), uu____7991) -> begin
((FStar_TypeChecker_Common.Flex_rigid), (tp))
end
| (uu____8006, FStar_Syntax_Syntax.Tm_uvar (uu____8007)) -> begin
((FStar_TypeChecker_Common.Rigid_flex), (tp))
end
| (uu____8022, uu____8023) -> begin
((FStar_TypeChecker_Common.Rigid_rigid), (tp))
end)
in (match (uu____7738) with
| (rank, tp1) -> begin
(

let uu____8036 = (FStar_All.pipe_right (

let uu___369_8040 = tp1
in {FStar_TypeChecker_Common.pid = uu___369_8040.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___369_8040.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___369_8040.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___369_8040.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___369_8040.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___369_8040.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___369_8040.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___369_8040.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___369_8040.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rank)}) (fun _0_6 -> FStar_TypeChecker_Common.TProb (_0_6)))
in ((rank), (uu____8036)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____8046 = (FStar_All.pipe_right (

let uu___370_8050 = cp
in {FStar_TypeChecker_Common.pid = uu___370_8050.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___370_8050.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___370_8050.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___370_8050.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___370_8050.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___370_8050.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___370_8050.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___370_8050.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___370_8050.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (FStar_TypeChecker_Common.Rigid_rigid)}) (fun _0_7 -> FStar_TypeChecker_Common.CProb (_0_7)))
in ((FStar_TypeChecker_Common.Rigid_rigid), (uu____8046)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option = (fun wl -> (

let rec aux = (fun uu____8111 probs -> (match (uu____8111) with
| (min_rank, min1, out) -> begin
(match (probs) with
| [] -> begin
(match (((min1), (min_rank))) with
| (FStar_Pervasives_Native.Some (p), FStar_Pervasives_Native.Some (r)) -> begin
FStar_Pervasives_Native.Some (((p), (out), (r)))
end
| uu____8192 -> begin
FStar_Pervasives_Native.None
end)
end
| (hd1)::tl1 -> begin
(

let uu____8213 = (rank wl.tcenv hd1)
in (match (uu____8213) with
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
| uu____8271 -> begin
(

let uu____8272 = ((Prims.op_Equality min_rank FStar_Pervasives_Native.None) || (

let uu____8276 = (FStar_Option.get min_rank)
in (rank_less_than rank1 uu____8276)))
in (match (uu____8272) with
| true -> begin
(match (min1) with
| FStar_Pervasives_Native.None -> begin
(aux ((FStar_Pervasives_Native.Some (rank1)), (FStar_Pervasives_Native.Some (hd2)), (out)) tl1)
end
| FStar_Pervasives_Native.Some (m) -> begin
(aux ((FStar_Pervasives_Native.Some (rank1)), (FStar_Pervasives_Native.Some (hd2)), ((m)::out)) tl1)
end)
end
| uu____8310 -> begin
(aux ((min_rank), (min1), ((hd2)::out)) tl1)
end))
end)
end))
end)
end))
in (aux ((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), ([])) wl.attempting)))


let flex_prob_closing : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun tcenv bs p -> (

let flex_will_be_closed = (fun t -> (

let uu____8344 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____8344) with
| (hd1, uu____8362) -> begin
(

let uu____8387 = (

let uu____8388 = (FStar_Syntax_Subst.compress hd1)
in uu____8388.FStar_Syntax_Syntax.n)
in (match (uu____8387) with
| FStar_Syntax_Syntax.Tm_uvar (u, uu____8392) -> begin
(FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders (FStar_Util.for_some (fun uu____8426 -> (match (uu____8426) with
| (y, uu____8434) -> begin
(FStar_All.pipe_right bs (FStar_Util.for_some (fun uu____8456 -> (match (uu____8456) with
| (x, uu____8464) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end))))
end))))
end
| uu____8469 -> begin
false
end))
end)))
in (

let uu____8470 = (rank tcenv p)
in (match (uu____8470) with
| (r, p1) -> begin
(match (p1) with
| FStar_TypeChecker_Common.CProb (uu____8477) -> begin
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
| UFailed of Prims.string


let uu___is_UDeferred : univ_eq_sol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UDeferred (_0) -> begin
true
end
| uu____8504 -> begin
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
| uu____8518 -> begin
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
| uu____8532 -> begin
false
end))


let __proj__UFailed__item___0 : univ_eq_sol  ->  Prims.string = (fun projectee -> (match (projectee) with
| UFailed (_0) -> begin
_0
end))


let rec really_solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun pid_orig wl u1 u2 -> (

let u11 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (

let u21 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (

let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u3 -> (

let uu____8584 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____8584) with
| (k, uu____8590) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Syntax_Unionfind.univ_equiv v1 v2)
end
| uu____8600 -> begin
false
end)
end)))))
end
| uu____8601 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (

let rec filter_out_common_univs = (fun u12 u22 -> (

let common_elts = (FStar_All.pipe_right u12 (FStar_List.fold_left (fun uvs uv1 -> (

let uu____8653 = (FStar_All.pipe_right u22 (FStar_List.existsML (fun uv2 -> (

let uu____8659 = (FStar_Syntax_Util.compare_univs uv1 uv2)
in (Prims.op_Equality uu____8659 (Prims.parse_int "0"))))))
in (match (uu____8653) with
| true -> begin
(uv1)::uvs
end
| uu____8662 -> begin
uvs
end))) []))
in (

let filter1 = (FStar_List.filter (fun u -> (

let uu____8675 = (FStar_All.pipe_right common_elts (FStar_List.existsML (fun u' -> (

let uu____8681 = (FStar_Syntax_Util.compare_univs u u')
in (Prims.op_Equality uu____8681 (Prims.parse_int "0"))))))
in (not (uu____8675)))))
in (

let uu____8682 = (filter1 u12)
in (

let uu____8685 = (filter1 u22)
in ((uu____8682), (uu____8685)))))))
in (

let try_umax_components = (fun u12 u22 msg -> (match ((not (wl.umax_heuristic_ok))) with
| true -> begin
UFailed ("Unable to unify universe terms with umax")
end
| uu____8708 -> begin
(match (((u12), (u22))) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(

let uu____8715 = (filter_out_common_univs us1 us2)
in (match (uu____8715) with
| (us11, us21) -> begin
(match ((Prims.op_Equality (FStar_List.length us11) (FStar_List.length us21))) with
| true -> begin
(

let rec aux = (fun wl1 us12 us22 -> (match (((us12), (us22))) with
| ((u13)::us13, (u23)::us23) -> begin
(

let uu____8774 = (really_solve_universe_eq pid_orig wl1 u13 u23)
in (match (uu____8774) with
| USolved (wl2) -> begin
(aux wl2 us13 us23)
end
| failed -> begin
failed
end))
end
| uu____8777 -> begin
USolved (wl1)
end))
in (aux wl us11 us21))
end
| uu____8786 -> begin
(

let uu____8787 = (

let uu____8788 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____8789 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" uu____8788 uu____8789)))
in UFailed (uu____8787))
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

let uu____8813 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____8813) with
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

let uu____8839 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____8839) with
| USolved (wl2) -> begin
(aux wl2 us2)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____8842 -> begin
(

let uu____8847 = (

let uu____8848 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____8849 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" uu____8848 uu____8849 msg)))
in UFailed (uu____8847))
end)
end))
in (match (((u11), (u21))) with
| (FStar_Syntax_Syntax.U_bvar (uu____8850), uu____8851) -> begin
(

let uu____8852 = (

let uu____8853 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____8854 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____8853 uu____8854)))
in (failwith uu____8852))
end
| (FStar_Syntax_Syntax.U_unknown, uu____8855) -> begin
(

let uu____8856 = (

let uu____8857 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____8858 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____8857 uu____8858)))
in (failwith uu____8856))
end
| (uu____8859, FStar_Syntax_Syntax.U_bvar (uu____8860)) -> begin
(

let uu____8861 = (

let uu____8862 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____8863 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____8862 uu____8863)))
in (failwith uu____8861))
end
| (uu____8864, FStar_Syntax_Syntax.U_unknown) -> begin
(

let uu____8865 = (

let uu____8866 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____8867 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____8866 uu____8867)))
in (failwith uu____8865))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____8870 -> begin
UFailed ("Incompatible universes")
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

let uu____8891 = (FStar_Syntax_Unionfind.univ_equiv v1 v2)
in (match (uu____8891) with
| true -> begin
USolved (wl)
end
| uu____8892 -> begin
(

let wl1 = (extend_solution pid_orig ((UNIV (((v1), (u21))))::[]) wl)
in USolved (wl1))
end))
end
| (FStar_Syntax_Syntax.U_unif (v1), u) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____8905 = (occurs_univ v1 u3)
in (match (uu____8905) with
| true -> begin
(

let uu____8906 = (

let uu____8907 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____8908 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____8907 uu____8908)))
in (try_umax_components u11 u21 uu____8906))
end
| uu____8909 -> begin
(

let uu____8910 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____8910))
end)))
end
| (u, FStar_Syntax_Syntax.U_unif (v1)) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____8922 = (occurs_univ v1 u3)
in (match (uu____8922) with
| true -> begin
(

let uu____8923 = (

let uu____8924 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____8925 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____8924 uu____8925)))
in (try_umax_components u11 u21 uu____8923))
end
| uu____8926 -> begin
(

let uu____8927 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____8927))
end)))
end
| (FStar_Syntax_Syntax.U_max (uu____8928), uu____8929) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____8932 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____8935 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____8935) with
| true -> begin
USolved (wl)
end
| uu____8936 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (uu____8937, FStar_Syntax_Syntax.U_max (uu____8938)) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____8941 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____8944 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____8944) with
| true -> begin
USolved (wl)
end
| uu____8945 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (FStar_Syntax_Syntax.U_succ (uu____8946), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_succ (uu____8947), FStar_Syntax_Syntax.U_name (uu____8948)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ (uu____8949)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name (uu____8950)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____8951), FStar_Syntax_Syntax.U_succ (uu____8952)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____8953), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end)))))))


let solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (match (wl.tcenv.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
USolved (wl)
end
| uu____8974 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders : 'a 'b . ('a Prims.list * ('a Prims.list  ->  'b))  ->  ('a Prims.list * ('a Prims.list  ->  'b))  ->  (('a Prims.list * 'b) * ('a Prims.list * 'b)) = (fun bc1 bc2 -> (

let uu____9053 = bc1
in (match (uu____9053) with
| (bs1, mk_cod1) -> begin
(

let uu____9097 = bc2
in (match (uu____9097) with
| (bs2, mk_cod2) -> begin
(

let rec aux = (fun bs11 bs21 -> (match (((bs11), (bs21))) with
| ((x)::xs, (y)::ys) -> begin
(

let uu____9208 = (aux xs ys)
in (match (uu____9208) with
| ((xs1, xr), (ys1, yr)) -> begin
(((((x)::xs1), (xr))), ((((y)::ys1), (yr))))
end))
end
| (xs, ys) -> begin
(

let uu____9291 = (

let uu____9298 = (mk_cod1 xs)
in (([]), (uu____9298)))
in (

let uu____9301 = (

let uu____9308 = (mk_cod2 ys)
in (([]), (uu____9308)))
in ((uu____9291), (uu____9301))))
end))
in (aux bs1 bs2))
end))
end)))


let guard_of_prob : FStar_TypeChecker_Env.env  ->  worklist  ->  tprob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * worklist) = (fun env wl problem t1 t2 -> (

let has_type_guard = (fun t11 t21 -> (match (problem.FStar_TypeChecker_Common.element) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____9376 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Util.mk_has_type t11 uu____9376 t21))
end
| FStar_Pervasives_Native.None -> begin
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None t11)
in (

let u_x = (env.FStar_TypeChecker_Env.universe_of env t11)
in (

let uu____9379 = (

let uu____9380 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t11 uu____9380 t21))
in (FStar_Syntax_Util.mk_forall u_x x uu____9379))))
end))
in (match (problem.FStar_TypeChecker_Common.relation) with
| FStar_TypeChecker_Common.EQ -> begin
(mk_eq2 wl env (FStar_TypeChecker_Common.TProb (problem)) t1 t2)
end
| FStar_TypeChecker_Common.SUB -> begin
(

let uu____9385 = (has_type_guard t1 t2)
in ((uu____9385), (wl)))
end
| FStar_TypeChecker_Common.SUBINV -> begin
(

let uu____9386 = (has_type_guard t2 t1)
in ((uu____9386), (wl)))
end)))


let is_flex_pat : 'Auu____9395 'Auu____9396 'Auu____9397 . ('Auu____9395 * 'Auu____9396 * 'Auu____9397 Prims.list)  ->  Prims.bool = (fun uu___347_9410 -> (match (uu___347_9410) with
| (uu____9419, uu____9420, []) -> begin
true
end
| uu____9423 -> begin
false
end))


let quasi_pattern : FStar_TypeChecker_Env.env  ->  flex_t  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ) FStar_Pervasives_Native.option = (fun env f -> (

let uu____9454 = f
in (match (uu____9454) with
| (uu____9461, {FStar_Syntax_Syntax.ctx_uvar_head = uu____9462; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9463; FStar_Syntax_Syntax.ctx_uvar_binders = ctx; FStar_Syntax_Syntax.ctx_uvar_typ = t_hd; FStar_Syntax_Syntax.ctx_uvar_reason = uu____9466; FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9467; FStar_Syntax_Syntax.ctx_uvar_range = uu____9468}, args) -> begin
(

let name_exists_in = (fun x bs -> (FStar_Util.for_some (fun uu____9528 -> (match (uu____9528) with
| (y, uu____9536) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end)) bs))
in (

let rec aux = (fun pat_binders formals t_res args1 -> (match (((formals), (args1))) with
| ([], []) -> begin
(

let uu____9690 = (

let uu____9705 = (

let uu____9708 = (FStar_Syntax_Syntax.mk_Total t_res)
in (FStar_Syntax_Util.arrow formals uu____9708))
in (((FStar_List.rev pat_binders)), (uu____9705)))
in FStar_Pervasives_Native.Some (uu____9690))
end
| (uu____9741, []) -> begin
(

let uu____9772 = (

let uu____9787 = (

let uu____9790 = (FStar_Syntax_Syntax.mk_Total t_res)
in (FStar_Syntax_Util.arrow formals uu____9790))
in (((FStar_List.rev pat_binders)), (uu____9787)))
in FStar_Pervasives_Native.Some (uu____9772))
end
| (((formal, formal_imp))::formals1, ((a, a_imp))::args2) -> begin
(

let uu____9881 = (

let uu____9882 = (FStar_Syntax_Subst.compress a)
in uu____9882.FStar_Syntax_Syntax.n)
in (match (uu____9881) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____9902 = ((name_exists_in x ctx) || (name_exists_in x pat_binders))
in (match (uu____9902) with
| true -> begin
(aux ((((formal), (formal_imp)))::pat_binders) formals1 t_res args2)
end
| uu____9927 -> begin
(

let x1 = (

let uu___371_9929 = x
in {FStar_Syntax_Syntax.ppname = uu___371_9929.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___371_9929.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = formal.FStar_Syntax_Syntax.sort})
in (

let subst1 = (

let uu____9933 = (

let uu____9934 = (

let uu____9941 = (FStar_Syntax_Syntax.bv_to_name x1)
in ((formal), (uu____9941)))
in FStar_Syntax_Syntax.NT (uu____9934))
in (uu____9933)::[])
in (

let formals2 = (FStar_Syntax_Subst.subst_binders subst1 formals1)
in (

let t_res1 = (FStar_Syntax_Subst.subst subst1 t_res)
in (aux (((((

let uu___372_9957 = x1
in {FStar_Syntax_Syntax.ppname = uu___372_9957.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___372_9957.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = formal.FStar_Syntax_Syntax.sort})), (a_imp)))::pat_binders) formals2 t_res1 args2)))))
end))
end
| uu____9958 -> begin
(aux ((((formal), (formal_imp)))::pat_binders) formals1 t_res args2)
end))
end
| ([], args2) -> begin
(

let uu____9998 = (

let uu____10013 = (FStar_TypeChecker_Normalize.unfold_whnf env t_res)
in (FStar_Syntax_Util.arrow_formals uu____10013))
in (match (uu____9998) with
| (more_formals, t_res1) -> begin
(match (more_formals) with
| [] -> begin
FStar_Pervasives_Native.None
end
| uu____10088 -> begin
(aux pat_binders more_formals t_res1 args2)
end)
end))
end))
in (match (args) with
| [] -> begin
FStar_Pervasives_Native.Some ((([]), (t_hd)))
end
| uu____10121 -> begin
(

let uu____10122 = (FStar_Syntax_Util.arrow_formals t_hd)
in (match (uu____10122) with
| (formals, t_res) -> begin
(aux [] formals t_res args)
end))
end)))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____10441 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10441) with
| true -> begin
(

let uu____10442 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" uu____10442))
end
| uu____10443 -> begin
()
end));
(

let uu____10444 = (next_prob probs)
in (match (uu____10444) with
| FStar_Pervasives_Native.Some (hd1, tl1, rank1) -> begin
(

let probs1 = (

let uu___373_10471 = probs
in {attempting = tl1; wl_deferred = uu___373_10471.wl_deferred; ctr = uu___373_10471.ctr; defer_ok = uu___373_10471.defer_ok; smt_ok = uu___373_10471.smt_ok; umax_heuristic_ok = uu___373_10471.umax_heuristic_ok; tcenv = uu___373_10471.tcenv; wl_implicits = uu___373_10471.wl_implicits})
in ((def_check_prob "solve,hd" hd1);
(match (hd1) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs1)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____10479 = (FStar_Util.physical_equality tp.FStar_TypeChecker_Common.lhs tp.FStar_TypeChecker_Common.rhs)
in (match (uu____10479) with
| true -> begin
(

let uu____10480 = (solve_prob hd1 FStar_Pervasives_Native.None [] probs1)
in (solve env uu____10480))
end
| uu____10481 -> begin
(match (((Prims.op_Equality rank1 FStar_TypeChecker_Common.Rigid_rigid) || ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) && (Prims.op_disEquality rank1 FStar_TypeChecker_Common.Flex_flex)))) with
| true -> begin
(solve_t' env tp probs1)
end
| uu____10482 -> begin
(match (probs1.defer_ok) with
| true -> begin
(solve env (defer "deferring flex_rigid or flex_flex subtyping" hd1 probs1))
end
| uu____10483 -> begin
(match ((Prims.op_Equality rank1 FStar_TypeChecker_Common.Flex_flex)) with
| true -> begin
(solve_t' env (

let uu___374_10485 = tp
in {FStar_TypeChecker_Common.pid = uu___374_10485.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___374_10485.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___374_10485.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___374_10485.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___374_10485.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___374_10485.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___374_10485.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___374_10485.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___374_10485.FStar_TypeChecker_Common.rank}) probs1)
end
| uu____10488 -> begin
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
| uu____10507 -> begin
(

let uu____10516 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____10575 -> (match (uu____10575) with
| (c, uu____10583, uu____10584) -> begin
(c < probs.ctr)
end))))
in (match (uu____10516) with
| (attempt1, rest) -> begin
(match (attempt1) with
| [] -> begin
(

let uu____10625 = (

let uu____10630 = (FStar_List.map (fun uu____10645 -> (match (uu____10645) with
| (uu____10656, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in ((uu____10630), (probs.wl_implicits)))
in Success (uu____10625))
end
| uu____10659 -> begin
(

let uu____10668 = (

let uu___375_10669 = probs
in (

let uu____10670 = (FStar_All.pipe_right attempt1 (FStar_List.map (fun uu____10689 -> (match (uu____10689) with
| (uu____10696, uu____10697, y) -> begin
y
end))))
in {attempting = uu____10670; wl_deferred = rest; ctr = uu___375_10669.ctr; defer_ok = uu___375_10669.defer_ok; smt_ok = uu___375_10669.smt_ok; umax_heuristic_ok = uu___375_10669.umax_heuristic_ok; tcenv = uu___375_10669.tcenv; wl_implicits = uu___375_10669.wl_implicits}))
in (solve env uu____10668))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____10704 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____10704) with
| USolved (wl1) -> begin
(

let uu____10706 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____10706))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl1) -> begin
(solve env (defer "" orig wl1))
end)))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (

let rec aux = (fun wl1 us1 us2 -> (match (((us1), (us2))) with
| ([], []) -> begin
USolved (wl1)
end
| ((u1)::us11, (u2)::us21) -> begin
(

let uu____10758 = (solve_universe_eq (p_pid orig) wl1 u1 u2)
in (match (uu____10758) with
| USolved (wl2) -> begin
(aux wl2 us11 us21)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____10761 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t11 = (whnf env t1)
in (

let t21 = (whnf env t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.pos = uu____10773; FStar_Syntax_Syntax.vars = uu____10774}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.pos = uu____10777; FStar_Syntax_Syntax.vars = uu____10778}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____10790), uu____10791) -> begin
(failwith "Impossible: expect head symbols to match")
end
| (uu____10798, FStar_Syntax_Syntax.Tm_uinst (uu____10799)) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____10806 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____10816 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10816) with
| true -> begin
(

let uu____10817 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" uu____10817 msg))
end
| uu____10818 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____10819 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_or_flex_rigid_subtyping : FStar_TypeChecker_Common.rank_t  ->  FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun rank1 env tp wl -> ((def_check_prob "solve_rigid_flex_or_flex_rigid_subtyping" (FStar_TypeChecker_Common.TProb (tp)));
(

let flip = (Prims.op_Equality rank1 FStar_TypeChecker_Common.Flex_rigid)
in (

let meet_or_join = (fun op ts env1 wl1 -> (

let eq_prob = (fun t1 t2 wl2 -> (

let uu____10903 = (new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos "join/meet refinements")
in (match (uu____10903) with
| (p, wl3) -> begin
((def_check_prob "meet_or_join" (FStar_TypeChecker_Common.TProb (p)));
((FStar_TypeChecker_Common.TProb (p)), (wl3));
)
end)))
in (

let pairwise = (fun t1 t2 wl2 -> ((

let uu____10956 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____10956) with
| true -> begin
(

let uu____10957 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10958 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n" uu____10957 uu____10958)))
end
| uu____10959 -> begin
()
end));
(

let uu____10960 = (head_matches_delta env1 wl2 t1 t2)
in (match (uu____10960) with
| (mr, ts1) -> begin
(match (mr) with
| HeadMatch (true) -> begin
(

let uu____11005 = (eq_prob t1 t2 wl2)
in (match (uu____11005) with
| (p, wl3) -> begin
((t1), ((p)::[]), (wl3))
end))
end
| MisMatch (uu____11026) -> begin
(

let uu____11035 = (eq_prob t1 t2 wl2)
in (match (uu____11035) with
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

let uu____11084 = (match (ts1) with
| FStar_Pervasives_Native.Some (t11, t21) -> begin
(

let uu____11099 = (FStar_Syntax_Subst.compress t11)
in (

let uu____11100 = (FStar_Syntax_Subst.compress t21)
in ((uu____11099), (uu____11100))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____11105 = (FStar_Syntax_Subst.compress t1)
in (

let uu____11106 = (FStar_Syntax_Subst.compress t2)
in ((uu____11105), (uu____11106))))
end)
in (match (uu____11084) with
| (t11, t21) -> begin
(

let try_eq = (fun t12 t22 wl3 -> (

let uu____11137 = (FStar_Syntax_Util.head_and_args t12)
in (match (uu____11137) with
| (t1_hd, t1_args) -> begin
(

let uu____11182 = (FStar_Syntax_Util.head_and_args t22)
in (match (uu____11182) with
| (t2_hd, t2_args) -> begin
(match ((Prims.op_disEquality (FStar_List.length t1_args) (FStar_List.length t2_args))) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____11245 -> begin
(

let uu____11246 = (

let uu____11253 = (

let uu____11264 = (FStar_Syntax_Syntax.as_arg t1_hd)
in (uu____11264)::t1_args)
in (

let uu____11281 = (

let uu____11290 = (FStar_Syntax_Syntax.as_arg t2_hd)
in (uu____11290)::t2_args)
in (FStar_List.fold_left2 (fun uu____11339 uu____11340 uu____11341 -> (match (((uu____11339), (uu____11340), (uu____11341))) with
| ((probs, wl4), (a1, uu____11391), (a2, uu____11393)) -> begin
(

let uu____11430 = (eq_prob a1 a2 wl4)
in (match (uu____11430) with
| (p, wl5) -> begin
(((p)::probs), (wl5))
end))
end)) (([]), (wl3)) uu____11253 uu____11281)))
in (match (uu____11246) with
| (probs, wl4) -> begin
(

let wl' = (

let uu___376_11456 = wl4
in {attempting = probs; wl_deferred = []; ctr = uu___376_11456.ctr; defer_ok = false; smt_ok = false; umax_heuristic_ok = uu___376_11456.umax_heuristic_ok; tcenv = uu___376_11456.tcenv; wl_implicits = []})
in (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____11464 = (solve env1 wl')
in (match (uu____11464) with
| Success (uu____11467, imps) -> begin
((FStar_Syntax_Unionfind.commit tx);
FStar_Pervasives_Native.Some ((

let uu___377_11471 = wl4
in {attempting = uu___377_11471.attempting; wl_deferred = uu___377_11471.wl_deferred; ctr = uu___377_11471.ctr; defer_ok = uu___377_11471.defer_ok; smt_ok = uu___377_11471.smt_ok; umax_heuristic_ok = uu___377_11471.umax_heuristic_ok; tcenv = uu___377_11471.tcenv; wl_implicits = (FStar_List.append wl4.wl_implicits imps)}));
)
end
| Failed (uu____11472) -> begin
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

let uu____11504 = (base_and_refinement_maybe_delta false env1 t12)
in (match (uu____11504) with
| (t1_base, p1_opt) -> begin
(

let uu____11539 = (base_and_refinement_maybe_delta false env1 t22)
in (match (uu____11539) with
| (t2_base, p2_opt) -> begin
(

let combine_refinements = (fun t_base p1_opt1 p2_opt1 -> (

let refine1 = (fun x t -> (

let uu____11637 = (FStar_Syntax_Util.is_t_true t)
in (match (uu____11637) with
| true -> begin
x.FStar_Syntax_Syntax.sort
end
| uu____11640 -> begin
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

let uu____11685 = (op phi11 phi21)
in (refine1 x1 uu____11685))))))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (x, phi)) -> begin
(

let x1 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let subst1 = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x1))))::[]
in (

let phi1 = (FStar_Syntax_Subst.subst subst1 phi)
in (

let uu____11715 = (op FStar_Syntax_Util.t_true phi1)
in (refine1 x1 uu____11715)))))
end
| (FStar_Pervasives_Native.Some (x, phi), FStar_Pervasives_Native.None) -> begin
(

let x1 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let subst1 = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x1))))::[]
in (

let phi1 = (FStar_Syntax_Subst.subst subst1 phi)
in (

let uu____11745 = (op FStar_Syntax_Util.t_true phi1)
in (refine1 x1 uu____11745)))))
end
| uu____11748 -> begin
t_base
end)))
in (

let uu____11765 = (try_eq t1_base t2_base wl3)
in (match (uu____11765) with
| FStar_Pervasives_Native.Some (wl4) -> begin
(

let uu____11779 = (combine_refinements t1_base p1_opt p2_opt)
in ((uu____11779), ([]), (wl4)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____11786 = (base_and_refinement_maybe_delta true env1 t12)
in (match (uu____11786) with
| (t1_base1, p1_opt1) -> begin
(

let uu____11821 = (base_and_refinement_maybe_delta true env1 t22)
in (match (uu____11821) with
| (t2_base1, p2_opt1) -> begin
(

let uu____11856 = (eq_prob t1_base1 t2_base1 wl3)
in (match (uu____11856) with
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

let uu____11880 = (combine t11 t21 wl2)
in (match (uu____11880) with
| (t12, ps, wl3) -> begin
((

let uu____11913 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____11913) with
| true -> begin
(

let uu____11914 = (FStar_Syntax_Print.term_to_string t12)
in (FStar_Util.print1 "pairwise fallback2 succeeded: %s" uu____11914))
end
| uu____11915 -> begin
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

let rec aux = (fun uu____11953 ts1 -> (match (uu____11953) with
| (out, probs, wl2) -> begin
(match (ts1) with
| [] -> begin
((out), (probs), (wl2))
end
| (t)::ts2 -> begin
(

let uu____12016 = (pairwise out t wl2)
in (match (uu____12016) with
| (out1, probs', wl3) -> begin
(aux ((out1), ((FStar_List.append probs probs')), (wl3)) ts2)
end))
end)
end))
in (

let uu____12052 = (

let uu____12063 = (FStar_List.hd ts)
in ((uu____12063), ([]), (wl1)))
in (

let uu____12072 = (FStar_List.tl ts)
in (aux uu____12052 uu____12072)))))))
in (

let uu____12079 = (match (flip) with
| true -> begin
((tp.FStar_TypeChecker_Common.lhs), (tp.FStar_TypeChecker_Common.rhs))
end
| uu____12094 -> begin
((tp.FStar_TypeChecker_Common.rhs), (tp.FStar_TypeChecker_Common.lhs))
end)
in (match (uu____12079) with
| (this_flex, this_rigid) -> begin
(

let uu____12103 = (

let uu____12104 = (FStar_Syntax_Subst.compress this_rigid)
in uu____12104.FStar_Syntax_Syntax.n)
in (match (uu____12103) with
| FStar_Syntax_Syntax.Tm_arrow (_bs, comp) -> begin
(

let uu____12129 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____12129) with
| true -> begin
(

let uu____12130 = (destruct_flex_t this_flex wl)
in (match (uu____12130) with
| (flex, wl1) -> begin
(

let uu____12137 = (quasi_pattern env flex)
in (match (uu____12137) with
| FStar_Pervasives_Native.None -> begin
(giveup env "flex-arrow subtyping, not a quasi pattern" (FStar_TypeChecker_Common.TProb (tp)))
end
| FStar_Pervasives_Native.Some (flex_bs, flex_t) -> begin
((

let uu____12155 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12155) with
| true -> begin
(

let uu____12156 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by imitating arrow:%s\n" uu____12156))
end
| uu____12157 -> begin
()
end));
(imitate_arrow (FStar_TypeChecker_Common.TProb (tp)) env wl1 flex flex_bs flex_t tp.FStar_TypeChecker_Common.relation this_rigid);
)
end))
end))
end
| uu____12158 -> begin
(

let uu____12159 = (attempt ((FStar_TypeChecker_Common.TProb ((

let uu___378_12162 = tp
in {FStar_TypeChecker_Common.pid = uu___378_12162.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___378_12162.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___378_12162.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___378_12162.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___378_12162.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___378_12162.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___378_12162.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___378_12162.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___378_12162.FStar_TypeChecker_Common.rank})))::[]) wl)
in (solve env uu____12159))
end))
end
| uu____12163 -> begin
((

let uu____12165 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12165) with
| true -> begin
(

let uu____12166 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" uu____12166))
end
| uu____12167 -> begin
()
end));
(

let uu____12168 = (FStar_Syntax_Util.head_and_args this_flex)
in (match (uu____12168) with
| (u, _args) -> begin
(

let uu____12211 = (

let uu____12212 = (FStar_Syntax_Subst.compress u)
in uu____12212.FStar_Syntax_Syntax.n)
in (match (uu____12211) with
| FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, _subst) -> begin
(

let equiv1 = (fun t -> (

let uu____12239 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____12239) with
| (u', uu____12257) -> begin
(

let uu____12282 = (

let uu____12283 = (whnf env u')
in uu____12283.FStar_Syntax_Syntax.n)
in (match (uu____12282) with
| FStar_Syntax_Syntax.Tm_uvar (ctx_uvar', _subst') -> begin
(FStar_Syntax_Unionfind.equiv ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head)
end
| uu____12304 -> begin
false
end))
end)))
in (

let uu____12305 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___348_12328 -> (match (uu___348_12328) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(

let tp2 = (maybe_invert tp1)
in (match (tp2.FStar_TypeChecker_Common.rank) with
| FStar_Pervasives_Native.Some (rank') when (Prims.op_Equality rank1 rank') -> begin
(match (flip) with
| true -> begin
(equiv1 tp2.FStar_TypeChecker_Common.lhs)
end
| uu____12336 -> begin
(equiv1 tp2.FStar_TypeChecker_Common.rhs)
end)
end
| uu____12337 -> begin
false
end))
end
| uu____12340 -> begin
false
end))))
in (match (uu____12305) with
| (bounds_probs, rest) -> begin
(

let bounds_typs = (

let uu____12354 = (whnf env this_rigid)
in (

let uu____12355 = (FStar_List.collect (fun uu___349_12361 -> (match (uu___349_12361) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____12367 = (match (flip) with
| true -> begin
(whnf env (maybe_invert p).FStar_TypeChecker_Common.rhs)
end
| uu____12368 -> begin
(whnf env (maybe_invert p).FStar_TypeChecker_Common.lhs)
end)
in (uu____12367)::[])
end
| uu____12369 -> begin
[]
end)) bounds_probs)
in (uu____12354)::uu____12355))
in (

let uu____12370 = (meet_or_join (match (flip) with
| true -> begin
FStar_Syntax_Util.mk_conj_simp
end
| uu____12389 -> begin
FStar_Syntax_Util.mk_disj_simp
end) bounds_typs env wl)
in (match (uu____12370) with
| (bound, sub_probs, wl1) -> begin
(

let uu____12401 = (

let flex_u = (flex_uvar_head this_flex)
in (

let bound1 = (

let uu____12416 = (

let uu____12417 = (FStar_Syntax_Subst.compress bound)
in uu____12417.FStar_Syntax_Syntax.n)
in (match (uu____12416) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) when ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB) && (

let uu____12429 = (occurs flex_u x.FStar_Syntax_Syntax.sort)
in (FStar_Pervasives_Native.snd uu____12429))) -> begin
x.FStar_Syntax_Syntax.sort
end
| uu____12438 -> begin
bound
end))
in (

let uu____12439 = (new_problem wl1 env bound1 FStar_TypeChecker_Common.EQ this_flex FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc (match (flip) with
| true -> begin
"joining refinements"
end
| uu____12446 -> begin
"meeting refinements"
end))
in ((bound1), (uu____12439)))))
in (match (uu____12401) with
| (bound_typ, (eq_prob, wl')) -> begin
((def_check_prob "meet_or_join2" (FStar_TypeChecker_Common.TProb (eq_prob)));
(

let uu____12468 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12468) with
| true -> begin
(

let wl'1 = (

let uu___379_12470 = wl1
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___379_12470.wl_deferred; ctr = uu___379_12470.ctr; defer_ok = uu___379_12470.defer_ok; smt_ok = uu___379_12470.smt_ok; umax_heuristic_ok = uu___379_12470.umax_heuristic_ok; tcenv = uu___379_12470.tcenv; wl_implicits = uu___379_12470.wl_implicits})
in (

let uu____12471 = (wl_to_string wl'1)
in (FStar_Util.print1 "After meet/join refinements: %s\n" uu____12471)))
end
| uu____12472 -> begin
()
end));
(

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____12474 = (solve_t env eq_prob (

let uu___380_12476 = wl'
in {attempting = sub_probs; wl_deferred = uu___380_12476.wl_deferred; ctr = uu___380_12476.ctr; defer_ok = false; smt_ok = uu___380_12476.smt_ok; umax_heuristic_ok = uu___380_12476.umax_heuristic_ok; tcenv = uu___380_12476.tcenv; wl_implicits = uu___380_12476.wl_implicits}))
in (match (uu____12474) with
| Success (uu____12477) -> begin
(

let wl2 = (

let uu___381_12483 = wl'
in {attempting = rest; wl_deferred = uu___381_12483.wl_deferred; ctr = uu___381_12483.ctr; defer_ok = uu___381_12483.defer_ok; smt_ok = uu___381_12483.smt_ok; umax_heuristic_ok = uu___381_12483.umax_heuristic_ok; tcenv = uu___381_12483.tcenv; wl_implicits = uu___381_12483.wl_implicits})
in (

let g = (FStar_List.fold_left (fun g p -> (FStar_Syntax_Util.mk_conj g (p_guard p))) eq_prob.FStar_TypeChecker_Common.logical_guard sub_probs)
in (

let wl3 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) (FStar_Pervasives_Native.Some (g)) [] wl2)
in (

let uu____12498 = (FStar_List.fold_left (fun wl4 p -> (solve_prob' true p FStar_Pervasives_Native.None [] wl4)) wl3 bounds_probs)
in ((FStar_Syntax_Unionfind.commit tx);
(solve env wl3);
)))))
end
| Failed (p, msg) -> begin
((

let uu____12509 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12509) with
| true -> begin
(

let uu____12510 = (

let uu____12511 = (FStar_List.map (prob_to_string env) ((FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs))
in (FStar_All.pipe_right uu____12511 (FStar_String.concat "\n")))
in (FStar_Util.print1 "meet/join attempted and failed to solve problems:\n%s\n" uu____12510))
end
| uu____12516 -> begin
()
end));
(

let uu____12517 = (

let uu____12532 = (base_and_refinement env bound_typ)
in ((rank1), (uu____12532)))
in (match (uu____12517) with
| (FStar_TypeChecker_Common.Rigid_flex, (t_base, FStar_Pervasives_Native.Some (uu____12554))) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(

let uu____12580 = (new_problem wl1 env t_base FStar_TypeChecker_Common.EQ this_flex FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "widened subtyping")
in (match (uu____12580) with
| (eq_prob1, wl2) -> begin
((def_check_prob "meet_or_join3" (FStar_TypeChecker_Common.TProb (eq_prob1)));
(

let wl3 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) (FStar_Pervasives_Native.Some ((p_guard (FStar_TypeChecker_Common.TProb (eq_prob1))))) [] wl2)
in (

let uu____12597 = (attempt ((FStar_TypeChecker_Common.TProb (eq_prob1))::[]) wl3)
in (solve env uu____12597)));
)
end));
)
end
| (FStar_TypeChecker_Common.Flex_rigid, (t_base, FStar_Pervasives_Native.Some (x, phi))) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(

let uu____12622 = (new_problem wl1 env t_base FStar_TypeChecker_Common.EQ this_flex FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "widened subtyping")
in (match (uu____12622) with
| (eq_prob1, wl2) -> begin
((def_check_prob "meet_or_join4" (FStar_TypeChecker_Common.TProb (eq_prob1)));
(

let phi1 = (guard_on_element wl2 tp x phi)
in (

let wl3 = (

let uu____12640 = (

let uu____12645 = (FStar_Syntax_Util.mk_conj phi1 (p_guard (FStar_TypeChecker_Common.TProb (eq_prob1))))
in FStar_Pervasives_Native.Some (uu____12645))
in (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) uu____12640 [] wl2))
in (

let uu____12650 = (attempt ((FStar_TypeChecker_Common.TProb (eq_prob1))::[]) wl3)
in (solve env uu____12650))));
)
end));
)
end
| uu____12651 -> begin
(giveup env (Prims.strcat "failed to solve sub-problems: " msg) p)
end));
)
end)));
)
end))
end)))
end)))
end
| uu____12666 when flip -> begin
(

let uu____12667 = (

let uu____12668 = (FStar_Util.string_of_int (rank_t_num rank1))
in (

let uu____12669 = (prob_to_string env (FStar_TypeChecker_Common.TProb (tp)))
in (FStar_Util.format2 "Impossible: (rank=%s) Not a flex-rigid: %s" uu____12668 uu____12669)))
in (failwith uu____12667))
end
| uu____12670 -> begin
(

let uu____12671 = (

let uu____12672 = (FStar_Util.string_of_int (rank_t_num rank1))
in (

let uu____12673 = (prob_to_string env (FStar_TypeChecker_Common.TProb (tp)))
in (FStar_Util.format2 "Impossible: (rank=%s) Not a rigid-flex: %s" uu____12672 uu____12673)))
in (failwith uu____12671))
end))
end));
)
end))
end))));
))
and imitate_arrow : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Env.env  ->  worklist  ->  flex_t  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  solution = (fun orig env wl lhs bs_lhs t_res_lhs rel arrow1 -> (

let bs_lhs_args = (FStar_List.map (fun uu____12707 -> (match (uu____12707) with
| (x, i) -> begin
(

let uu____12726 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____12726), (i)))
end)) bs_lhs)
in (

let uu____12729 = lhs
in (match (uu____12729) with
| (uu____12730, u_lhs, uu____12732) -> begin
(

let imitate_comp = (fun bs bs_terms c wl1 -> (

let imitate_tot_or_gtot = (fun t uopt f wl2 -> (

let uu____12829 = (match (uopt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Util.type_u ())
end
| FStar_Pervasives_Native.Some (univ) -> begin
(

let uu____12839 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (univ)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in ((uu____12839), (univ)))
end)
in (match (uu____12829) with
| (k, univ) -> begin
(

let uu____12846 = (copy_uvar u_lhs (FStar_List.append bs_lhs bs) k wl2)
in (match (uu____12846) with
| (uu____12863, u, wl3) -> begin
(

let uu____12866 = (f u (FStar_Pervasives_Native.Some (univ)))
in ((uu____12866), (wl3)))
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

let uu____12892 = (

let uu____12905 = (

let uu____12916 = (FStar_Syntax_Syntax.as_arg ct.FStar_Syntax_Syntax.result_typ)
in (uu____12916)::ct.FStar_Syntax_Syntax.effect_args)
in (FStar_List.fold_right (fun uu____12967 uu____12968 -> (match (((uu____12967), (uu____12968))) with
| ((a, i), (out_args, wl2)) -> begin
(

let uu____13069 = (

let uu____13076 = (

let uu____13079 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____13079))
in (copy_uvar u_lhs [] uu____13076 wl2))
in (match (uu____13069) with
| (uu____13108, t_a, wl3) -> begin
(

let uu____13111 = (copy_uvar u_lhs bs t_a wl3)
in (match (uu____13111) with
| (uu____13130, a', wl4) -> begin
(((((a'), (i)))::out_args), (wl4))
end))
end))
end)) uu____12905 (([]), (wl1))))
in (match (uu____12892) with
| (out_args, wl2) -> begin
(

let ct' = (

let uu___382_13186 = ct
in (

let uu____13187 = (

let uu____13190 = (FStar_List.hd out_args)
in (FStar_Pervasives_Native.fst uu____13190))
in (

let uu____13205 = (FStar_List.tl out_args)
in {FStar_Syntax_Syntax.comp_univs = uu___382_13186.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___382_13186.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____13187; FStar_Syntax_Syntax.effect_args = uu____13205; FStar_Syntax_Syntax.flags = uu___382_13186.FStar_Syntax_Syntax.flags})))
in (((

let uu___383_13223 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct'); FStar_Syntax_Syntax.pos = uu___383_13223.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___383_13223.FStar_Syntax_Syntax.vars})), (wl2)))
end))
end)))
in (

let uu____13226 = (FStar_Syntax_Util.arrow_formals_comp arrow1)
in (match (uu____13226) with
| (formals, c) -> begin
(

let rec aux = (fun bs bs_terms formals1 wl1 -> (match (formals1) with
| [] -> begin
(

let uu____13288 = (imitate_comp bs bs_terms c wl1)
in (match (uu____13288) with
| (c', wl2) -> begin
(

let lhs' = (FStar_Syntax_Util.arrow bs c')
in (

let sol = (

let uu____13299 = (

let uu____13304 = (FStar_Syntax_Util.abs bs_lhs lhs' (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot t_res_lhs))))
in ((u_lhs), (uu____13304)))
in TERM (uu____13299))
in (

let uu____13305 = (mk_t_problem wl2 [] orig lhs' rel arrow1 FStar_Pervasives_Native.None "arrow imitation")
in (match (uu____13305) with
| (sub_prob, wl3) -> begin
(

let uu____13318 = (

let uu____13319 = (solve_prob orig FStar_Pervasives_Native.None ((sol)::[]) wl3)
in (attempt ((sub_prob)::[]) uu____13319))
in (solve env uu____13318))
end))))
end))
end
| ((x, imp))::formals2 -> begin
(

let uu____13341 = (

let uu____13348 = (

let uu____13351 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____13351 FStar_Pervasives_Native.fst))
in (copy_uvar u_lhs (FStar_List.append bs_lhs bs) uu____13348 wl1))
in (match (uu____13341) with
| (_ctx_u_x, u_x, wl2) -> begin
(

let y = (

let uu____13372 = (

let uu____13375 = (FStar_Syntax_Syntax.range_of_bv x)
in FStar_Pervasives_Native.Some (uu____13375))
in (FStar_Syntax_Syntax.new_bv uu____13372 u_x))
in (

let uu____13376 = (

let uu____13379 = (

let uu____13382 = (

let uu____13383 = (FStar_Syntax_Syntax.bv_to_name y)
in ((uu____13383), (imp)))
in (uu____13382)::[])
in (FStar_List.append bs_terms uu____13379))
in (aux (FStar_List.append bs ((((y), (imp)))::[])) uu____13376 formals2 wl2)))
end))
end))
in (

let uu____13410 = (occurs_check u_lhs arrow1)
in (match (uu____13410) with
| (uu____13421, occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____13432 = (

let uu____13433 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____13433))
in (giveup_or_defer env orig wl uu____13432))
end
| uu____13434 -> begin
(aux [] [] formals wl)
end)
end)))
end)))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (worklist  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  (FStar_TypeChecker_Common.prob * worklist))  ->  solution = (fun env bs1 bs2 orig wl rhs -> ((

let uu____13462 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____13462) with
| true -> begin
(

let uu____13463 = (FStar_Syntax_Print.binders_to_string ", " bs1)
in (

let uu____13464 = (FStar_Syntax_Print.binders_to_string ", " bs2)
in (FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n" uu____13463 (rel_to_string (p_rel orig)) uu____13464)))
end
| uu____13465 -> begin
()
end));
(

let rec aux = (fun wl1 scope env1 subst1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
(

let uu____13585 = (rhs wl1 scope env1 subst1)
in (match (uu____13585) with
| (rhs_prob, wl2) -> begin
((

let uu____13605 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____13605) with
| true -> begin
(

let uu____13606 = (prob_to_string env1 rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" uu____13606))
end
| uu____13607 -> begin
()
end));
(

let formula = (p_guard rhs_prob)
in ((FStar_Util.Inl ((((rhs_prob)::[]), (formula)))), (wl2)));
)
end))
end
| (((hd1, imp))::xs1, ((hd2, imp'))::ys1) when (

let uu____13679 = (FStar_Syntax_Util.eq_aqual imp imp')
in (Prims.op_Equality uu____13679 FStar_Syntax_Util.Equal)) -> begin
(

let hd11 = (

let uu___384_13681 = hd1
in (

let uu____13682 = (FStar_Syntax_Subst.subst subst1 hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___384_13681.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___384_13681.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____13682}))
in (

let hd21 = (

let uu___385_13686 = hd2
in (

let uu____13687 = (FStar_Syntax_Subst.subst subst1 hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___385_13686.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___385_13686.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____13687}))
in (

let uu____13690 = (

let uu____13695 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_t_problem wl1 scope orig hd11.FStar_Syntax_Syntax.sort uu____13695 hd21.FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None "Formal parameter"))
in (match (uu____13690) with
| (prob, wl2) -> begin
(

let hd12 = (FStar_Syntax_Syntax.freshen_bv hd11)
in (

let subst2 = (

let uu____13714 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd12))))::uu____13714)
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 hd12)
in (

let uu____13718 = (aux wl2 (FStar_List.append scope ((((hd12), (imp)))::[])) env2 subst2 xs1 ys1)
in (match (uu____13718) with
| (FStar_Util.Inl (sub_probs, phi), wl3) -> begin
(

let phi1 = (

let uu____13781 = (FStar_TypeChecker_Env.close_forall env2 ((((hd12), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj (p_guard prob) uu____13781))
in ((

let uu____13799 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____13799) with
| true -> begin
(

let uu____13800 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____13801 = (FStar_Syntax_Print.bv_to_string hd12)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" uu____13800 uu____13801)))
end
| uu____13802 -> begin
()
end));
((FStar_Util.Inl ((((prob)::sub_probs), (phi1)))), (wl3));
))
end
| fail1 -> begin
fail1
end)))))
end))))
end
| uu____13828 -> begin
((FStar_Util.Inr ("arity or argument-qualifier mismatch")), (wl1))
end))
in (

let uu____13861 = (aux wl [] env [] bs1 bs2)
in (match (uu____13861) with
| (FStar_Util.Inr (msg), wl1) -> begin
(giveup env msg orig)
end
| (FStar_Util.Inl (sub_probs, phi), wl1) -> begin
(

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some (phi)) [] wl1)
in (

let uu____13910 = (attempt sub_probs wl2)
in (solve env uu____13910)))
end)));
))
and try_solve_without_smt_or_else : FStar_TypeChecker_Env.env  ->  worklist  ->  (FStar_TypeChecker_Env.env  ->  worklist  ->  solution)  ->  (FStar_TypeChecker_Env.env  ->  worklist  ->  (FStar_TypeChecker_Common.prob * Prims.string)  ->  solution)  ->  solution = (fun env wl try_solve else_solve -> (

let wl' = (

let uu___386_13930 = wl
in {attempting = []; wl_deferred = []; ctr = uu___386_13930.ctr; defer_ok = false; smt_ok = false; umax_heuristic_ok = false; tcenv = uu___386_13930.tcenv; wl_implicits = []})
in (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____13938 = (try_solve env wl')
in (match (uu____13938) with
| Success (uu____13939, imps) -> begin
((FStar_Syntax_Unionfind.commit tx);
(

let wl1 = (

let uu___387_13943 = wl
in {attempting = uu___387_13943.attempting; wl_deferred = uu___387_13943.wl_deferred; ctr = uu___387_13943.ctr; defer_ok = uu___387_13943.defer_ok; smt_ok = uu___387_13943.smt_ok; umax_heuristic_ok = uu___387_13943.umax_heuristic_ok; tcenv = uu___387_13943.tcenv; wl_implicits = (FStar_List.append wl.wl_implicits imps)})
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

let uu____13951 = (compress_tprob wl.tcenv problem)
in (solve_t' env uu____13951 wl));
))
and solve_t_flex_rigid_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  flex_t  ->  FStar_Syntax_Syntax.term  ->  solution = (fun env orig wl lhs rhs -> (

let binders_as_bv_set = (fun bs -> (

let uu____13965 = (FStar_List.map FStar_Pervasives_Native.fst bs)
in (FStar_Util.as_set uu____13965 FStar_Syntax_Syntax.order_bv)))
in (

let mk_solution = (fun env1 lhs1 bs rhs1 -> (

let uu____13999 = lhs1
in (match (uu____13999) with
| (uu____14002, ctx_u, uu____14004) -> begin
(

let sol = (match (bs) with
| [] -> begin
rhs1
end
| uu____14012 -> begin
(

let uu____14013 = (sn_binders env1 bs)
in (u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ uu____14013 rhs1))
end)
in (TERM (((ctx_u), (sol))))::[])
end)))
in (

let try_quasi_pattern = (fun orig1 env1 wl1 lhs1 rhs1 -> (

let uu____14060 = (quasi_pattern env1 lhs1)
in (match (uu____14060) with
| FStar_Pervasives_Native.None -> begin
((FStar_Util.Inl ("Not a quasi-pattern")), (wl1))
end
| FStar_Pervasives_Native.Some (bs, uu____14090) -> begin
(

let uu____14095 = lhs1
in (match (uu____14095) with
| (t_lhs, ctx_u, args) -> begin
(

let uu____14109 = (occurs_check ctx_u rhs1)
in (match (uu____14109) with
| (uvars1, occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____14151 = (

let uu____14158 = (

let uu____14159 = (FStar_Option.get msg)
in (Prims.strcat "quasi-pattern, occurs-check failed: " uu____14159))
in FStar_Util.Inl (uu____14158))
in ((uu____14151), (wl1)))
end
| uu____14168 -> begin
(

let fvs_lhs = (binders_as_bv_set (FStar_List.append ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders bs))
in (

let fvs_rhs = (FStar_Syntax_Free.names rhs1)
in (

let uu____14181 = (

let uu____14182 = (FStar_Util.set_is_subset_of fvs_rhs fvs_lhs)
in (not (uu____14182)))
in (match (uu____14181) with
| true -> begin
((FStar_Util.Inl ("quasi-pattern, free names on the RHS are not included in the LHS")), (wl1))
end
| uu____14201 -> begin
(

let uu____14202 = (

let uu____14209 = (mk_solution env1 lhs1 bs rhs1)
in FStar_Util.Inr (uu____14209))
in (

let uu____14214 = (restrict_all_uvars ctx_u uvars1 wl1)
in ((uu____14202), (uu____14214))))
end))))
end)
end))
end))
end)))
in (

let imitate_app = (fun orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 -> (

let uu____14257 = (FStar_Syntax_Util.head_and_args rhs1)
in (match (uu____14257) with
| (rhs_hd, args) -> begin
(

let uu____14300 = (FStar_Util.prefix args)
in (match (uu____14300) with
| (args_rhs, last_arg_rhs) -> begin
(

let rhs' = (FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs FStar_Pervasives_Native.None rhs1.FStar_Syntax_Syntax.pos)
in (

let uu____14372 = lhs1
in (match (uu____14372) with
| (t_lhs, u_lhs, _lhs_args) -> begin
(

let uu____14376 = (

let uu____14387 = (

let uu____14394 = (

let uu____14397 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____14397))
in (copy_uvar u_lhs [] uu____14394 wl1))
in (match (uu____14387) with
| (uu____14424, t_last_arg, wl2) -> begin
(

let uu____14427 = (

let uu____14434 = (

let uu____14435 = (

let uu____14444 = (FStar_Syntax_Syntax.null_binder t_last_arg)
in (uu____14444)::[])
in (FStar_List.append bs_lhs uu____14435))
in (copy_uvar u_lhs uu____14434 t_res_lhs wl2))
in (match (uu____14427) with
| (uu____14479, lhs', wl3) -> begin
(

let uu____14482 = (copy_uvar u_lhs bs_lhs t_last_arg wl3)
in (match (uu____14482) with
| (uu____14499, lhs'_last_arg, wl4) -> begin
((lhs'), (lhs'_last_arg), (wl4))
end))
end))
end))
in (match (uu____14376) with
| (lhs', lhs'_last_arg, wl2) -> begin
(

let sol = (

let uu____14520 = (

let uu____14521 = (

let uu____14526 = (

let uu____14527 = (

let uu____14530 = (

let uu____14535 = (

let uu____14536 = (FStar_Syntax_Syntax.as_arg lhs'_last_arg)
in (uu____14536)::[])
in (FStar_Syntax_Syntax.mk_Tm_app lhs' uu____14535))
in (uu____14530 FStar_Pervasives_Native.None t_lhs.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.abs bs_lhs uu____14527 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot t_res_lhs)))))
in ((u_lhs), (uu____14526)))
in TERM (uu____14521))
in (uu____14520)::[])
in (

let uu____14563 = (

let uu____14570 = (mk_t_problem wl2 [] orig1 lhs' FStar_TypeChecker_Common.EQ rhs' FStar_Pervasives_Native.None "first-order lhs")
in (match (uu____14570) with
| (p1, wl3) -> begin
(

let uu____14589 = (mk_t_problem wl3 [] orig1 lhs'_last_arg FStar_TypeChecker_Common.EQ (FStar_Pervasives_Native.fst last_arg_rhs) FStar_Pervasives_Native.None "first-order rhs")
in (match (uu____14589) with
| (p2, wl4) -> begin
(((p1)::(p2)::[]), (wl4))
end))
end))
in (match (uu____14563) with
| (sub_probs, wl3) -> begin
(

let uu____14620 = (

let uu____14621 = (solve_prob orig1 FStar_Pervasives_Native.None sol wl3)
in (attempt sub_probs uu____14621))
in (solve env1 uu____14620))
end)))
end))
end)))
end))
end)))
in (

let first_order = (fun orig1 env1 wl1 lhs1 rhs1 -> (

let is_app = (fun rhs2 -> (

let uu____14654 = (FStar_Syntax_Util.head_and_args rhs2)
in (match (uu____14654) with
| (uu____14671, args) -> begin
(match (args) with
| [] -> begin
false
end
| uu____14705 -> begin
true
end)
end)))
in (

let is_arrow = (fun rhs2 -> (

let uu____14722 = (

let uu____14723 = (FStar_Syntax_Subst.compress rhs2)
in uu____14723.FStar_Syntax_Syntax.n)
in (match (uu____14722) with
| FStar_Syntax_Syntax.Tm_arrow (uu____14726) -> begin
true
end
| uu____14741 -> begin
false
end)))
in (

let uu____14742 = (quasi_pattern env1 lhs1)
in (match (uu____14742) with
| FStar_Pervasives_Native.None -> begin
(

let uu____14753 = (

let uu____14754 = (prob_to_string env1 orig1)
in (FStar_Util.format1 "first_order heuristic cannot solve %s; lhs not a quasi-pattern" uu____14754))
in (giveup_or_defer env1 orig1 wl1 uu____14753))
end
| FStar_Pervasives_Native.Some (bs_lhs, t_res_lhs) -> begin
(

let uu____14761 = (is_app rhs1)
in (match (uu____14761) with
| true -> begin
(imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1)
end
| uu____14762 -> begin
(

let uu____14763 = (is_arrow rhs1)
in (match (uu____14763) with
| true -> begin
(imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs FStar_TypeChecker_Common.EQ rhs1)
end
| uu____14764 -> begin
(

let uu____14765 = (

let uu____14766 = (prob_to_string env1 orig1)
in (FStar_Util.format1 "first_order heuristic cannot solve %s; rhs not an app or arrow" uu____14766))
in (giveup_or_defer env1 orig1 wl1 uu____14765))
end))
end))
end)))))
in (match ((p_rel orig)) with
| FStar_TypeChecker_Common.SUB -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer env orig wl "flex-rigid subtyping")
end
| uu____14767 -> begin
(solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.SUBINV -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer env orig wl "flex-rigid subtyping")
end
| uu____14768 -> begin
(solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.EQ -> begin
(

let uu____14769 = lhs
in (match (uu____14769) with
| (_t1, ctx_uv, args_lhs) -> begin
(

let uu____14773 = (pat_vars env ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs)
in (match (uu____14773) with
| FStar_Pervasives_Native.Some (lhs_binders) -> begin
(

let rhs1 = (sn env rhs)
in (

let names_to_string1 = (fun fvs -> (

let uu____14790 = (

let uu____14793 = (FStar_Util.set_elements fvs)
in (FStar_List.map FStar_Syntax_Print.bv_to_string uu____14793))
in (FStar_All.pipe_right uu____14790 (FStar_String.concat ", "))))
in (

let fvs1 = (binders_as_bv_set (FStar_List.append ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders lhs_binders))
in (

let fvs2 = (FStar_Syntax_Free.names rhs1)
in (

let uu____14810 = (occurs_check ctx_uv rhs1)
in (match (uu____14810) with
| (uvars1, occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____14832 = (

let uu____14833 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____14833))
in (giveup_or_defer env orig wl uu____14832))
end
| uu____14834 -> begin
(

let uu____14835 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____14835) with
| true -> begin
(

let sol = (mk_solution env lhs lhs_binders rhs1)
in (

let wl1 = (restrict_all_uvars ctx_uv uvars1 wl)
in (

let uu____14840 = (solve_prob orig FStar_Pervasives_Native.None sol wl1)
in (solve env uu____14840))))
end
| uu____14841 -> begin
(match (wl.defer_ok) with
| true -> begin
(

let uu____14842 = (

let uu____14843 = (names_to_string1 fvs2)
in (

let uu____14844 = (names_to_string1 fvs1)
in (

let uu____14845 = (FStar_Syntax_Print.binders_to_string ", " (FStar_List.append ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders lhs_binders))
in (FStar_Util.format3 "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}" uu____14843 uu____14844 uu____14845))))
in (giveup_or_defer env orig wl uu____14842))
end
| uu____14852 -> begin
(first_order orig env wl lhs rhs1)
end)
end))
end)
end))))))
end
| uu____14853 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer env orig wl "Not a pattern")
end
| uu____14856 -> begin
(

let uu____14857 = (try_quasi_pattern orig env wl lhs rhs)
in (match (uu____14857) with
| (FStar_Util.Inr (sol), wl1) -> begin
(

let uu____14880 = (solve_prob orig FStar_Pervasives_Native.None sol wl1)
in (solve env uu____14880))
end
| (FStar_Util.Inl (msg), uu____14882) -> begin
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
(giveup_or_defer env orig wl "flex-flex subtyping")
end
| uu____14896 -> begin
(solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.SUBINV -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer env orig wl "flex-flex subtyping")
end
| uu____14897 -> begin
(solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.EQ -> begin
(match ((wl.defer_ok && ((not ((is_flex_pat lhs))) || (not ((is_flex_pat rhs)))))) with
| true -> begin
(giveup_or_defer env orig wl "flex-flex non-pattern")
end
| uu____14914 -> begin
(

let uu____14915 = (

let uu____14932 = (quasi_pattern env lhs)
in (

let uu____14939 = (quasi_pattern env rhs)
in ((uu____14932), (uu____14939))))
in (match (uu____14915) with
| (FStar_Pervasives_Native.Some (binders_lhs, t_res_lhs), FStar_Pervasives_Native.Some (binders_rhs, t_res_rhs)) -> begin
(

let uu____14982 = lhs
in (match (uu____14982) with
| ({FStar_Syntax_Syntax.n = uu____14983; FStar_Syntax_Syntax.pos = range; FStar_Syntax_Syntax.vars = uu____14985}, u_lhs, uu____14987) -> begin
(

let uu____14990 = rhs
in (match (uu____14990) with
| (uu____14991, u_rhs, uu____14993) -> begin
(

let uu____14994 = ((FStar_Syntax_Unionfind.equiv u_lhs.FStar_Syntax_Syntax.ctx_uvar_head u_rhs.FStar_Syntax_Syntax.ctx_uvar_head) && (binders_eq binders_lhs binders_rhs))
in (match (uu____14994) with
| true -> begin
(

let uu____14999 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____14999))
end
| uu____15000 -> begin
(

let uu____15001 = (maximal_prefix u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders)
in (match (uu____15001) with
| (ctx_w, (ctx_l, ctx_r)) -> begin
(

let gamma_w = (gamma_until u_lhs.FStar_Syntax_Syntax.ctx_uvar_gamma ctx_w)
in (

let zs = (intersect_binders gamma_w (FStar_List.append ctx_l binders_lhs) (FStar_List.append ctx_r binders_rhs))
in (

let uu____15033 = (

let uu____15040 = (

let uu____15043 = (FStar_Syntax_Syntax.mk_Total t_res_lhs)
in (FStar_Syntax_Util.arrow zs uu____15043))
in (new_uvar (Prims.strcat "flex-flex quasi:" (Prims.strcat "\tlhs=" (Prims.strcat u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason (Prims.strcat "\trhs=" u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason)))) wl range gamma_w ctx_w uu____15040 FStar_Syntax_Syntax.Strict))
in (match (uu____15033) with
| (uu____15046, w, wl1) -> begin
(

let w_app = (

let uu____15052 = (

let uu____15057 = (FStar_List.map (fun uu____15068 -> (match (uu____15068) with
| (z, uu____15076) -> begin
(

let uu____15081 = (FStar_Syntax_Syntax.bv_to_name z)
in (FStar_Syntax_Syntax.as_arg uu____15081))
end)) zs)
in (FStar_Syntax_Syntax.mk_Tm_app w uu____15057))
in (uu____15052 FStar_Pervasives_Native.None w.FStar_Syntax_Syntax.pos))
in ((

let uu____15085 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____15085) with
| true -> begin
(

let uu____15086 = (

let uu____15089 = (flex_t_to_string lhs)
in (

let uu____15090 = (

let uu____15093 = (flex_t_to_string rhs)
in (

let uu____15094 = (

let uu____15097 = (term_to_string w)
in (

let uu____15098 = (

let uu____15101 = (FStar_Syntax_Print.binders_to_string ", " (FStar_List.append ctx_l binders_lhs))
in (

let uu____15108 = (

let uu____15111 = (FStar_Syntax_Print.binders_to_string ", " (FStar_List.append ctx_r binders_rhs))
in (

let uu____15118 = (

let uu____15121 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (uu____15121)::[])
in (uu____15111)::uu____15118))
in (uu____15101)::uu____15108))
in (uu____15097)::uu____15098))
in (uu____15093)::uu____15094))
in (uu____15089)::uu____15090))
in (FStar_Util.print "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n" uu____15086))
end
| uu____15122 -> begin
()
end));
(

let sol = (

let s1 = (

let uu____15127 = (

let uu____15132 = (FStar_Syntax_Util.abs binders_lhs w_app (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot t_res_lhs))))
in ((u_lhs), (uu____15132)))
in TERM (uu____15127))
in (

let uu____15133 = (FStar_Syntax_Unionfind.equiv u_lhs.FStar_Syntax_Syntax.ctx_uvar_head u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____15133) with
| true -> begin
(s1)::[]
end
| uu____15136 -> begin
(

let s2 = (

let uu____15138 = (

let uu____15143 = (FStar_Syntax_Util.abs binders_rhs w_app (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot t_res_lhs))))
in ((u_rhs), (uu____15143)))
in TERM (uu____15138))
in (s1)::(s2)::[])
end)))
in (

let uu____15144 = (solve_prob orig FStar_Pervasives_Native.None sol wl1)
in (solve env uu____15144)));
))
end))))
end))
end))
end))
end))
end
| uu____15145 -> begin
(giveup_or_defer env orig wl "flex-flex: non-patterns")
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

let uu____15210 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____15210) with
| true -> begin
(

let uu____15211 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____15212 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____15213 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____15214 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n" (match (need_unif) with
| true -> begin
"need unification"
end
| uu____15215 -> begin
"match"
end) uu____15211 uu____15212 uu____15213 uu____15214)))))
end
| uu____15216 -> begin
()
end));
(

let uu____15217 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____15217) with
| (head1, args1) -> begin
(

let uu____15260 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____15260) with
| (head2, args2) -> begin
(

let solve_head_then = (fun wl2 k -> (match (need_unif) with
| true -> begin
(k true wl2)
end
| uu____15324 -> begin
(

let uu____15325 = (solve_maybe_uinsts env1 orig head1 head2 wl2)
in (match (uu____15325) with
| USolved (wl3) -> begin
(k true wl3)
end
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl3) -> begin
(k false (defer "universe constraints" orig wl3))
end))
end))
in (

let nargs = (FStar_List.length args1)
in (match ((Prims.op_disEquality nargs (FStar_List.length args2))) with
| true -> begin
(

let uu____15350 = (

let uu____15351 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____15352 = (args_to_string args1)
in (

let uu____15355 = (FStar_Syntax_Print.term_to_string head2)
in (

let uu____15356 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____15351 uu____15352 uu____15355 uu____15356)))))
in (giveup env1 uu____15350 orig))
end
| uu____15359 -> begin
(

let uu____15360 = ((Prims.op_Equality nargs (Prims.parse_int "0")) || (

let uu____15366 = (FStar_Syntax_Util.eq_args args1 args2)
in (Prims.op_Equality uu____15366 FStar_Syntax_Util.Equal)))
in (match (uu____15360) with
| true -> begin
(match (need_unif) with
| true -> begin
(solve_t env1 (

let uu___388_15368 = problem
in {FStar_TypeChecker_Common.pid = uu___388_15368.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = head1; FStar_TypeChecker_Common.relation = uu___388_15368.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = head2; FStar_TypeChecker_Common.element = uu___388_15368.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___388_15368.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___388_15368.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___388_15368.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___388_15368.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___388_15368.FStar_TypeChecker_Common.rank}) wl1)
end
| uu____15369 -> begin
(solve_head_then wl1 (fun ok wl2 -> (match (ok) with
| true -> begin
(

let uu____15375 = (solve_prob orig FStar_Pervasives_Native.None [] wl2)
in (solve env1 uu____15375))
end
| uu____15376 -> begin
(solve env1 wl2)
end)))
end)
end
| uu____15377 -> begin
(

let uu____15378 = (base_and_refinement env1 t1)
in (match (uu____15378) with
| (base1, refinement1) -> begin
(

let uu____15403 = (base_and_refinement env1 t2)
in (match (uu____15403) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(

let mk_sub_probs = (fun wl2 -> (

let argp = (match (need_unif) with
| true -> begin
(FStar_List.zip ((((head1), (FStar_Pervasives_Native.None)))::args1) ((((head2), (FStar_Pervasives_Native.None)))::args2))
end
| uu____15549 -> begin
(FStar_List.zip args1 args2)
end)
in (

let uu____15566 = (FStar_List.fold_right (fun uu____15606 uu____15607 -> (match (((uu____15606), (uu____15607))) with
| (((a1, uu____15659), (a2, uu____15661)), (probs, wl3)) -> begin
(

let uu____15710 = (mk_problem wl3 [] orig a1 FStar_TypeChecker_Common.EQ a2 FStar_Pervasives_Native.None "index")
in (match (uu____15710) with
| (prob', wl4) -> begin
(((FStar_TypeChecker_Common.TProb (prob'))::probs), (wl4))
end))
end)) argp (([]), (wl2)))
in (match (uu____15566) with
| (subprobs, wl3) -> begin
((

let uu____15752 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____15752) with
| true -> begin
(

let uu____15753 = (FStar_Syntax_Print.list_to_string (prob_to_string env1) subprobs)
in (FStar_Util.print1 "Adding subproblems for arguments: %s" uu____15753))
end
| uu____15754 -> begin
()
end));
(

let uu____15756 = (FStar_Options.defensive ())
in (match (uu____15756) with
| true -> begin
(FStar_List.iter (def_check_prob "solve_t\' subprobs") subprobs)
end
| uu____15757 -> begin
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
| uu____15775 -> begin
(

let uu____15776 = (mk_sub_probs wl3)
in (match (uu____15776) with
| (subprobs, wl4) -> begin
(

let formula = (

let uu____15792 = (FStar_List.map (fun p -> (p_guard p)) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____15792))
in (

let wl5 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) [] wl4)
in (

let uu____15800 = (attempt subprobs wl5)
in (solve env2 uu____15800))))
end))
end))))
in (

let solve_sub_probs_no_smt = (fun env2 wl2 -> (solve_head_then wl2 (fun ok wl3 -> (

let uu____15823 = (mk_sub_probs wl3)
in (match (uu____15823) with
| (subprobs, wl4) -> begin
(

let wl5 = (solve_prob orig FStar_Pervasives_Native.None [] wl4)
in (

let uu____15837 = (attempt subprobs wl5)
in (solve env2 uu____15837)))
end)))))
in (

let unfold_and_retry = (fun d env2 wl2 uu____15862 -> (match (uu____15862) with
| (prob, reason) -> begin
((

let uu____15870 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____15870) with
| true -> begin
(

let uu____15871 = (prob_to_string env2 orig)
in (

let uu____15872 = (prob_to_string env2 prob)
in (FStar_Util.print3 "Failed to solve %s because sub-problem %s is not solvable without SMT because %s" uu____15871 uu____15872 reason)))
end
| uu____15873 -> begin
()
end));
(

let uu____15874 = (

let uu____15883 = (FStar_TypeChecker_Normalize.unfold_head_once env2 t1)
in (

let uu____15886 = (FStar_TypeChecker_Normalize.unfold_head_once env2 t2)
in ((uu____15883), (uu____15886))))
in (match (uu____15874) with
| (FStar_Pervasives_Native.Some (t1'), FStar_Pervasives_Native.Some (t2')) -> begin
(

let uu____15899 = (FStar_Syntax_Util.head_and_args t1')
in (match (uu____15899) with
| (head1', uu____15917) -> begin
(

let uu____15942 = (FStar_Syntax_Util.head_and_args t2')
in (match (uu____15942) with
| (head2', uu____15960) -> begin
(

let uu____15985 = (

let uu____15990 = (FStar_Syntax_Util.eq_tm head1' head1)
in (

let uu____15991 = (FStar_Syntax_Util.eq_tm head2' head2)
in ((uu____15990), (uu____15991))))
in (match (uu____15985) with
| (FStar_Syntax_Util.Equal, FStar_Syntax_Util.Equal) -> begin
((

let uu____15993 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____15993) with
| true -> begin
(

let uu____15994 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____15995 = (FStar_Syntax_Print.term_to_string t1')
in (

let uu____15996 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____15997 = (FStar_Syntax_Print.term_to_string t2')
in (FStar_Util.print4 "Unfolding didn\'t make progress ... got %s ~> %s;\nand %s ~> %s\n" uu____15994 uu____15995 uu____15996 uu____15997)))))
end
| uu____15998 -> begin
()
end));
(solve_sub_probs env2 wl2);
)
end
| uu____15999 -> begin
(

let torig' = (

let uu___389_16007 = torig
in {FStar_TypeChecker_Common.pid = uu___389_16007.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1'; FStar_TypeChecker_Common.relation = uu___389_16007.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2'; FStar_TypeChecker_Common.element = uu___389_16007.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___389_16007.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___389_16007.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___389_16007.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___389_16007.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___389_16007.FStar_TypeChecker_Common.rank})
in ((

let uu____16009 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____16009) with
| true -> begin
(

let uu____16010 = (prob_to_string env2 (FStar_TypeChecker_Common.TProb (torig')))
in (FStar_Util.print1 "Unfolded and now trying %s\n" uu____16010))
end
| uu____16011 -> begin
()
end));
(solve_t env2 torig' wl2);
))
end))
end))
end))
end
| uu____16012 -> begin
(solve_sub_probs env2 wl2)
end));
)
end))
in (

let d = (

let uu____16024 = (delta_depth_of_term env1 head1)
in (match (uu____16024) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(FStar_TypeChecker_Common.decr_delta_depth d)
end))
in (

let treat_as_injective = (

let uu____16031 = (

let uu____16032 = (FStar_Syntax_Util.un_uinst head1)
in uu____16032.FStar_Syntax_Syntax.n)
in (match (uu____16031) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_TypeChecker_Env.fv_has_attr env1 fv FStar_Parser_Const.unifier_hint_injective_lid)
end
| uu____16036 -> begin
false
end))
in (match (d) with
| FStar_Pervasives_Native.Some (d1) when (wl1.smt_ok && (not (treat_as_injective))) -> begin
(try_solve_without_smt_or_else env1 wl1 solve_sub_probs_no_smt (unfold_and_retry d1))
end
| uu____16038 -> begin
(solve_sub_probs env1 wl1)
end)))))))
end
| uu____16041 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env1 (

let uu___390_16077 = problem
in {FStar_TypeChecker_Common.pid = uu___390_16077.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___390_16077.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___390_16077.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___390_16077.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___390_16077.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___390_16077.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___390_16077.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___390_16077.FStar_TypeChecker_Common.rank}) wl1)))
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

let uu____16152 = (destruct_flex_t scrutinee wl1)
in (match (uu____16152) with
| ((_t, uv, _args), wl2) -> begin
(

let uu____16163 = (FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p)
in (match (uu____16163) with
| (xs, pat_term, uu____16178, uu____16179) -> begin
(

let uu____16184 = (FStar_List.fold_left (fun uu____16207 x -> (match (uu____16207) with
| (subst1, wl3) -> begin
(

let t_x = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____16228 = (copy_uvar uv [] t_x wl3)
in (match (uu____16228) with
| (uu____16247, u, wl4) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (u))))::subst1
in ((subst2), (wl4)))
end)))
end)) (([]), (wl2)) xs)
in (match (uu____16184) with
| (subst1, wl3) -> begin
(

let pat_term1 = (FStar_Syntax_Subst.subst subst1 pat_term)
in (

let uu____16268 = (new_problem wl3 env1 scrutinee FStar_TypeChecker_Common.EQ pat_term1 FStar_Pervasives_Native.None scrutinee.FStar_Syntax_Syntax.pos "match heuristic")
in (match (uu____16268) with
| (prob, wl4) -> begin
(

let wl' = (

let uu___391_16284 = wl4
in {attempting = (FStar_TypeChecker_Common.TProb (prob))::[]; wl_deferred = []; ctr = uu___391_16284.ctr; defer_ok = false; smt_ok = false; umax_heuristic_ok = uu___391_16284.umax_heuristic_ok; tcenv = uu___391_16284.tcenv; wl_implicits = []})
in (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____16292 = (solve env1 wl')
in (match (uu____16292) with
| Success (uu____16295, imps) -> begin
(

let wl'1 = (

let uu___392_16298 = wl'
in {attempting = (orig)::[]; wl_deferred = uu___392_16298.wl_deferred; ctr = uu___392_16298.ctr; defer_ok = uu___392_16298.defer_ok; smt_ok = uu___392_16298.smt_ok; umax_heuristic_ok = uu___392_16298.umax_heuristic_ok; tcenv = uu___392_16298.tcenv; wl_implicits = uu___392_16298.wl_implicits})
in (

let uu____16299 = (solve env1 wl'1)
in (match (uu____16299) with
| Success (uu____16302, imps') -> begin
((FStar_Syntax_Unionfind.commit tx);
FStar_Pervasives_Native.Some ((

let uu___393_16306 = wl4
in {attempting = uu___393_16306.attempting; wl_deferred = uu___393_16306.wl_deferred; ctr = uu___393_16306.ctr; defer_ok = uu___393_16306.defer_ok; smt_ok = uu___393_16306.smt_ok; umax_heuristic_ok = uu___393_16306.umax_heuristic_ok; tcenv = uu___393_16306.tcenv; wl_implicits = (FStar_List.append wl4.wl_implicits (FStar_List.append imps imps'))}));
)
end
| Failed (uu____16307) -> begin
((FStar_Syntax_Unionfind.rollback tx);
FStar_Pervasives_Native.None;
)
end)))
end
| uu____16313 -> begin
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

let uu____16334 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____16334) with
| true -> begin
(

let uu____16335 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____16336 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying match heuristic for %s vs. %s\n" uu____16335 uu____16336)))
end
| uu____16337 -> begin
()
end));
(

let uu____16338 = (

let uu____16359 = (

let uu____16368 = (FStar_Syntax_Util.unmeta t1)
in ((s1), (uu____16368)))
in (

let uu____16375 = (

let uu____16384 = (FStar_Syntax_Util.unmeta t2)
in ((s2), (uu____16384)))
in ((uu____16359), (uu____16375))))
in (match (uu____16338) with
| ((uu____16413, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match (scrutinee, branches); FStar_Syntax_Syntax.pos = uu____16416; FStar_Syntax_Syntax.vars = uu____16417}), (s, t)) -> begin
(

let uu____16488 = (

let uu____16489 = (is_flex scrutinee)
in (not (uu____16489)))
in (match (uu____16488) with
| true -> begin
((

let uu____16497 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____16497) with
| true -> begin
(

let uu____16498 = (FStar_Syntax_Print.term_to_string scrutinee)
in (FStar_Util.print1 "match head %s is not a flex term\n" uu____16498))
end
| uu____16499 -> begin
()
end));
FStar_Util.Inr (FStar_Pervasives_Native.None);
)
end
| uu____16502 -> begin
(match (wl1.defer_ok) with
| true -> begin
((

let uu____16510 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____16510) with
| true -> begin
(FStar_Util.print_string "Deferring ... \n")
end
| uu____16511 -> begin
()
end));
FStar_Util.Inl ("defer");
)
end
| uu____16514 -> begin
((

let uu____16516 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____16516) with
| true -> begin
(

let uu____16517 = (FStar_Syntax_Print.term_to_string scrutinee)
in (

let uu____16518 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Heuristic applicable with scrutinee %s and other side = %s\n" uu____16517 uu____16518)))
end
| uu____16519 -> begin
()
end));
(

let pat_discriminates = (fun uu___350_16539 -> (match (uu___350_16539) with
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_constant (uu____16554); FStar_Syntax_Syntax.p = uu____16555}, FStar_Pervasives_Native.None, uu____16556) -> begin
true
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (uu____16569); FStar_Syntax_Syntax.p = uu____16570}, FStar_Pervasives_Native.None, uu____16571) -> begin
true
end
| uu____16596 -> begin
false
end))
in (

let head_matching_branch = (FStar_All.pipe_right branches (FStar_Util.try_find (fun b -> (match ((pat_discriminates b)) with
| true -> begin
(

let uu____16696 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____16696) with
| (uu____16697, uu____16698, t') -> begin
(

let uu____16716 = (head_matches_delta env1 wl1 s t')
in (match (uu____16716) with
| (FullMatch, uu____16727) -> begin
true
end
| (HeadMatch (uu____16740), uu____16741) -> begin
true
end
| uu____16754 -> begin
false
end))
end))
end
| uu____16765 -> begin
false
end))))
in (match (head_matching_branch) with
| FStar_Pervasives_Native.None -> begin
((

let uu____16787 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____16787) with
| true -> begin
(FStar_Util.print_string "No head_matching branch\n")
end
| uu____16788 -> begin
()
end));
(

let try_branches = (

let uu____16792 = (FStar_Util.prefix_until (fun b -> (not ((pat_discriminates b)))) branches)
in (match (uu____16792) with
| FStar_Pervasives_Native.Some (branches1, uu____16880, uu____16881) -> begin
branches1
end
| uu____17026 -> begin
branches
end))
in (

let uu____17081 = (FStar_Util.find_map try_branches (fun b -> (

let uu____17090 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____17090) with
| (p, uu____17094, uu____17095) -> begin
(try_solve_branch scrutinee p)
end))))
in (FStar_All.pipe_left (fun _0_8 -> FStar_Util.Inr (_0_8)) uu____17081)));
)
end
| FStar_Pervasives_Native.Some (b) -> begin
(

let uu____17151 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____17151) with
| (p, uu____17159, e) -> begin
((

let uu____17178 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____17178) with
| true -> begin
(

let uu____17179 = (FStar_Syntax_Print.pat_to_string p)
in (

let uu____17180 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print2 "Found head matching branch %s -> %s\n" uu____17179 uu____17180)))
end
| uu____17181 -> begin
()
end));
(

let uu____17182 = (try_solve_branch scrutinee p)
in (FStar_All.pipe_left (fun _0_9 -> FStar_Util.Inr (_0_9)) uu____17182));
)
end))
end)));
)
end)
end))
end
| ((s, t), (uu____17197, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match (scrutinee, branches); FStar_Syntax_Syntax.pos = uu____17200; FStar_Syntax_Syntax.vars = uu____17201})) -> begin
(

let uu____17270 = (

let uu____17271 = (is_flex scrutinee)
in (not (uu____17271)))
in (match (uu____17270) with
| true -> begin
((

let uu____17279 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____17279) with
| true -> begin
(

let uu____17280 = (FStar_Syntax_Print.term_to_string scrutinee)
in (FStar_Util.print1 "match head %s is not a flex term\n" uu____17280))
end
| uu____17281 -> begin
()
end));
FStar_Util.Inr (FStar_Pervasives_Native.None);
)
end
| uu____17284 -> begin
(match (wl1.defer_ok) with
| true -> begin
((

let uu____17292 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____17292) with
| true -> begin
(FStar_Util.print_string "Deferring ... \n")
end
| uu____17293 -> begin
()
end));
FStar_Util.Inl ("defer");
)
end
| uu____17296 -> begin
((

let uu____17298 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____17298) with
| true -> begin
(

let uu____17299 = (FStar_Syntax_Print.term_to_string scrutinee)
in (

let uu____17300 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Heuristic applicable with scrutinee %s and other side = %s\n" uu____17299 uu____17300)))
end
| uu____17301 -> begin
()
end));
(

let pat_discriminates = (fun uu___350_17321 -> (match (uu___350_17321) with
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_constant (uu____17336); FStar_Syntax_Syntax.p = uu____17337}, FStar_Pervasives_Native.None, uu____17338) -> begin
true
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (uu____17351); FStar_Syntax_Syntax.p = uu____17352}, FStar_Pervasives_Native.None, uu____17353) -> begin
true
end
| uu____17378 -> begin
false
end))
in (

let head_matching_branch = (FStar_All.pipe_right branches (FStar_Util.try_find (fun b -> (match ((pat_discriminates b)) with
| true -> begin
(

let uu____17478 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____17478) with
| (uu____17479, uu____17480, t') -> begin
(

let uu____17498 = (head_matches_delta env1 wl1 s t')
in (match (uu____17498) with
| (FullMatch, uu____17509) -> begin
true
end
| (HeadMatch (uu____17522), uu____17523) -> begin
true
end
| uu____17536 -> begin
false
end))
end))
end
| uu____17547 -> begin
false
end))))
in (match (head_matching_branch) with
| FStar_Pervasives_Native.None -> begin
((

let uu____17569 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____17569) with
| true -> begin
(FStar_Util.print_string "No head_matching branch\n")
end
| uu____17570 -> begin
()
end));
(

let try_branches = (

let uu____17574 = (FStar_Util.prefix_until (fun b -> (not ((pat_discriminates b)))) branches)
in (match (uu____17574) with
| FStar_Pervasives_Native.Some (branches1, uu____17662, uu____17663) -> begin
branches1
end
| uu____17808 -> begin
branches
end))
in (

let uu____17863 = (FStar_Util.find_map try_branches (fun b -> (

let uu____17872 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____17872) with
| (p, uu____17876, uu____17877) -> begin
(try_solve_branch scrutinee p)
end))))
in (FStar_All.pipe_left (fun _0_10 -> FStar_Util.Inr (_0_10)) uu____17863)));
)
end
| FStar_Pervasives_Native.Some (b) -> begin
(

let uu____17933 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____17933) with
| (p, uu____17941, e) -> begin
((

let uu____17960 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____17960) with
| true -> begin
(

let uu____17961 = (FStar_Syntax_Print.pat_to_string p)
in (

let uu____17962 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print2 "Found head matching branch %s -> %s\n" uu____17961 uu____17962)))
end
| uu____17963 -> begin
()
end));
(

let uu____17964 = (try_solve_branch scrutinee p)
in (FStar_All.pipe_left (fun _0_11 -> FStar_Util.Inr (_0_11)) uu____17964));
)
end))
end)));
)
end)
end))
end
| uu____17977 -> begin
((

let uu____17999 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____17999) with
| true -> begin
(

let uu____18000 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____18001 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print2 "Heuristic not applicable: tag lhs=%s, rhs=%s\n" uu____18000 uu____18001)))
end
| uu____18002 -> begin
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

let uu____18043 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("RelDelta")))
in (match (uu____18043) with
| true -> begin
(

let uu____18044 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____18045 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____18046 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____18047 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n" uu____18044 uu____18045 uu____18046 uu____18047)))))
end
| uu____18048 -> begin
()
end));
(

let uu____18049 = (head_matches_delta env1 wl1 t1 t2)
in (match (uu____18049) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____18080), uu____18081) -> begin
(

let rec may_relate = (fun head3 -> (

let uu____18108 = (

let uu____18109 = (FStar_Syntax_Subst.compress head3)
in uu____18109.FStar_Syntax_Syntax.n)
in (match (uu____18108) with
| FStar_Syntax_Syntax.Tm_name (uu____18112) -> begin
true
end
| FStar_Syntax_Syntax.Tm_match (uu____18113) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____18137 = (FStar_TypeChecker_Env.delta_depth_of_fv env1 fv)
in (match (uu____18137) with
| FStar_Syntax_Syntax.Delta_equational_at_level (uu____18138) -> begin
true
end
| FStar_Syntax_Syntax.Delta_abstract (uu____18139) -> begin
(Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)
end
| uu____18140 -> begin
false
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____18142, uu____18143) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____18185) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____18191) -> begin
(may_relate t)
end
| uu____18196 -> begin
false
end)))
in (

let uu____18197 = (try_match_heuristic env1 orig wl1 t1 t2 o)
in (match (uu____18197) with
| FStar_Util.Inl (_defer_ok) -> begin
(giveup_or_defer1 orig "delaying match heuristic")
end
| FStar_Util.Inr (FStar_Pervasives_Native.Some (wl2)) -> begin
(solve env1 wl2)
end
| FStar_Util.Inr (FStar_Pervasives_Native.None) -> begin
(

let uu____18212 = (((may_relate head1) || (may_relate head2)) && wl1.smt_ok)
in (match (uu____18212) with
| true -> begin
(

let uu____18213 = (guard_of_prob env1 wl1 problem t1 t2)
in (match (uu____18213) with
| (guard, wl2) -> begin
(

let uu____18220 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl2)
in (solve env1 uu____18220))
end))
end
| uu____18221 -> begin
(

let uu____18222 = (

let uu____18223 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____18224 = (

let uu____18225 = (

let uu____18228 = (delta_depth_of_term env1 head1)
in (FStar_Util.bind_opt uu____18228 (fun x -> (

let uu____18234 = (FStar_Syntax_Print.delta_depth_to_string x)
in FStar_Pervasives_Native.Some (uu____18234)))))
in (FStar_Util.dflt "" uu____18225))
in (

let uu____18235 = (FStar_Syntax_Print.term_to_string head2)
in (

let uu____18236 = (

let uu____18237 = (

let uu____18240 = (delta_depth_of_term env1 head2)
in (FStar_Util.bind_opt uu____18240 (fun x -> (

let uu____18246 = (FStar_Syntax_Print.delta_depth_to_string x)
in FStar_Pervasives_Native.Some (uu____18246)))))
in (FStar_Util.dflt "" uu____18237))
in (FStar_Util.format4 "head mismatch (%s (%s) vs %s (%s))" uu____18223 uu____18224 uu____18235 uu____18236)))))
in (giveup env1 uu____18222 orig))
end))
end)))
end
| (HeadMatch (true), uu____18247) when (Prims.op_disEquality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(match (wl1.smt_ok) with
| true -> begin
(

let uu____18260 = (guard_of_prob env1 wl1 problem t1 t2)
in (match (uu____18260) with
| (guard, wl2) -> begin
(

let uu____18267 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl2)
in (solve env1 uu____18267))
end))
end
| uu____18268 -> begin
(

let uu____18269 = (

let uu____18270 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____18271 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "head mismatch for subtyping (%s vs %s)" uu____18270 uu____18271)))
in (giveup env1 uu____18269 orig))
end)
end
| (uu____18272, FStar_Pervasives_Native.Some (t11, t21)) -> begin
(solve_t env1 (

let uu___394_18286 = problem
in {FStar_TypeChecker_Common.pid = uu___394_18286.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___394_18286.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___394_18286.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___394_18286.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___394_18286.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___394_18286.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___394_18286.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___394_18286.FStar_TypeChecker_Common.rank}) wl1)
end
| (HeadMatch (unif), FStar_Pervasives_Native.None) -> begin
(rigid_heads_match env1 unif torig wl1 t1 t2)
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

let uu____18310 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____18310) with
| true -> begin
(

let uu____18311 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____18311))
end
| uu____18312 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in ((

let uu____18316 = (

let uu____18319 = (p_scope orig)
in (FStar_List.map FStar_Pervasives_Native.fst uu____18319))
in (FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1" uu____18316 t1));
(

let uu____18337 = (

let uu____18340 = (p_scope orig)
in (FStar_List.map FStar_Pervasives_Native.fst uu____18340))
in (FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2" uu____18337 t2));
(

let uu____18358 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____18358) with
| true -> begin
(

let uu____18359 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____18360 = (

let uu____18361 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____18362 = (

let uu____18363 = (FStar_Syntax_Print.term_to_string t1)
in (Prims.strcat "::" uu____18363))
in (Prims.strcat uu____18361 uu____18362)))
in (

let uu____18364 = (

let uu____18365 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____18366 = (

let uu____18367 = (FStar_Syntax_Print.term_to_string t2)
in (Prims.strcat "::" uu____18367))
in (Prims.strcat uu____18365 uu____18366)))
in (FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n" uu____18359 uu____18360 uu____18364 (rel_to_string problem.FStar_TypeChecker_Common.relation)))))
end
| uu____18368 -> begin
()
end));
(

let r = (FStar_TypeChecker_Env.get_range env)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_delayed (uu____18370), uu____18371) -> begin
(failwith "Impossible: terms were not compressed")
end
| (uu____18394, FStar_Syntax_Syntax.Tm_delayed (uu____18395)) -> begin
(failwith "Impossible: terms were not compressed")
end
| (FStar_Syntax_Syntax.Tm_ascribed (uu____18418), uu____18419) -> begin
(

let uu____18446 = (

let uu___395_18447 = problem
in (

let uu____18448 = (FStar_Syntax_Util.unascribe t1)
in {FStar_TypeChecker_Common.pid = uu___395_18447.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____18448; FStar_TypeChecker_Common.relation = uu___395_18447.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___395_18447.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___395_18447.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___395_18447.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___395_18447.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___395_18447.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___395_18447.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___395_18447.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____18446 wl))
end
| (FStar_Syntax_Syntax.Tm_meta (uu____18449), uu____18450) -> begin
(

let uu____18457 = (

let uu___396_18458 = problem
in (

let uu____18459 = (FStar_Syntax_Util.unmeta t1)
in {FStar_TypeChecker_Common.pid = uu___396_18458.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____18459; FStar_TypeChecker_Common.relation = uu___396_18458.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___396_18458.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___396_18458.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___396_18458.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___396_18458.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___396_18458.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___396_18458.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___396_18458.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____18457 wl))
end
| (uu____18460, FStar_Syntax_Syntax.Tm_ascribed (uu____18461)) -> begin
(

let uu____18488 = (

let uu___397_18489 = problem
in (

let uu____18490 = (FStar_Syntax_Util.unascribe t2)
in {FStar_TypeChecker_Common.pid = uu___397_18489.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___397_18489.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___397_18489.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____18490; FStar_TypeChecker_Common.element = uu___397_18489.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___397_18489.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___397_18489.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___397_18489.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___397_18489.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___397_18489.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____18488 wl))
end
| (uu____18491, FStar_Syntax_Syntax.Tm_meta (uu____18492)) -> begin
(

let uu____18499 = (

let uu___398_18500 = problem
in (

let uu____18501 = (FStar_Syntax_Util.unmeta t2)
in {FStar_TypeChecker_Common.pid = uu___398_18500.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___398_18500.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___398_18500.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____18501; FStar_TypeChecker_Common.element = uu___398_18500.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___398_18500.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___398_18500.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___398_18500.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___398_18500.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___398_18500.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____18499 wl))
end
| (FStar_Syntax_Syntax.Tm_quoted (t11, uu____18503), FStar_Syntax_Syntax.Tm_quoted (t21, uu____18505)) -> begin
(

let uu____18514 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____18514))
end
| (FStar_Syntax_Syntax.Tm_bvar (uu____18515), uu____18516) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (uu____18517, FStar_Syntax_Syntax.Tm_bvar (uu____18518)) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (FStar_Syntax_Syntax.Tm_type (u1), FStar_Syntax_Syntax.Tm_type (u2)) -> begin
(solve_one_universe_eq env orig u1 u2 wl)
end
| (FStar_Syntax_Syntax.Tm_arrow (bs1, c1), FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) -> begin
(

let mk_c = (fun c uu___351_18587 -> (match (uu___351_18587) with
| [] -> begin
c
end
| bs -> begin
(

let uu____18615 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____18615))
end))
in (

let uu____18626 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____18626) with
| ((bs11, c11), (bs21, c21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun wl1 scope env1 subst1 -> (

let c12 = (FStar_Syntax_Subst.subst_comp subst1 c11)
in (

let c22 = (FStar_Syntax_Subst.subst_comp subst1 c21)
in (

let rel = (

let uu____18775 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____18775) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____18776 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (mk_c_problem wl1 scope orig c12 rel c22 FStar_Pervasives_Native.None "function co-domain"))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___352_18860 -> (match (uu___352_18860) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____18902 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____18902) with
| ((bs11, tbody11), (bs21, tbody21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun wl1 scope env1 subst1 -> (

let uu____19047 = (FStar_Syntax_Subst.subst subst1 tbody11)
in (

let uu____19048 = (FStar_Syntax_Subst.subst subst1 tbody21)
in (mk_t_problem wl1 scope orig uu____19047 problem.FStar_TypeChecker_Common.relation uu____19048 FStar_Pervasives_Native.None "lambda co-domain")))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (uu____19049), uu____19050) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____19079) -> begin
true
end
| uu____19098 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____19123 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____19133 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let force_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
t
end
| uu____19150 -> begin
(

let uu____19151 = (env.FStar_TypeChecker_Env.type_of (

let uu___399_19159 = env
in {FStar_TypeChecker_Env.solver = uu___399_19159.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___399_19159.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___399_19159.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___399_19159.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___399_19159.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___399_19159.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___399_19159.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___399_19159.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___399_19159.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___399_19159.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___399_19159.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___399_19159.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___399_19159.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___399_19159.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___399_19159.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___399_19159.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___399_19159.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___399_19159.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___399_19159.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___399_19159.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___399_19159.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___399_19159.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___399_19159.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___399_19159.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___399_19159.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___399_19159.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___399_19159.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___399_19159.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___399_19159.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___399_19159.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___399_19159.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___399_19159.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___399_19159.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___399_19159.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___399_19159.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___399_19159.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___399_19159.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___399_19159.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___399_19159.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___399_19159.FStar_TypeChecker_Env.nbe}) t)
in (match (uu____19151) with
| (uu____19162, ty, uu____19164) -> begin
(

let ty1 = (

let rec aux = (fun ty1 -> (

let ty2 = (FStar_TypeChecker_Normalize.unfold_whnf env ty1)
in (

let uu____19173 = (

let uu____19174 = (FStar_Syntax_Subst.compress ty2)
in uu____19174.FStar_Syntax_Syntax.n)
in (match (uu____19173) with
| FStar_Syntax_Syntax.Tm_refine (uu____19177) -> begin
(

let uu____19184 = (FStar_Syntax_Util.unrefine ty2)
in (aux uu____19184))
end
| uu____19185 -> begin
ty2
end))))
in (aux ty))
in (

let r1 = (FStar_TypeChecker_Normalize.eta_expand_with_type env t ty1)
in ((

let uu____19188 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____19188) with
| true -> begin
(

let uu____19189 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____19190 = (

let uu____19191 = (FStar_TypeChecker_Normalize.unfold_whnf env ty1)
in (FStar_Syntax_Print.term_to_string uu____19191))
in (

let uu____19192 = (FStar_Syntax_Print.term_to_string r1)
in (FStar_Util.print3 "force_eta of (%s) at type (%s) = %s\n" uu____19189 uu____19190 uu____19192))))
end
| uu____19193 -> begin
()
end));
r1;
)))
end))
end))
in (

let uu____19194 = (

let uu____19211 = (maybe_eta t1)
in (

let uu____19218 = (maybe_eta t2)
in ((uu____19211), (uu____19218))))
in (match (uu____19194) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___400_19260 = problem
in {FStar_TypeChecker_Common.pid = uu___400_19260.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___400_19260.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___400_19260.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___400_19260.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___400_19260.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___400_19260.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___400_19260.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___400_19260.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____19281 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____19281) with
| true -> begin
(

let uu____19282 = (destruct_flex_t not_abs wl)
in (match (uu____19282) with
| (flex, wl1) -> begin
(solve_t_flex_rigid_eq env orig wl1 flex t_abs)
end))
end
| uu____19289 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___401_19297 = problem
in {FStar_TypeChecker_Common.pid = uu___401_19297.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___401_19297.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___401_19297.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___401_19297.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___401_19297.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___401_19297.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___401_19297.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___401_19297.FStar_TypeChecker_Common.rank}) wl)
end
| uu____19298 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____19319 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____19319) with
| true -> begin
(

let uu____19320 = (destruct_flex_t not_abs wl)
in (match (uu____19320) with
| (flex, wl1) -> begin
(solve_t_flex_rigid_eq env orig wl1 flex t_abs)
end))
end
| uu____19327 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___401_19335 = problem
in {FStar_TypeChecker_Common.pid = uu___401_19335.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___401_19335.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___401_19335.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___401_19335.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___401_19335.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___401_19335.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___401_19335.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___401_19335.FStar_TypeChecker_Common.rank}) wl)
end
| uu____19336 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| uu____19337 -> begin
(failwith "Impossible: at least one side is an abstraction")
end)))))
end
| (uu____19354, FStar_Syntax_Syntax.Tm_abs (uu____19355)) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____19384) -> begin
true
end
| uu____19403 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____19428 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____19438 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let force_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
t
end
| uu____19455 -> begin
(

let uu____19456 = (env.FStar_TypeChecker_Env.type_of (

let uu___399_19464 = env
in {FStar_TypeChecker_Env.solver = uu___399_19464.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___399_19464.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___399_19464.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___399_19464.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___399_19464.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___399_19464.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___399_19464.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___399_19464.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___399_19464.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___399_19464.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___399_19464.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___399_19464.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___399_19464.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___399_19464.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___399_19464.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___399_19464.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___399_19464.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___399_19464.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___399_19464.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___399_19464.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___399_19464.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___399_19464.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___399_19464.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___399_19464.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___399_19464.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___399_19464.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___399_19464.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___399_19464.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___399_19464.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___399_19464.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___399_19464.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___399_19464.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___399_19464.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___399_19464.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___399_19464.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___399_19464.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___399_19464.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___399_19464.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___399_19464.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___399_19464.FStar_TypeChecker_Env.nbe}) t)
in (match (uu____19456) with
| (uu____19467, ty, uu____19469) -> begin
(

let ty1 = (

let rec aux = (fun ty1 -> (

let ty2 = (FStar_TypeChecker_Normalize.unfold_whnf env ty1)
in (

let uu____19478 = (

let uu____19479 = (FStar_Syntax_Subst.compress ty2)
in uu____19479.FStar_Syntax_Syntax.n)
in (match (uu____19478) with
| FStar_Syntax_Syntax.Tm_refine (uu____19482) -> begin
(

let uu____19489 = (FStar_Syntax_Util.unrefine ty2)
in (aux uu____19489))
end
| uu____19490 -> begin
ty2
end))))
in (aux ty))
in (

let r1 = (FStar_TypeChecker_Normalize.eta_expand_with_type env t ty1)
in ((

let uu____19493 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____19493) with
| true -> begin
(

let uu____19494 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____19495 = (

let uu____19496 = (FStar_TypeChecker_Normalize.unfold_whnf env ty1)
in (FStar_Syntax_Print.term_to_string uu____19496))
in (

let uu____19497 = (FStar_Syntax_Print.term_to_string r1)
in (FStar_Util.print3 "force_eta of (%s) at type (%s) = %s\n" uu____19494 uu____19495 uu____19497))))
end
| uu____19498 -> begin
()
end));
r1;
)))
end))
end))
in (

let uu____19499 = (

let uu____19516 = (maybe_eta t1)
in (

let uu____19523 = (maybe_eta t2)
in ((uu____19516), (uu____19523))))
in (match (uu____19499) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___400_19565 = problem
in {FStar_TypeChecker_Common.pid = uu___400_19565.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___400_19565.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___400_19565.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___400_19565.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___400_19565.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___400_19565.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___400_19565.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___400_19565.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____19586 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____19586) with
| true -> begin
(

let uu____19587 = (destruct_flex_t not_abs wl)
in (match (uu____19587) with
| (flex, wl1) -> begin
(solve_t_flex_rigid_eq env orig wl1 flex t_abs)
end))
end
| uu____19594 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___401_19602 = problem
in {FStar_TypeChecker_Common.pid = uu___401_19602.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___401_19602.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___401_19602.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___401_19602.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___401_19602.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___401_19602.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___401_19602.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___401_19602.FStar_TypeChecker_Common.rank}) wl)
end
| uu____19603 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____19624 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____19624) with
| true -> begin
(

let uu____19625 = (destruct_flex_t not_abs wl)
in (match (uu____19625) with
| (flex, wl1) -> begin
(solve_t_flex_rigid_eq env orig wl1 flex t_abs)
end))
end
| uu____19632 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___401_19640 = problem
in {FStar_TypeChecker_Common.pid = uu___401_19640.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___401_19640.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___401_19640.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___401_19640.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___401_19640.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___401_19640.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___401_19640.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___401_19640.FStar_TypeChecker_Common.rank}) wl)
end
| uu____19641 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| uu____19642 -> begin
(failwith "Impossible: at least one side is an abstraction")
end)))))
end
| (FStar_Syntax_Syntax.Tm_refine (x1, phi1), FStar_Syntax_Syntax.Tm_refine (x2, phi2)) -> begin
(

let uu____19671 = (

let uu____19676 = (head_matches_delta env wl x1.FStar_Syntax_Syntax.sort x2.FStar_Syntax_Syntax.sort)
in (match (uu____19676) with
| (FullMatch, FStar_Pervasives_Native.Some (t11, t21)) -> begin
(((

let uu___402_19704 = x1
in {FStar_Syntax_Syntax.ppname = uu___402_19704.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___402_19704.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t11})), ((

let uu___403_19706 = x2
in {FStar_Syntax_Syntax.ppname = uu___403_19706.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___403_19706.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t21})))
end
| (HeadMatch (uu____19707), FStar_Pervasives_Native.Some (t11, t21)) -> begin
(((

let uu___402_19721 = x1
in {FStar_Syntax_Syntax.ppname = uu___402_19721.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___402_19721.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t11})), ((

let uu___403_19723 = x2
in {FStar_Syntax_Syntax.ppname = uu___403_19723.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___403_19723.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t21})))
end
| uu____19724 -> begin
((x1), (x2))
end))
in (match (uu____19671) with
| (x11, x21) -> begin
(

let t11 = (FStar_Syntax_Util.refine x11 phi1)
in (

let t21 = (FStar_Syntax_Util.refine x21 phi2)
in (

let uu____19743 = (as_refinement false env t11)
in (match (uu____19743) with
| (x12, phi11) -> begin
(

let uu____19750 = (as_refinement false env t21)
in (match (uu____19750) with
| (x22, phi21) -> begin
((

let uu____19758 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____19758) with
| true -> begin
((

let uu____19760 = (FStar_Syntax_Print.bv_to_string x12)
in (

let uu____19761 = (FStar_Syntax_Print.term_to_string x12.FStar_Syntax_Syntax.sort)
in (

let uu____19762 = (FStar_Syntax_Print.term_to_string phi11)
in (FStar_Util.print3 "ref1 = (%s):(%s){%s}\n" uu____19760 uu____19761 uu____19762))));
(

let uu____19763 = (FStar_Syntax_Print.bv_to_string x22)
in (

let uu____19764 = (FStar_Syntax_Print.term_to_string x22.FStar_Syntax_Syntax.sort)
in (

let uu____19765 = (FStar_Syntax_Print.term_to_string phi21)
in (FStar_Util.print3 "ref2 = (%s):(%s){%s}\n" uu____19763 uu____19764 uu____19765))));
)
end
| uu____19766 -> begin
()
end));
(

let uu____19767 = (mk_t_problem wl [] orig x12.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x22.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (match (uu____19767) with
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

let uu____19835 = (imp phi13 phi23)
in (FStar_All.pipe_right uu____19835 (guard_on_element wl1 problem x13))))
in (

let fallback = (fun uu____19847 -> (

let impl = (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp1 FStar_Syntax_Util.mk_iff phi12 phi22)
end
| uu____19853 -> begin
(mk_imp1 FStar_Syntax_Util.mk_imp phi12 phi22)
end)
in (

let guard = (FStar_Syntax_Util.mk_conj (p_guard base_prob) impl)
in ((

let uu____19858 = (

let uu____19861 = (p_scope orig)
in (FStar_List.map FStar_Pervasives_Native.fst uu____19861))
in (FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.1" uu____19858 (p_guard base_prob)));
(

let uu____19879 = (

let uu____19882 = (p_scope orig)
in (FStar_List.map FStar_Pervasives_Native.fst uu____19882))
in (FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.2" uu____19879 impl));
(

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl1)
in (

let uu____19900 = (attempt ((base_prob)::[]) wl2)
in (solve env1 uu____19900)));
))))
in (

let has_uvars = ((

let uu____19904 = (

let uu____19905 = (FStar_Syntax_Free.uvars phi12)
in (FStar_Util.set_is_empty uu____19905))
in (not (uu____19904))) || (

let uu____19909 = (

let uu____19910 = (FStar_Syntax_Free.uvars phi22)
in (FStar_Util.set_is_empty uu____19910))
in (not (uu____19909))))
in (match (((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) || ((not (env1.FStar_TypeChecker_Env.uvar_subtyping)) && has_uvars))) with
| true -> begin
(

let uu____19913 = (

let uu____19918 = (

let uu____19927 = (FStar_Syntax_Syntax.mk_binder x13)
in (uu____19927)::[])
in (mk_t_problem wl1 uu____19918 orig phi12 FStar_TypeChecker_Common.EQ phi22 FStar_Pervasives_Native.None "refinement formula"))
in (match (uu____19913) with
| (ref_prob, wl2) -> begin
(

let uu____19948 = (solve env1 (

let uu___404_19950 = wl2
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___404_19950.ctr; defer_ok = false; smt_ok = uu___404_19950.smt_ok; umax_heuristic_ok = uu___404_19950.umax_heuristic_ok; tcenv = uu___404_19950.tcenv; wl_implicits = uu___404_19950.wl_implicits}))
in (match (uu____19948) with
| Failed (prob, msg) -> begin
(match ((((not (env1.FStar_TypeChecker_Env.uvar_subtyping)) && has_uvars) || (not (wl2.smt_ok)))) with
| true -> begin
(giveup env1 msg prob)
end
| uu____19959 -> begin
(fallback ())
end)
end
| Success (uu____19960) -> begin
(

let guard = (

let uu____19968 = (FStar_All.pipe_right (p_guard ref_prob) (guard_on_element wl2 problem x13))
in (FStar_Syntax_Util.mk_conj (p_guard base_prob) uu____19968))
in (

let wl3 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl2)
in (

let wl4 = (

let uu___405_19977 = wl3
in {attempting = uu___405_19977.attempting; wl_deferred = uu___405_19977.wl_deferred; ctr = (wl3.ctr + (Prims.parse_int "1")); defer_ok = uu___405_19977.defer_ok; smt_ok = uu___405_19977.smt_ok; umax_heuristic_ok = uu___405_19977.umax_heuristic_ok; tcenv = uu___405_19977.tcenv; wl_implicits = uu___405_19977.wl_implicits})
in (

let uu____19978 = (attempt ((base_prob)::[]) wl4)
in (solve env1 uu____19978)))))
end))
end))
end
| uu____19979 -> begin
(fallback ())
end)))))))))
end));
)
end))
end))))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____19980), FStar_Syntax_Syntax.Tm_uvar (uu____19981)) -> begin
(

let uu____20006 = (destruct_flex_t t1 wl)
in (match (uu____20006) with
| (f1, wl1) -> begin
(

let uu____20013 = (destruct_flex_t t2 wl1)
in (match (uu____20013) with
| (f2, wl2) -> begin
(solve_t_flex_flex env orig wl2 f1 f2)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____20020); FStar_Syntax_Syntax.pos = uu____20021; FStar_Syntax_Syntax.vars = uu____20022}, uu____20023), FStar_Syntax_Syntax.Tm_uvar (uu____20024)) -> begin
(

let uu____20073 = (destruct_flex_t t1 wl)
in (match (uu____20073) with
| (f1, wl1) -> begin
(

let uu____20080 = (destruct_flex_t t2 wl1)
in (match (uu____20080) with
| (f2, wl2) -> begin
(solve_t_flex_flex env orig wl2 f1 f2)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____20087), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____20088); FStar_Syntax_Syntax.pos = uu____20089; FStar_Syntax_Syntax.vars = uu____20090}, uu____20091)) -> begin
(

let uu____20140 = (destruct_flex_t t1 wl)
in (match (uu____20140) with
| (f1, wl1) -> begin
(

let uu____20147 = (destruct_flex_t t2 wl1)
in (match (uu____20147) with
| (f2, wl2) -> begin
(solve_t_flex_flex env orig wl2 f1 f2)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____20154); FStar_Syntax_Syntax.pos = uu____20155; FStar_Syntax_Syntax.vars = uu____20156}, uu____20157), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____20158); FStar_Syntax_Syntax.pos = uu____20159; FStar_Syntax_Syntax.vars = uu____20160}, uu____20161)) -> begin
(

let uu____20234 = (destruct_flex_t t1 wl)
in (match (uu____20234) with
| (f1, wl1) -> begin
(

let uu____20241 = (destruct_flex_t t2 wl1)
in (match (uu____20241) with
| (f2, wl2) -> begin
(solve_t_flex_flex env orig wl2 f1 f2)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____20248), uu____20249) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(

let uu____20262 = (destruct_flex_t t1 wl)
in (match (uu____20262) with
| (f1, wl1) -> begin
(solve_t_flex_rigid_eq env orig wl1 f1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____20269); FStar_Syntax_Syntax.pos = uu____20270; FStar_Syntax_Syntax.vars = uu____20271}, uu____20272), uu____20273) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(

let uu____20310 = (destruct_flex_t t1 wl)
in (match (uu____20310) with
| (f1, wl1) -> begin
(solve_t_flex_rigid_eq env orig wl1 f1 t2)
end))
end
| (uu____20317, FStar_Syntax_Syntax.Tm_uvar (uu____20318)) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (uu____20331, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____20332); FStar_Syntax_Syntax.pos = uu____20333; FStar_Syntax_Syntax.vars = uu____20334}, uu____20335)) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____20372), FStar_Syntax_Syntax.Tm_arrow (uu____20373)) -> begin
(solve_t' env (

let uu___406_20401 = problem
in {FStar_TypeChecker_Common.pid = uu___406_20401.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___406_20401.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___406_20401.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___406_20401.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___406_20401.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___406_20401.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___406_20401.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___406_20401.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___406_20401.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____20402); FStar_Syntax_Syntax.pos = uu____20403; FStar_Syntax_Syntax.vars = uu____20404}, uu____20405), FStar_Syntax_Syntax.Tm_arrow (uu____20406)) -> begin
(solve_t' env (

let uu___406_20458 = problem
in {FStar_TypeChecker_Common.pid = uu___406_20458.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___406_20458.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___406_20458.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___406_20458.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___406_20458.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___406_20458.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___406_20458.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___406_20458.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___406_20458.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____20459, FStar_Syntax_Syntax.Tm_uvar (uu____20460)) -> begin
(

let uu____20473 = (attempt ((FStar_TypeChecker_Common.TProb (problem))::[]) wl)
in (solve env uu____20473))
end
| (uu____20474, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____20475); FStar_Syntax_Syntax.pos = uu____20476; FStar_Syntax_Syntax.vars = uu____20477}, uu____20478)) -> begin
(

let uu____20515 = (attempt ((FStar_TypeChecker_Common.TProb (problem))::[]) wl)
in (solve env uu____20515))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____20516), uu____20517) -> begin
(

let uu____20530 = (attempt ((FStar_TypeChecker_Common.TProb (problem))::[]) wl)
in (solve env uu____20530))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____20531); FStar_Syntax_Syntax.pos = uu____20532; FStar_Syntax_Syntax.vars = uu____20533}, uu____20534), uu____20535) -> begin
(

let uu____20572 = (attempt ((FStar_TypeChecker_Common.TProb (problem))::[]) wl)
in (solve env uu____20572))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____20573), uu____20574) -> begin
(

let t21 = (

let uu____20582 = (base_and_refinement env t2)
in (FStar_All.pipe_left force_refinement uu____20582))
in (solve_t env (

let uu___407_20608 = problem
in {FStar_TypeChecker_Common.pid = uu___407_20608.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___407_20608.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___407_20608.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___407_20608.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___407_20608.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___407_20608.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___407_20608.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___407_20608.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___407_20608.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____20609, FStar_Syntax_Syntax.Tm_refine (uu____20610)) -> begin
(

let t11 = (

let uu____20618 = (base_and_refinement env t1)
in (FStar_All.pipe_left force_refinement uu____20618))
in (solve_t env (

let uu___408_20644 = problem
in {FStar_TypeChecker_Common.pid = uu___408_20644.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___408_20644.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___408_20644.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___408_20644.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___408_20644.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___408_20644.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___408_20644.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___408_20644.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___408_20644.FStar_TypeChecker_Common.rank}) wl))
end
| (FStar_Syntax_Syntax.Tm_match (s1, brs1), FStar_Syntax_Syntax.Tm_match (s2, brs2)) -> begin
(

let by_smt = (fun uu____20726 -> (

let uu____20727 = (guard_of_prob env wl problem t1 t2)
in (match (uu____20727) with
| (guard, wl1) -> begin
(

let uu____20734 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl1)
in (solve env uu____20734))
end)))
in (

let rec solve_branches = (fun wl1 brs11 brs21 -> (match (((brs11), (brs21))) with
| ((br1)::rs1, (br2)::rs2) -> begin
(

let uu____20953 = br1
in (match (uu____20953) with
| (p1, w1, uu____20982) -> begin
(

let uu____20999 = br2
in (match (uu____20999) with
| (p2, w2, uu____21022) -> begin
(

let uu____21027 = (

let uu____21028 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (not (uu____21028)))
in (match (uu____21027) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____21051 -> begin
(

let uu____21052 = (FStar_Syntax_Subst.open_branch' br1)
in (match (uu____21052) with
| ((p11, w11, e1), s) -> begin
(

let uu____21089 = br2
in (match (uu____21089) with
| (p21, w21, e2) -> begin
(

let w22 = (FStar_Util.map_opt w21 (FStar_Syntax_Subst.subst s))
in (

let e21 = (FStar_Syntax_Subst.subst s e2)
in (

let scope = (

let uu____21122 = (FStar_Syntax_Syntax.pat_bvs p11)
in (FStar_All.pipe_left (FStar_List.map FStar_Syntax_Syntax.mk_binder) uu____21122))
in (

let uu____21127 = (match (((w11), (w22))) with
| (FStar_Pervasives_Native.Some (uu____21158), FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (uu____21179)) -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.Some ((([]), (wl1)))
end
| (FStar_Pervasives_Native.Some (w12), FStar_Pervasives_Native.Some (w23)) -> begin
(

let uu____21238 = (mk_t_problem wl1 scope orig w12 FStar_TypeChecker_Common.EQ w23 FStar_Pervasives_Native.None "when clause")
in (match (uu____21238) with
| (p, wl2) -> begin
FStar_Pervasives_Native.Some ((((((scope), (p)))::[]), (wl2)))
end))
end)
in (FStar_Util.bind_opt uu____21127 (fun uu____21309 -> (match (uu____21309) with
| (wprobs, wl2) -> begin
(

let uu____21346 = (mk_t_problem wl2 scope orig e1 FStar_TypeChecker_Common.EQ e21 FStar_Pervasives_Native.None "branch body")
in (match (uu____21346) with
| (prob, wl3) -> begin
((

let uu____21366 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl3.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____21366) with
| true -> begin
(

let uu____21367 = (prob_to_string env prob)
in (

let uu____21368 = (FStar_Syntax_Print.binders_to_string ", " scope)
in (FStar_Util.print2 "Created problem for branches %s with scope %s\n" uu____21367 uu____21368)))
end
| uu____21369 -> begin
()
end));
(

let uu____21370 = (solve_branches wl3 rs1 rs2)
in (FStar_Util.bind_opt uu____21370 (fun uu____21406 -> (match (uu____21406) with
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
| uu____21535 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____21576 = (solve_branches wl brs1 brs2)
in (match (uu____21576) with
| FStar_Pervasives_Native.None -> begin
(match (wl.smt_ok) with
| true -> begin
(by_smt ())
end
| uu____21599 -> begin
(giveup env "Tm_match branches don\'t match" orig)
end)
end
| FStar_Pervasives_Native.Some (sub_probs, wl1) -> begin
(

let uu____21624 = (mk_t_problem wl1 [] orig s1 FStar_TypeChecker_Common.EQ s2 FStar_Pervasives_Native.None "match scrutinee")
in (match (uu____21624) with
| (sc_prob, wl2) -> begin
(

let sub_probs1 = ((([]), (sc_prob)))::sub_probs
in (

let formula = (

let uu____21657 = (FStar_List.map (fun uu____21669 -> (match (uu____21669) with
| (scope, p) -> begin
(FStar_TypeChecker_Env.close_forall wl2.tcenv scope (p_guard p))
end)) sub_probs1)
in (FStar_Syntax_Util.mk_conj_l uu____21657))
in (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let wl3 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) [] wl2)
in (

let uu____21678 = (

let uu____21679 = (

let uu____21680 = (FStar_List.map FStar_Pervasives_Native.snd sub_probs1)
in (attempt uu____21680 (

let uu___409_21688 = wl3
in {attempting = uu___409_21688.attempting; wl_deferred = uu___409_21688.wl_deferred; ctr = uu___409_21688.ctr; defer_ok = uu___409_21688.defer_ok; smt_ok = false; umax_heuristic_ok = uu___409_21688.umax_heuristic_ok; tcenv = uu___409_21688.tcenv; wl_implicits = uu___409_21688.wl_implicits})))
in (solve env uu____21679))
in (match (uu____21678) with
| Success (ds, imp) -> begin
((FStar_Syntax_Unionfind.commit tx);
Success (((ds), (imp)));
)
end
| Failed (uu____21692) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(by_smt ());
)
end))))))
end))
end))))
end
| (FStar_Syntax_Syntax.Tm_match (uu____21698), uu____21699) -> begin
(

let head1 = (

let uu____21723 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____21723 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____21769 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____21769 FStar_Pervasives_Native.fst))
in ((

let uu____21815 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____21815) with
| true -> begin
(

let uu____21816 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____21817 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____21818 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____21816 uu____21817 uu____21818))))
end
| uu____21819 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____21828 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____21828)) && (

let uu____21832 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____21832))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____21848 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____21848 FStar_Syntax_Util.Equal)))))
in (

let uu____21849 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____21849) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____21850 = (equal t1 t2)
in (match (uu____21850) with
| true -> begin
(

let uu____21851 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____21851))
end
| uu____21852 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____21853 -> begin
(

let uu____21854 = (

let uu____21861 = (equal t1 t2)
in (match (uu____21861) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____21870 -> begin
(

let uu____21871 = (mk_eq2 wl env orig t1 t2)
in (match (uu____21871) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____21854) with
| (guard, wl1) -> begin
(

let uu____21892 = (solve_prob orig guard [] wl1)
in (solve env uu____21892))
end))
end)
end
| uu____21893 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____21894), uu____21895) -> begin
(

let head1 = (

let uu____21903 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____21903 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____21949 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____21949 FStar_Pervasives_Native.fst))
in ((

let uu____21995 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____21995) with
| true -> begin
(

let uu____21996 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____21997 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____21998 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____21996 uu____21997 uu____21998))))
end
| uu____21999 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____22008 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____22008)) && (

let uu____22012 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____22012))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____22028 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____22028 FStar_Syntax_Util.Equal)))))
in (

let uu____22029 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____22029) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____22030 = (equal t1 t2)
in (match (uu____22030) with
| true -> begin
(

let uu____22031 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____22031))
end
| uu____22032 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____22033 -> begin
(

let uu____22034 = (

let uu____22041 = (equal t1 t2)
in (match (uu____22041) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____22050 -> begin
(

let uu____22051 = (mk_eq2 wl env orig t1 t2)
in (match (uu____22051) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____22034) with
| (guard, wl1) -> begin
(

let uu____22072 = (solve_prob orig guard [] wl1)
in (solve env uu____22072))
end))
end)
end
| uu____22073 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (FStar_Syntax_Syntax.Tm_name (uu____22074), uu____22075) -> begin
(

let head1 = (

let uu____22077 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22077 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22123 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22123 FStar_Pervasives_Native.fst))
in ((

let uu____22169 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____22169) with
| true -> begin
(

let uu____22170 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22171 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22172 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22170 uu____22171 uu____22172))))
end
| uu____22173 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____22182 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____22182)) && (

let uu____22186 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____22186))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____22202 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____22202 FStar_Syntax_Util.Equal)))))
in (

let uu____22203 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____22203) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____22204 = (equal t1 t2)
in (match (uu____22204) with
| true -> begin
(

let uu____22205 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____22205))
end
| uu____22206 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____22207 -> begin
(

let uu____22208 = (

let uu____22215 = (equal t1 t2)
in (match (uu____22215) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____22224 -> begin
(

let uu____22225 = (mk_eq2 wl env orig t1 t2)
in (match (uu____22225) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____22208) with
| (guard, wl1) -> begin
(

let uu____22246 = (solve_prob orig guard [] wl1)
in (solve env uu____22246))
end))
end)
end
| uu____22247 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (FStar_Syntax_Syntax.Tm_constant (uu____22248), uu____22249) -> begin
(

let head1 = (

let uu____22251 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22251 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22297 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22297 FStar_Pervasives_Native.fst))
in ((

let uu____22343 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____22343) with
| true -> begin
(

let uu____22344 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22345 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22346 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22344 uu____22345 uu____22346))))
end
| uu____22347 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____22356 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____22356)) && (

let uu____22360 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____22360))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____22376 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____22376 FStar_Syntax_Util.Equal)))))
in (

let uu____22377 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____22377) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____22378 = (equal t1 t2)
in (match (uu____22378) with
| true -> begin
(

let uu____22379 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____22379))
end
| uu____22380 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____22381 -> begin
(

let uu____22382 = (

let uu____22389 = (equal t1 t2)
in (match (uu____22389) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____22398 -> begin
(

let uu____22399 = (mk_eq2 wl env orig t1 t2)
in (match (uu____22399) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____22382) with
| (guard, wl1) -> begin
(

let uu____22420 = (solve_prob orig guard [] wl1)
in (solve env uu____22420))
end))
end)
end
| uu____22421 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____22422), uu____22423) -> begin
(

let head1 = (

let uu____22425 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22425 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22471 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22471 FStar_Pervasives_Native.fst))
in ((

let uu____22517 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____22517) with
| true -> begin
(

let uu____22518 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22519 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22520 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22518 uu____22519 uu____22520))))
end
| uu____22521 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____22530 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____22530)) && (

let uu____22534 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____22534))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____22550 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____22550 FStar_Syntax_Util.Equal)))))
in (

let uu____22551 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____22551) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____22552 = (equal t1 t2)
in (match (uu____22552) with
| true -> begin
(

let uu____22553 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____22553))
end
| uu____22554 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____22555 -> begin
(

let uu____22556 = (

let uu____22563 = (equal t1 t2)
in (match (uu____22563) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____22572 -> begin
(

let uu____22573 = (mk_eq2 wl env orig t1 t2)
in (match (uu____22573) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____22556) with
| (guard, wl1) -> begin
(

let uu____22594 = (solve_prob orig guard [] wl1)
in (solve env uu____22594))
end))
end)
end
| uu____22595 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (FStar_Syntax_Syntax.Tm_app (uu____22596), uu____22597) -> begin
(

let head1 = (

let uu____22615 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22615 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22661 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22661 FStar_Pervasives_Native.fst))
in ((

let uu____22707 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____22707) with
| true -> begin
(

let uu____22708 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22709 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22710 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22708 uu____22709 uu____22710))))
end
| uu____22711 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____22720 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____22720)) && (

let uu____22724 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____22724))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____22740 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____22740 FStar_Syntax_Util.Equal)))))
in (

let uu____22741 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____22741) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____22742 = (equal t1 t2)
in (match (uu____22742) with
| true -> begin
(

let uu____22743 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____22743))
end
| uu____22744 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____22745 -> begin
(

let uu____22746 = (

let uu____22753 = (equal t1 t2)
in (match (uu____22753) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____22762 -> begin
(

let uu____22763 = (mk_eq2 wl env orig t1 t2)
in (match (uu____22763) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____22746) with
| (guard, wl1) -> begin
(

let uu____22784 = (solve_prob orig guard [] wl1)
in (solve env uu____22784))
end))
end)
end
| uu____22785 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (uu____22786, FStar_Syntax_Syntax.Tm_match (uu____22787)) -> begin
(

let head1 = (

let uu____22811 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22811 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22857 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22857 FStar_Pervasives_Native.fst))
in ((

let uu____22903 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____22903) with
| true -> begin
(

let uu____22904 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22905 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22906 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22904 uu____22905 uu____22906))))
end
| uu____22907 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____22916 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____22916)) && (

let uu____22920 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____22920))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____22936 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____22936 FStar_Syntax_Util.Equal)))))
in (

let uu____22937 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____22937) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____22938 = (equal t1 t2)
in (match (uu____22938) with
| true -> begin
(

let uu____22939 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____22939))
end
| uu____22940 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____22941 -> begin
(

let uu____22942 = (

let uu____22949 = (equal t1 t2)
in (match (uu____22949) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____22958 -> begin
(

let uu____22959 = (mk_eq2 wl env orig t1 t2)
in (match (uu____22959) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____22942) with
| (guard, wl1) -> begin
(

let uu____22980 = (solve_prob orig guard [] wl1)
in (solve env uu____22980))
end))
end)
end
| uu____22981 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (uu____22982, FStar_Syntax_Syntax.Tm_uinst (uu____22983)) -> begin
(

let head1 = (

let uu____22991 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22991 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____23031 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____23031 FStar_Pervasives_Native.fst))
in ((

let uu____23071 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____23071) with
| true -> begin
(

let uu____23072 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____23073 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____23074 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____23072 uu____23073 uu____23074))))
end
| uu____23075 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____23084 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____23084)) && (

let uu____23088 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____23088))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____23104 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____23104 FStar_Syntax_Util.Equal)))))
in (

let uu____23105 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____23105) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____23106 = (equal t1 t2)
in (match (uu____23106) with
| true -> begin
(

let uu____23107 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____23107))
end
| uu____23108 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____23109 -> begin
(

let uu____23110 = (

let uu____23117 = (equal t1 t2)
in (match (uu____23117) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____23126 -> begin
(

let uu____23127 = (mk_eq2 wl env orig t1 t2)
in (match (uu____23127) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____23110) with
| (guard, wl1) -> begin
(

let uu____23148 = (solve_prob orig guard [] wl1)
in (solve env uu____23148))
end))
end)
end
| uu____23149 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (uu____23150, FStar_Syntax_Syntax.Tm_name (uu____23151)) -> begin
(

let head1 = (

let uu____23153 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____23153 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____23193 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____23193 FStar_Pervasives_Native.fst))
in ((

let uu____23233 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____23233) with
| true -> begin
(

let uu____23234 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____23235 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____23236 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____23234 uu____23235 uu____23236))))
end
| uu____23237 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____23246 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____23246)) && (

let uu____23250 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____23250))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____23266 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____23266 FStar_Syntax_Util.Equal)))))
in (

let uu____23267 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____23267) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____23268 = (equal t1 t2)
in (match (uu____23268) with
| true -> begin
(

let uu____23269 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____23269))
end
| uu____23270 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____23271 -> begin
(

let uu____23272 = (

let uu____23279 = (equal t1 t2)
in (match (uu____23279) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____23288 -> begin
(

let uu____23289 = (mk_eq2 wl env orig t1 t2)
in (match (uu____23289) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____23272) with
| (guard, wl1) -> begin
(

let uu____23310 = (solve_prob orig guard [] wl1)
in (solve env uu____23310))
end))
end)
end
| uu____23311 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (uu____23312, FStar_Syntax_Syntax.Tm_constant (uu____23313)) -> begin
(

let head1 = (

let uu____23315 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____23315 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____23355 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____23355 FStar_Pervasives_Native.fst))
in ((

let uu____23395 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____23395) with
| true -> begin
(

let uu____23396 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____23397 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____23398 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____23396 uu____23397 uu____23398))))
end
| uu____23399 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____23408 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____23408)) && (

let uu____23412 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____23412))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____23428 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____23428 FStar_Syntax_Util.Equal)))))
in (

let uu____23429 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____23429) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____23430 = (equal t1 t2)
in (match (uu____23430) with
| true -> begin
(

let uu____23431 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____23431))
end
| uu____23432 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____23433 -> begin
(

let uu____23434 = (

let uu____23441 = (equal t1 t2)
in (match (uu____23441) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____23450 -> begin
(

let uu____23451 = (mk_eq2 wl env orig t1 t2)
in (match (uu____23451) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____23434) with
| (guard, wl1) -> begin
(

let uu____23472 = (solve_prob orig guard [] wl1)
in (solve env uu____23472))
end))
end)
end
| uu____23473 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (uu____23474, FStar_Syntax_Syntax.Tm_fvar (uu____23475)) -> begin
(

let head1 = (

let uu____23477 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____23477 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____23517 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____23517 FStar_Pervasives_Native.fst))
in ((

let uu____23557 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____23557) with
| true -> begin
(

let uu____23558 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____23559 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____23560 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____23558 uu____23559 uu____23560))))
end
| uu____23561 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____23570 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____23570)) && (

let uu____23574 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____23574))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____23590 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____23590 FStar_Syntax_Util.Equal)))))
in (

let uu____23591 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____23591) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____23592 = (equal t1 t2)
in (match (uu____23592) with
| true -> begin
(

let uu____23593 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____23593))
end
| uu____23594 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____23595 -> begin
(

let uu____23596 = (

let uu____23603 = (equal t1 t2)
in (match (uu____23603) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____23612 -> begin
(

let uu____23613 = (mk_eq2 wl env orig t1 t2)
in (match (uu____23613) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____23596) with
| (guard, wl1) -> begin
(

let uu____23634 = (solve_prob orig guard [] wl1)
in (solve env uu____23634))
end))
end)
end
| uu____23635 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (uu____23636, FStar_Syntax_Syntax.Tm_app (uu____23637)) -> begin
(

let head1 = (

let uu____23655 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____23655 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____23695 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____23695 FStar_Pervasives_Native.fst))
in ((

let uu____23735 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____23735) with
| true -> begin
(

let uu____23736 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____23737 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____23738 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____23736 uu____23737 uu____23738))))
end
| uu____23739 -> begin
()
end));
(

let no_free_uvars = (fun t -> ((

let uu____23748 = (FStar_Syntax_Free.uvars t)
in (FStar_Util.set_is_empty uu____23748)) && (

let uu____23752 = (FStar_Syntax_Free.univs t)
in (FStar_Util.set_is_empty uu____23752))))
in (

let equal = (fun t11 t21 -> (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::[]) env t21)
in (

let uu____23768 = (FStar_Syntax_Util.eq_tm t12 t22)
in (Prims.op_Equality uu____23768 FStar_Syntax_Util.Equal)))))
in (

let uu____23769 = (((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) && (no_free_uvars t1)) && (no_free_uvars t2))
in (match (uu____23769) with
| true -> begin
(match ((not (wl.smt_ok))) with
| true -> begin
(

let uu____23770 = (equal t1 t2)
in (match (uu____23770) with
| true -> begin
(

let uu____23771 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____23771))
end
| uu____23772 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))
end
| uu____23773 -> begin
(

let uu____23774 = (

let uu____23781 = (equal t1 t2)
in (match (uu____23781) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____23790 -> begin
(

let uu____23791 = (mk_eq2 wl env orig t1 t2)
in (match (uu____23791) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____23774) with
| (guard, wl1) -> begin
(

let uu____23812 = (solve_prob orig guard [] wl1)
in (solve env uu____23812))
end))
end)
end
| uu____23813 -> begin
(rigid_rigid_delta env problem wl head1 head2 t1 t2)
end))));
)))
end
| (FStar_Syntax_Syntax.Tm_let (uu____23814), FStar_Syntax_Syntax.Tm_let (uu____23815)) -> begin
(

let uu____23840 = (FStar_Syntax_Util.term_eq t1 t2)
in (match (uu____23840) with
| true -> begin
(

let uu____23841 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____23841))
end
| uu____23842 -> begin
(giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig)
end))
end
| (FStar_Syntax_Syntax.Tm_let (uu____23843), uu____23844) -> begin
(

let uu____23857 = (

let uu____23862 = (

let uu____23863 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____23864 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____23865 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____23866 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)" uu____23863 uu____23864 uu____23865 uu____23866)))))
in ((FStar_Errors.Fatal_UnificationNotWellFormed), (uu____23862)))
in (FStar_Errors.raise_error uu____23857 t1.FStar_Syntax_Syntax.pos))
end
| (uu____23867, FStar_Syntax_Syntax.Tm_let (uu____23868)) -> begin
(

let uu____23881 = (

let uu____23886 = (

let uu____23887 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____23888 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____23889 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____23890 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)" uu____23887 uu____23888 uu____23889 uu____23890)))))
in ((FStar_Errors.Fatal_UnificationNotWellFormed), (uu____23886)))
in (FStar_Errors.raise_error uu____23881 t1.FStar_Syntax_Syntax.pos))
end
| uu____23891 -> begin
(giveup env "head tag mismatch" orig)
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

let solve_eq = (fun c1_comp c2_comp -> ((

let uu____23952 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____23952) with
| true -> begin
(

let uu____23953 = (

let uu____23954 = (FStar_Syntax_Syntax.mk_Comp c1_comp)
in (FStar_Syntax_Print.comp_to_string uu____23954))
in (

let uu____23955 = (

let uu____23956 = (FStar_Syntax_Syntax.mk_Comp c2_comp)
in (FStar_Syntax_Print.comp_to_string uu____23956))
in (FStar_Util.print2 "solve_c is using an equality constraint (%s vs %s)\n" uu____23953 uu____23955)))
end
| uu____23957 -> begin
()
end));
(

let uu____23958 = (

let uu____23959 = (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)
in (not (uu____23959)))
in (match (uu____23958) with
| true -> begin
(

let uu____23960 = (

let uu____23961 = (FStar_Syntax_Print.lid_to_string c1_comp.FStar_Syntax_Syntax.effect_name)
in (

let uu____23962 = (FStar_Syntax_Print.lid_to_string c2_comp.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible effects: %s <> %s" uu____23961 uu____23962)))
in (giveup env uu____23960 orig))
end
| uu____23963 -> begin
(

let uu____23964 = (sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ FStar_TypeChecker_Common.EQ c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type")
in (match (uu____23964) with
| (ret_sub_prob, wl1) -> begin
(

let uu____23971 = (FStar_List.fold_right2 (fun uu____24008 uu____24009 uu____24010 -> (match (((uu____24008), (uu____24009), (uu____24010))) with
| ((a1, uu____24054), (a2, uu____24056), (arg_sub_probs, wl2)) -> begin
(

let uu____24089 = (sub_prob wl2 a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (match (uu____24089) with
| (p, wl3) -> begin
(((p)::arg_sub_probs), (wl3))
end))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args (([]), (wl1)))
in (match (uu____23971) with
| (arg_sub_probs, wl2) -> begin
(

let sub_probs = (ret_sub_prob)::arg_sub_probs
in (

let guard = (

let uu____24118 = (FStar_List.map p_guard sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____24118))
in (

let wl3 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl2)
in (

let uu____24126 = (attempt sub_probs wl3)
in (solve env uu____24126)))))
end))
end))
end));
))
in (

let solve_sub = (fun c11 edge c21 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let lift_c1 = (fun uu____24149 -> (

let wp = (match (c11.FStar_Syntax_Syntax.effect_args) with
| ((wp1, uu____24152))::[] -> begin
wp1
end
| uu____24177 -> begin
(

let uu____24188 = (

let uu____24189 = (

let uu____24190 = (FStar_Ident.range_of_lid c11.FStar_Syntax_Syntax.effect_name)
in (FStar_Range.string_of_range uu____24190))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" uu____24189))
in (failwith uu____24188))
end)
in (

let univs1 = (match (c11.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
(

let uu____24196 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (uu____24196)::[])
end
| x -> begin
x
end)
in (

let uu____24198 = (

let uu____24209 = (

let uu____24218 = (

let uu____24219 = (FStar_List.hd univs1)
in (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp uu____24219 c11.FStar_Syntax_Syntax.result_typ wp))
in (FStar_Syntax_Syntax.as_arg uu____24218))
in (uu____24209)::[])
in {FStar_Syntax_Syntax.comp_univs = univs1; FStar_Syntax_Syntax.effect_name = c21.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c11.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____24198; FStar_Syntax_Syntax.flags = c11.FStar_Syntax_Syntax.flags}))))
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____24236 = (lift_c1 ())
in (solve_eq uu____24236 c21))
end
| uu____24237 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___353_24242 -> (match (uu___353_24242) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| uu____24243 -> begin
false
end))))
in (

let uu____24244 = (match (((c11.FStar_Syntax_Syntax.effect_args), (c21.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____24274))::uu____24275, ((wp2, uu____24277))::uu____24278) -> begin
((wp1), (wp2))
end
| uu____24351 -> begin
(

let uu____24376 = (

let uu____24381 = (

let uu____24382 = (FStar_Syntax_Print.lid_to_string c11.FStar_Syntax_Syntax.effect_name)
in (

let uu____24383 = (FStar_Syntax_Print.lid_to_string c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____24382 uu____24383)))
in ((FStar_Errors.Fatal_ExpectNormalizedEffect), (uu____24381)))
in (FStar_Errors.raise_error uu____24376 env.FStar_TypeChecker_Env.range))
end)
in (match (uu____24244) with
| (wpc1, wpc2) -> begin
(

let uu____24390 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____24390) with
| true -> begin
(

let uu____24393 = (problem_using_guard orig c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ FStar_Pervasives_Native.None "result type")
in (solve_t env uu____24393 wl))
end
| uu____24394 -> begin
(

let uu____24395 = (

let uu____24402 = (FStar_TypeChecker_Env.effect_decl_opt env c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.must uu____24402))
in (match (uu____24395) with
| (c2_decl, qualifiers) -> begin
(

let uu____24423 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____24423) with
| true -> begin
(

let c1_repr = (

let uu____24427 = (

let uu____24428 = (

let uu____24429 = (lift_c1 ())
in (FStar_Syntax_Syntax.mk_Comp uu____24429))
in (

let uu____24430 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____24428 uu____24430)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::[]) env uu____24427))
in (

let c2_repr = (

let uu____24432 = (

let uu____24433 = (FStar_Syntax_Syntax.mk_Comp c21)
in (

let uu____24434 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____24433 uu____24434)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::[]) env uu____24432))
in (

let uu____24435 = (

let uu____24440 = (

let uu____24441 = (FStar_Syntax_Print.term_to_string c1_repr)
in (

let uu____24442 = (FStar_Syntax_Print.term_to_string c2_repr)
in (FStar_Util.format2 "sub effect repr: %s <: %s" uu____24441 uu____24442)))
in (sub_prob wl c1_repr problem.FStar_TypeChecker_Common.relation c2_repr uu____24440))
in (match (uu____24435) with
| (prob, wl1) -> begin
(

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some ((p_guard prob))) [] wl1)
in (

let uu____24446 = (attempt ((prob)::[]) wl2)
in (solve env uu____24446)))
end))))
end
| uu____24447 -> begin
(

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____24453 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____24457 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____24457) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____24458 -> begin
()
end));
(

let c1_univ = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____24460 = (

let uu____24467 = (

let uu____24468 = (

let uu____24485 = (FStar_TypeChecker_Env.inst_effect_fun_with ((c1_univ)::[]) env c2_decl c2_decl.FStar_Syntax_Syntax.trivial)
in (

let uu____24488 = (

let uu____24499 = (FStar_Syntax_Syntax.as_arg c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____24508 = (

let uu____24519 = (

let uu____24528 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c1_univ c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____24528))
in (uu____24519)::[])
in (uu____24499)::uu____24508))
in ((uu____24485), (uu____24488))))
in FStar_Syntax_Syntax.Tm_app (uu____24468))
in (FStar_Syntax_Syntax.mk uu____24467))
in (uu____24460 FStar_Pervasives_Native.None r)));
)
end
| uu____24576 -> begin
(

let c1_univ = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (

let c2_univ = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____24579 = (

let uu____24586 = (

let uu____24587 = (

let uu____24604 = (FStar_TypeChecker_Env.inst_effect_fun_with ((c2_univ)::[]) env c2_decl c2_decl.FStar_Syntax_Syntax.stronger)
in (

let uu____24607 = (

let uu____24618 = (FStar_Syntax_Syntax.as_arg c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____24627 = (

let uu____24638 = (FStar_Syntax_Syntax.as_arg wpc2)
in (

let uu____24647 = (

let uu____24658 = (

let uu____24667 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c1_univ c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____24667))
in (uu____24658)::[])
in (uu____24638)::uu____24647))
in (uu____24618)::uu____24627))
in ((uu____24604), (uu____24607))))
in FStar_Syntax_Syntax.Tm_app (uu____24587))
in (FStar_Syntax_Syntax.mk uu____24586))
in (uu____24579 FStar_Pervasives_Native.None r))))
end)
end)
in ((

let uu____24724 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____24724) with
| true -> begin
(

let uu____24725 = (

let uu____24726 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Simplify)::[]) env g)
in (FStar_Syntax_Print.term_to_string uu____24726))
in (FStar_Util.print1 "WP guard (simplifed) is (%s)\n" uu____24725))
end
| uu____24727 -> begin
()
end));
(

let uu____24728 = (sub_prob wl c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ "result type")
in (match (uu____24728) with
| (base_prob, wl1) -> begin
(

let wl2 = (

let uu____24736 = (

let uu____24739 = (FStar_Syntax_Util.mk_conj (p_guard base_prob) g)
in (FStar_All.pipe_left (fun _0_12 -> FStar_Pervasives_Native.Some (_0_12)) uu____24739))
in (solve_prob orig uu____24736 [] wl1))
in (

let uu____24742 = (attempt ((base_prob)::[]) wl2)
in (solve env uu____24742)))
end));
))
end))
end))
end))
end)))
end))))
in (

let uu____24743 = (FStar_Util.physical_equality c1 c2)
in (match (uu____24743) with
| true -> begin
(

let uu____24744 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____24744))
end
| uu____24745 -> begin
((

let uu____24747 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____24747) with
| true -> begin
(

let uu____24748 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____24749 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____24748 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____24749)))
end
| uu____24750 -> begin
()
end));
(

let uu____24751 = (

let uu____24760 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____24763 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____24760), (uu____24763))))
in (match (uu____24751) with
| (c11, c21) -> begin
(match (((c11.FStar_Syntax_Syntax.n), (c21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____24781), FStar_Syntax_Syntax.Total (t2, uu____24783)) when (FStar_Syntax_Util.non_informative t2) -> begin
(

let uu____24800 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____24800 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____24801), FStar_Syntax_Syntax.Total (uu____24802)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| (FStar_Syntax_Syntax.Total (t1, uu____24820), FStar_Syntax_Syntax.Total (t2, uu____24822)) -> begin
(

let uu____24839 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____24839 wl))
end
| (FStar_Syntax_Syntax.GTotal (t1, uu____24841), FStar_Syntax_Syntax.GTotal (t2, uu____24843)) -> begin
(

let uu____24860 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____24860 wl))
end
| (FStar_Syntax_Syntax.Total (t1, uu____24862), FStar_Syntax_Syntax.GTotal (t2, uu____24864)) -> begin
(

let uu____24881 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____24881 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____24882), FStar_Syntax_Syntax.Comp (uu____24883)) -> begin
(

let uu____24892 = (

let uu___410_24895 = problem
in (

let uu____24898 = (

let uu____24899 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____24899))
in {FStar_TypeChecker_Common.pid = uu___410_24895.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____24898; FStar_TypeChecker_Common.relation = uu___410_24895.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___410_24895.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___410_24895.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___410_24895.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___410_24895.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___410_24895.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___410_24895.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___410_24895.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____24892 wl))
end
| (FStar_Syntax_Syntax.Total (uu____24900), FStar_Syntax_Syntax.Comp (uu____24901)) -> begin
(

let uu____24910 = (

let uu___410_24913 = problem
in (

let uu____24916 = (

let uu____24917 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____24917))
in {FStar_TypeChecker_Common.pid = uu___410_24913.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____24916; FStar_TypeChecker_Common.relation = uu___410_24913.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___410_24913.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___410_24913.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___410_24913.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___410_24913.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___410_24913.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___410_24913.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___410_24913.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____24910 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____24918), FStar_Syntax_Syntax.GTotal (uu____24919)) -> begin
(

let uu____24928 = (

let uu___411_24931 = problem
in (

let uu____24934 = (

let uu____24935 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____24935))
in {FStar_TypeChecker_Common.pid = uu___411_24931.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___411_24931.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___411_24931.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____24934; FStar_TypeChecker_Common.element = uu___411_24931.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___411_24931.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___411_24931.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___411_24931.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___411_24931.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___411_24931.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____24928 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____24936), FStar_Syntax_Syntax.Total (uu____24937)) -> begin
(

let uu____24946 = (

let uu___411_24949 = problem
in (

let uu____24952 = (

let uu____24953 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____24953))
in {FStar_TypeChecker_Common.pid = uu___411_24949.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___411_24949.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___411_24949.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____24952; FStar_TypeChecker_Common.element = uu___411_24949.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___411_24949.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___411_24949.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___411_24949.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___411_24949.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___411_24949.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____24946 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____24954), FStar_Syntax_Syntax.Comp (uu____24955)) -> begin
(

let uu____24956 = ((((FStar_Syntax_Util.is_ml_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) || ((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_total_comp c21))) || (((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB)))
in (match (uu____24956) with
| true -> begin
(

let uu____24957 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c11) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c21) FStar_Pervasives_Native.None "result type")
in (solve_t env uu____24957 wl))
end
| uu____24958 -> begin
(

let c1_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (

let c2_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____24961 = (

let uu____24966 = (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)
in (match (uu____24966) with
| true -> begin
((c1_comp), (c2_comp))
end
| uu____24971 -> begin
(

let uu____24972 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let uu____24973 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((uu____24972), (uu____24973))))
end))
in (match (uu____24961) with
| (c1_comp1, c2_comp1) -> begin
(solve_eq c1_comp1 c2_comp1)
end))
end
| uu____24976 -> begin
(

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((

let uu____24980 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____24980) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c12.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c22.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____24981 -> begin
()
end));
(

let uu____24982 = (FStar_TypeChecker_Env.monad_leq env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____24982) with
| FStar_Pervasives_Native.None -> begin
(

let uu____24985 = (

let uu____24986 = (FStar_Syntax_Print.lid_to_string c12.FStar_Syntax_Syntax.effect_name)
in (

let uu____24987 = (FStar_Syntax_Print.lid_to_string c22.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____24986 uu____24987)))
in (giveup env uu____24985 orig))
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
end)))))))))


let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (

let uu____24994 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun i -> (FStar_Syntax_Print.term_to_string i.FStar_TypeChecker_Env.imp_tm))))
in (FStar_All.pipe_right uu____24994 (FStar_String.concat ", "))))


let ineqs_to_string : (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.string = (fun ineqs -> (

let vars = (

let uu____25035 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs) (FStar_List.map FStar_Syntax_Print.univ_to_string))
in (FStar_All.pipe_right uu____25035 (FStar_String.concat ", ")))
in (

let ineqs1 = (

let uu____25053 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs) (FStar_List.map (fun uu____25081 -> (match (uu____25081) with
| (u1, u2) -> begin
(

let uu____25088 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____25089 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "%s < %s" uu____25088 uu____25089)))
end))))
in (FStar_All.pipe_right uu____25053 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred), (g.FStar_TypeChecker_Env.univ_ineqs))) with
| (FStar_TypeChecker_Common.Trivial, [], (uu____25116, [])) when (

let uu____25141 = (FStar_Options.print_implicits ())
in (not (uu____25141))) -> begin
"{}"
end
| uu____25142 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____25165 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)) || (FStar_Options.print_implicits ()))
in (match (uu____25165) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____25166 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____25168 = (FStar_List.map (fun uu____25178 -> (match (uu____25178) with
| (uu____25183, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right uu____25168 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (

let uu____25188 = (ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs)
in (FStar_Util.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n" form carry uu____25188 imps)))))
end))


let new_t_problem : worklist  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  (FStar_TypeChecker_Common.prob * worklist) = (fun wl env lhs rel rhs elt loc -> (

let reason = (

let uu____25241 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))))
in (match (uu____25241) with
| true -> begin
(

let uu____25242 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____25243 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____25242 (rel_to_string rel) uu____25243)))
end
| uu____25244 -> begin
"TOP"
end))
in (

let uu____25245 = (new_problem wl env lhs rel rhs elt loc reason)
in (match (uu____25245) with
| (p, wl1) -> begin
((def_check_prob (Prims.strcat "new_t_problem." reason) (FStar_TypeChecker_Common.TProb (p)));
((FStar_TypeChecker_Common.TProb (p)), (wl1));
)
end))))


let new_t_prob : worklist  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv * worklist) = (fun wl env t1 rel t2 -> (

let x = (

let uu____25303 = (

let uu____25306 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_13 -> FStar_Pervasives_Native.Some (_0_13)) uu____25306))
in (FStar_Syntax_Syntax.new_bv uu____25303 t1))
in (

let uu____25309 = (

let uu____25314 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some (x)) uu____25314))
in (match (uu____25309) with
| (p, wl1) -> begin
((p), (x), (wl1))
end))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits) FStar_Pervasives_Native.option)  ->  (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits) FStar_Pervasives_Native.option = (fun env probs err -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let sol = (solve env probs)
in (match (sol) with
| Success (deferred, implicits) -> begin
((FStar_Syntax_Unionfind.commit tx);
FStar_Pervasives_Native.Some (((deferred), (implicits)));
)
end
| Failed (d, s) -> begin
((

let uu____25387 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))))
in (match (uu____25387) with
| true -> begin
(

let uu____25388 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____25388))
end
| uu____25389 -> begin
()
end));
(

let result = (err ((d), (s)))
in ((FStar_Syntax_Unionfind.rollback tx);
result;
));
)
end))))


let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
((

let uu____25410 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____25410) with
| true -> begin
(

let uu____25411 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____25411))
end
| uu____25412 -> begin
()
end));
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.NoFullNorm)::[]) env f)
in ((

let uu____25415 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____25415) with
| true -> begin
(

let uu____25416 = (FStar_Syntax_Print.term_to_string f1)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____25416))
end
| uu____25417 -> begin
()
end));
(

let f2 = (

let uu____25419 = (

let uu____25420 = (FStar_Syntax_Util.unmeta f1)
in uu____25420.FStar_Syntax_Syntax.n)
in (match (uu____25419) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____25424 -> begin
FStar_TypeChecker_Common.NonTrivial (f1)
end))
in (

let uu___412_25425 = g
in {FStar_TypeChecker_Env.guard_f = f2; FStar_TypeChecker_Env.deferred = uu___412_25425.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___412_25425.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___412_25425.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicit Prims.list) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (deferred, implicits) -> begin
(

let uu____25479 = (

let uu____25480 = (

let uu____25481 = (FStar_All.pipe_right (p_guard prob) (fun _0_14 -> FStar_TypeChecker_Common.NonTrivial (_0_14)))
in {FStar_TypeChecker_Env.guard_f = uu____25481; FStar_TypeChecker_Env.deferred = deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = implicits})
in (simplify_guard env uu____25480))
in (FStar_All.pipe_left (fun _0_15 -> FStar_Pervasives_Native.Some (_0_15)) uu____25479))
end))


let with_guard_no_simp : 'Auu____25496 . 'Auu____25496  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____25519 = (

let uu____25520 = (FStar_All.pipe_right (p_guard prob) (fun _0_16 -> FStar_TypeChecker_Common.NonTrivial (_0_16)))
in {FStar_TypeChecker_Env.guard_f = uu____25520; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in FStar_Pervasives_Native.Some (uu____25519))
end))


let try_teq : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun smt_ok env t1 t2 -> ((

let uu____25550 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____25550) with
| true -> begin
(

let uu____25551 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____25552 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" uu____25551 uu____25552)))
end
| uu____25553 -> begin
()
end));
(

let uu____25554 = (

let uu____25559 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None uu____25559))
in (match (uu____25554) with
| (prob, wl) -> begin
(

let g = (

let uu____25567 = (solve_and_commit env (singleton wl prob smt_ok) (fun uu____25577 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob) uu____25567))
in g)
end));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____25611 = (try_teq true env t1 t2)
in (match (uu____25611) with
| FStar_Pervasives_Native.None -> begin
((

let uu____25615 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____25616 = (FStar_TypeChecker_Err.basic_type_error env FStar_Pervasives_Native.None t2 t1)
in (FStar_Errors.log_issue uu____25615 uu____25616)));
FStar_TypeChecker_Env.trivial_guard;
)
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____25623 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____25623) with
| true -> begin
(

let uu____25624 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____25625 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____25626 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____25624 uu____25625 uu____25626))))
end
| uu____25627 -> begin
()
end));
g;
)
end)))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun env e t1 t2 -> (

let uu____25648 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____25649 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t2 t1)
in (FStar_Errors.log_issue uu____25648 uu____25649))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env c1 c2 -> (

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____25672 -> begin
FStar_TypeChecker_Common.SUB
end)
in ((

let uu____25674 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____25674) with
| true -> begin
(

let uu____25675 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____25676 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n" uu____25675 uu____25676 (match ((Prims.op_Equality rel FStar_TypeChecker_Common.EQ)) with
| true -> begin
"EQ"
end
| uu____25677 -> begin
"SUB"
end))))
end
| uu____25678 -> begin
()
end));
(

let uu____25679 = (

let uu____25686 = (FStar_TypeChecker_Env.get_range env)
in (new_problem (empty_worklist env) env c1 rel c2 FStar_Pervasives_Native.None uu____25686 "sub_comp"))
in (match (uu____25679) with
| (prob, wl) -> begin
(

let prob1 = FStar_TypeChecker_Common.CProb (prob)
in ((def_check_prob "sub_comp" prob1);
(

let uu____25697 = (solve_and_commit env (singleton wl prob1 true) (fun uu____25707 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob1) uu____25697));
))
end));
)))


let solve_universe_inequalities' : FStar_Syntax_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  unit = (fun tx env uu____25752 -> (match (uu____25752) with
| (variables, ineqs) -> begin
(

let fail1 = (fun u1 u2 -> ((FStar_Syntax_Unionfind.rollback tx);
(

let uu____25795 = (

let uu____25800 = (

let uu____25801 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____25802 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Universe %s and %s are incompatible" uu____25801 uu____25802)))
in ((FStar_Errors.Fatal_IncompatibleUniverse), (uu____25800)))
in (

let uu____25803 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____25795 uu____25803)));
))
in (

let equiv1 = (fun v1 v' -> (

let uu____25815 = (

let uu____25820 = (FStar_Syntax_Subst.compress_univ v1)
in (

let uu____25821 = (FStar_Syntax_Subst.compress_univ v')
in ((uu____25820), (uu____25821))))
in (match (uu____25815) with
| (FStar_Syntax_Syntax.U_unif (v0), FStar_Syntax_Syntax.U_unif (v0')) -> begin
(FStar_Syntax_Unionfind.univ_equiv v0 v0')
end
| uu____25840 -> begin
false
end)))
in (

let sols = (FStar_All.pipe_right variables (FStar_List.collect (fun v1 -> (

let uu____25870 = (FStar_Syntax_Subst.compress_univ v1)
in (match (uu____25870) with
| FStar_Syntax_Syntax.U_unif (uu____25877) -> begin
(

let lower_bounds_of_v = (FStar_All.pipe_right ineqs (FStar_List.collect (fun uu____25906 -> (match (uu____25906) with
| (u, v') -> begin
(

let uu____25915 = (equiv1 v1 v')
in (match (uu____25915) with
| true -> begin
(

let uu____25918 = (FStar_All.pipe_right variables (FStar_Util.for_some (equiv1 u)))
in (match (uu____25918) with
| true -> begin
[]
end
| uu____25923 -> begin
(u)::[]
end))
end
| uu____25924 -> begin
[]
end))
end))))
in (

let lb = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max (lower_bounds_of_v)))
in (((lb), (v1)))::[]))
end
| uu____25934 -> begin
[]
end)))))
in (

let uu____25939 = (

let wl = (

let uu___413_25943 = (empty_worklist env)
in {attempting = uu___413_25943.attempting; wl_deferred = uu___413_25943.wl_deferred; ctr = uu___413_25943.ctr; defer_ok = false; smt_ok = uu___413_25943.smt_ok; umax_heuristic_ok = uu___413_25943.umax_heuristic_ok; tcenv = uu___413_25943.tcenv; wl_implicits = uu___413_25943.wl_implicits})
in (FStar_All.pipe_right sols (FStar_List.map (fun uu____25961 -> (match (uu____25961) with
| (lb, v1) -> begin
(

let uu____25968 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl lb v1)
in (match (uu____25968) with
| USolved (wl1) -> begin
()
end
| uu____25970 -> begin
(fail1 lb v1)
end))
end)))))
in (

let rec check_ineq = (fun uu____25980 -> (match (uu____25980) with
| (u, v1) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u)
in (

let v2 = (FStar_TypeChecker_Normalize.normalize_universe env v1)
in (match (((u1), (v2))) with
| (FStar_Syntax_Syntax.U_zero, uu____25989) -> begin
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
| (FStar_Syntax_Syntax.U_name (uu____26012), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_unif (uu____26014), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_max (us), uu____26025) -> begin
(FStar_All.pipe_right us (FStar_Util.for_all (fun u2 -> (check_ineq ((u2), (v2))))))
end
| (uu____26032, FStar_Syntax_Syntax.U_max (vs)) -> begin
(FStar_All.pipe_right vs (FStar_Util.for_some (fun v3 -> (check_ineq ((u1), (v3))))))
end
| uu____26040 -> begin
false
end)))
end))
in (

let uu____26045 = (FStar_All.pipe_right ineqs (FStar_Util.for_all (fun uu____26060 -> (match (uu____26060) with
| (u, v1) -> begin
(

let uu____26067 = (check_ineq ((u), (v1)))
in (match (uu____26067) with
| true -> begin
true
end
| uu____26068 -> begin
((

let uu____26070 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____26070) with
| true -> begin
(

let uu____26071 = (FStar_Syntax_Print.univ_to_string u)
in (

let uu____26072 = (FStar_Syntax_Print.univ_to_string v1)
in (FStar_Util.print2 "%s </= %s" uu____26071 uu____26072)))
end
| uu____26073 -> begin
()
end));
false;
)
end))
end))))
in (match (uu____26045) with
| true -> begin
()
end
| uu____26074 -> begin
((

let uu____26076 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____26076) with
| true -> begin
((

let uu____26078 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Partially solved inequality constraints are: %s\n" uu____26078));
(FStar_Syntax_Unionfind.rollback tx);
(

let uu____26088 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Original solved inequality constraints are: %s\n" uu____26088));
)
end
| uu____26097 -> begin
()
end));
(

let uu____26098 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_FailToSolveUniverseInEquality), ("Failed to solve universe inequalities for inductives")) uu____26098));
)
end)))))))
end))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  unit = (fun env ineqs -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Syntax_Unionfind.commit tx);
)))


let try_solve_deferred_constraints : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun defer_ok env g -> (

let fail1 = (fun uu____26165 -> (match (uu____26165) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ErrorInSolveDeferredConstraints), (msg)) (p_loc d)))
end))
in (

let wl = (

let uu___414_26186 = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in {attempting = uu___414_26186.attempting; wl_deferred = uu___414_26186.wl_deferred; ctr = uu___414_26186.ctr; defer_ok = defer_ok; smt_ok = uu___414_26186.smt_ok; umax_heuristic_ok = uu___414_26186.umax_heuristic_ok; tcenv = uu___414_26186.tcenv; wl_implicits = uu___414_26186.wl_implicits})
in ((

let uu____26188 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____26188) with
| true -> begin
(

let uu____26189 = (FStar_Util.string_of_bool defer_ok)
in (

let uu____26190 = (wl_to_string wl)
in (

let uu____26191 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print3 "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n" uu____26189 uu____26190 uu____26191))))
end
| uu____26192 -> begin
()
end));
(

let g1 = (

let uu____26194 = (solve_and_commit env wl fail1)
in (match (uu____26194) with
| FStar_Pervasives_Native.Some ((uu____26201)::uu____26202, uu____26203) when (not (defer_ok)) -> begin
(failwith "Impossible: Unexpected deferred constraints remain")
end
| FStar_Pervasives_Native.Some (deferred, imps) -> begin
(

let uu___415_26228 = g
in {FStar_TypeChecker_Env.guard_f = uu___415_26228.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = deferred; FStar_TypeChecker_Env.univ_ineqs = uu___415_26228.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)})
end
| uu____26229 -> begin
(failwith "Impossible: should have raised a failure already")
end))
in ((solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___416_26237 = g1
in {FStar_TypeChecker_Env.guard_f = uu___416_26237.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___416_26237.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = uu___416_26237.FStar_TypeChecker_Env.implicits});
));
))))


let solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (try_solve_deferred_constraints false env g))


let solve_some_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (try_solve_deferred_constraints true env g))


let last_proof_ns : FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let maybe_update_proof_ns : FStar_TypeChecker_Env.env  ->  unit = (fun env -> (

let pns = env.FStar_TypeChecker_Env.proof_ns
in (

let uu____26285 = (FStar_ST.op_Bang last_proof_ns)
in (match (uu____26285) with
| FStar_Pervasives_Native.None -> begin
(FStar_ST.op_Colon_Equals last_proof_ns (FStar_Pervasives_Native.Some (pns)))
end
| FStar_Pervasives_Native.Some (old) -> begin
(match ((Prims.op_Equality old pns)) with
| true -> begin
()
end
| uu____26335 -> begin
((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(FStar_ST.op_Colon_Equals last_proof_ns (FStar_Pervasives_Native.Some (pns)));
)
end)
end))))


let discharge_guard' : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun use_env_range_msg env g use_smt -> (

let debug1 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTQuery")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Tac"))))
in (

let g1 = (solve_deferred_constraints env g)
in (

let ret_g = (

let uu___417_26396 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___417_26396.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___417_26396.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___417_26396.FStar_TypeChecker_Env.implicits})
in (

let uu____26397 = (

let uu____26398 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____26398)))
in (match (uu____26397) with
| true -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| uu____26401 -> begin
(match (g1.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((match (debug1) with
| true -> begin
(

let uu____26406 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____26407 = (

let uu____26408 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____26408))
in (FStar_Errors.diag uu____26406 uu____26407)))
end
| uu____26409 -> begin
()
end);
(

let vc1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.Primops)::[]) env vc)
in ((match (debug1) with
| true -> begin
(

let uu____26412 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____26413 = (

let uu____26414 = (FStar_Syntax_Print.term_to_string vc1)
in (FStar_Util.format1 "After normalization VC=\n%s\n" uu____26414))
in (FStar_Errors.diag uu____26412 uu____26413)))
end
| uu____26415 -> begin
()
end);
(

let uu____26417 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Env.def_check_closed_in_env uu____26417 "discharge_guard\'" env vc1));
(

let uu____26418 = (FStar_TypeChecker_Env.check_trivial vc1)
in (match (uu____26418) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc2) -> begin
(match ((not (use_smt))) with
| true -> begin
((match (debug1) with
| true -> begin
(

let uu____26425 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____26426 = (

let uu____26427 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Cannot solve without SMT : %s\n" uu____26427))
in (FStar_Errors.diag uu____26425 uu____26426)))
end
| uu____26428 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end
| uu____26429 -> begin
((match (debug1) with
| true -> begin
(

let uu____26432 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____26433 = (

let uu____26434 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____26434))
in (FStar_Errors.diag uu____26432 uu____26433)))
end
| uu____26435 -> begin
()
end);
(

let vcs = (

let uu____26445 = (FStar_Options.use_tactics ())
in (match (uu____26445) with
| true -> begin
(FStar_Options.with_saved_options (fun uu____26465 -> ((

let uu____26467 = (FStar_Options.set_options FStar_Options.Set "--no_tactics")
in (FStar_All.pipe_left (fun a1 -> ()) uu____26467));
(

let vcs = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.preprocess env vc2)
in (FStar_All.pipe_right vcs (FStar_List.map (fun uu____26510 -> (match (uu____26510) with
| (env1, goal, opts) -> begin
(

let uu____26526 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.Primops)::[]) env1 goal)
in ((env1), (uu____26526), (opts)))
end)))));
)))
end
| uu____26527 -> begin
(

let uu____26528 = (

let uu____26535 = (FStar_Options.peek ())
in ((env), (vc2), (uu____26535)))
in (uu____26528)::[])
end))
in (FStar_All.pipe_right vcs (FStar_List.iter (fun uu____26568 -> (match (uu____26568) with
| (env1, goal, opts) -> begin
(

let uu____26578 = (FStar_TypeChecker_Env.check_trivial goal)
in (match (uu____26578) with
| FStar_TypeChecker_Common.Trivial -> begin
(match (debug1) with
| true -> begin
(FStar_Util.print_string "Goal completely solved by tactic\n")
end
| uu____26580 -> begin
()
end)
end
| FStar_TypeChecker_Common.NonTrivial (goal1) -> begin
((FStar_Options.push ());
(FStar_Options.set opts);
(maybe_update_proof_ns env1);
(match (debug1) with
| true -> begin
(

let uu____26586 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____26587 = (

let uu____26588 = (FStar_Syntax_Print.term_to_string goal1)
in (

let uu____26589 = (FStar_TypeChecker_Env.string_of_proof_ns env1)
in (FStar_Util.format2 "Trying to solve:\n> %s\nWith proof_ns:\n %s\n" uu____26588 uu____26589)))
in (FStar_Errors.diag uu____26586 uu____26587)))
end
| uu____26590 -> begin
()
end);
(match (debug1) with
| true -> begin
(

let uu____26592 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____26593 = (

let uu____26594 = (FStar_Syntax_Print.term_to_string goal1)
in (FStar_Util.format1 "Before calling solver VC=\n%s\n" uu____26594))
in (FStar_Errors.diag uu____26592 uu____26593)))
end
| uu____26595 -> begin
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


let discharge_guard_no_smt : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let uu____26608 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____26608) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____26615 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ExpectTrivialPreCondition), ("Expected a trivial pre-condition")) uu____26615))
end)))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let uu____26626 = (discharge_guard' FStar_Pervasives_Native.None env g true)
in (match (uu____26626) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end)))


let teq_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> (

let uu____26652 = (try_teq false env t1 t2)
in (match (uu____26652) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (g) -> begin
(discharge_guard' FStar_Pervasives_Native.None env g false)
end)))


let resolve_implicits' : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env must_total forcelax g -> (

let unresolved = (fun ctx_u -> (

let uu____26687 = (FStar_Syntax_Unionfind.find ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____26687) with
| FStar_Pervasives_Native.Some (uu____26690) -> begin
false
end
| FStar_Pervasives_Native.None -> begin
true
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____26710 = acc
in (match (uu____26710) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____26717 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd1)::tl1 -> begin
(

let uu____26722 = hd1
in (match (uu____26722) with
| {FStar_TypeChecker_Env.imp_reason = reason; FStar_TypeChecker_Env.imp_uvar = ctx_u; FStar_TypeChecker_Env.imp_tm = tm; FStar_TypeChecker_Env.imp_range = r; FStar_TypeChecker_Env.imp_meta = uu____26727} -> begin
(match ((Prims.op_Equality ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check FStar_Syntax_Syntax.Allow_unresolved)) with
| true -> begin
(until_fixpoint ((out), (true)) tl1)
end
| uu____26734 -> begin
(

let uu____26735 = (unresolved ctx_u)
in (match (uu____26735) with
| true -> begin
(match (hd1.FStar_TypeChecker_Env.imp_meta) with
| FStar_Pervasives_Native.None -> begin
(until_fixpoint (((hd1)::out), (changed)) tl1)
end
| FStar_Pervasives_Native.Some (env1, tau) -> begin
((

let uu____26747 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("Tac")))
in (match (uu____26747) with
| true -> begin
(

let uu____26748 = (FStar_Syntax_Print.ctx_uvar_to_string ctx_u)
in (FStar_Util.print1 "Running tactic for meta-arg %s\n" uu____26748))
end
| uu____26749 -> begin
()
end));
(

let t = (env1.FStar_TypeChecker_Env.synth_hook env1 hd1.FStar_TypeChecker_Env.imp_uvar.FStar_Syntax_Syntax.ctx_uvar_typ tau)
in (

let extra = (

let uu____26754 = (teq_nosmt env1 t tm)
in (match (uu____26754) with
| FStar_Pervasives_Native.None -> begin
(failwith "resolve_implicits: unifying with an unresolved uvar failed?")
end
| FStar_Pervasives_Native.Some (g1) -> begin
g1.FStar_TypeChecker_Env.implicits
end))
in (

let hd2 = (

let uu___418_26763 = hd1
in {FStar_TypeChecker_Env.imp_reason = uu___418_26763.FStar_TypeChecker_Env.imp_reason; FStar_TypeChecker_Env.imp_uvar = uu___418_26763.FStar_TypeChecker_Env.imp_uvar; FStar_TypeChecker_Env.imp_tm = uu___418_26763.FStar_TypeChecker_Env.imp_tm; FStar_TypeChecker_Env.imp_range = uu___418_26763.FStar_TypeChecker_Env.imp_range; FStar_TypeChecker_Env.imp_meta = FStar_Pervasives_Native.None})
in (until_fixpoint ((out), (true)) ((hd2)::(FStar_List.append extra tl1))))));
)
end)
end
| uu____26768 -> begin
(match ((Prims.op_Equality ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check FStar_Syntax_Syntax.Allow_untyped)) with
| true -> begin
(until_fixpoint ((out), (true)) tl1)
end
| uu____26769 -> begin
(

let env1 = (

let uu___419_26771 = env
in {FStar_TypeChecker_Env.solver = uu___419_26771.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___419_26771.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___419_26771.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_TypeChecker_Env.gamma_sig = uu___419_26771.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___419_26771.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___419_26771.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___419_26771.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___419_26771.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___419_26771.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___419_26771.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___419_26771.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___419_26771.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___419_26771.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___419_26771.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___419_26771.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___419_26771.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___419_26771.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___419_26771.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___419_26771.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___419_26771.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___419_26771.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___419_26771.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___419_26771.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___419_26771.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___419_26771.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___419_26771.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___419_26771.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___419_26771.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___419_26771.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___419_26771.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___419_26771.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___419_26771.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___419_26771.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___419_26771.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___419_26771.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___419_26771.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___419_26771.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___419_26771.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___419_26771.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___419_26771.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___419_26771.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___419_26771.FStar_TypeChecker_Env.nbe})
in (

let tm1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env1 tm)
in (

let env2 = (match (forcelax) with
| true -> begin
(

let uu___420_26774 = env1
in {FStar_TypeChecker_Env.solver = uu___420_26774.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___420_26774.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___420_26774.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___420_26774.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___420_26774.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___420_26774.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___420_26774.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___420_26774.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___420_26774.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___420_26774.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___420_26774.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___420_26774.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___420_26774.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___420_26774.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___420_26774.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___420_26774.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___420_26774.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___420_26774.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___420_26774.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___420_26774.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___420_26774.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___420_26774.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___420_26774.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___420_26774.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___420_26774.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___420_26774.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___420_26774.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___420_26774.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___420_26774.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___420_26774.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___420_26774.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___420_26774.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___420_26774.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___420_26774.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___420_26774.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___420_26774.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___420_26774.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___420_26774.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___420_26774.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___420_26774.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___420_26774.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___420_26774.FStar_TypeChecker_Env.nbe})
end
| uu____26775 -> begin
env1
end)
in ((

let uu____26777 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____26777) with
| true -> begin
(

let uu____26778 = (FStar_Syntax_Print.uvar_to_string ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____26779 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____26780 = (FStar_Syntax_Print.term_to_string ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (

let uu____26781 = (FStar_Range.string_of_range r)
in (FStar_Util.print5 "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n" uu____26778 uu____26779 uu____26780 reason uu____26781)))))
end
| uu____26782 -> begin
()
end));
(

let g1 = (FStar_All.try_with (fun uu___422_26785 -> (match (()) with
| () -> begin
(env2.FStar_TypeChecker_Env.check_type_of must_total env2 tm1 ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
end)) (fun uu___421_26789 -> (match (uu___421_26789) with
| e when (FStar_Errors.handleable e) -> begin
((

let uu____26792 = (

let uu____26801 = (

let uu____26808 = (

let uu____26809 = (FStar_Syntax_Print.uvar_to_string ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____26810 = (FStar_TypeChecker_Normalize.term_to_string env2 tm1)
in (

let uu____26811 = (FStar_TypeChecker_Normalize.term_to_string env2 ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format3 "Failed while checking implicit %s set to %s of expected type %s" uu____26809 uu____26810 uu____26811))))
in ((FStar_Errors.Error_BadImplicit), (uu____26808), (r)))
in (uu____26801)::[])
in (FStar_Errors.add_errors uu____26792));
(FStar_Exn.raise e);
)
end)))
in (

let g2 = (match (env2.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___423_26825 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___423_26825.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___423_26825.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___423_26825.FStar_TypeChecker_Env.implicits})
end
| uu____26826 -> begin
g1
end)
in (

let g' = (

let uu____26828 = (discharge_guard' (FStar_Pervasives_Native.Some ((fun uu____26838 -> (

let uu____26839 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____26840 = (FStar_Range.string_of_range r)
in (

let uu____26841 = (FStar_Range.string_of_range tm1.FStar_Syntax_Syntax.pos)
in (FStar_Util.format4 "%s (Introduced at %s for %s resolved at %s)" uu____26839 uu____26840 reason uu____26841))))))) env2 g2 true)
in (match (uu____26828) with
| FStar_Pervasives_Native.Some (g3) -> begin
g3
end
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end))
in (until_fixpoint (((FStar_List.append g'.FStar_TypeChecker_Env.implicits out)), (true)) tl1))));
))))
end)
end))
end)
end))
end)
end)))
in (

let uu___424_26843 = g
in (

let uu____26844 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___424_26843.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___424_26843.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___424_26843.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____26844})))))


let resolve_implicits : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (resolve_implicits' env true false g))


let resolve_implicits_tac : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (resolve_implicits' env false true g))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  unit = (fun env g -> (

let g1 = (

let uu____26878 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____26878 (resolve_implicits env)))
in (match (g1.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(

let uu____26879 = (discharge_guard env g1)
in (FStar_All.pipe_left (fun a2 -> ()) uu____26879))
end
| (imp)::uu____26881 -> begin
(

let uu____26884 = (

let uu____26889 = (

let uu____26890 = (FStar_Syntax_Print.uvar_to_string imp.FStar_TypeChecker_Env.imp_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____26891 = (FStar_TypeChecker_Normalize.term_to_string env imp.FStar_TypeChecker_Env.imp_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format3 "Failed to resolve implicit argument %s of type %s introduced for %s" uu____26890 uu____26891 imp.FStar_TypeChecker_Env.imp_reason)))
in ((FStar_Errors.Fatal_FailToResolveImplicitArgument), (uu____26889)))
in (FStar_Errors.raise_error uu____26884 imp.FStar_TypeChecker_Env.imp_range))
end)))


let teq_nosmt_force : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____26907 = (teq_nosmt env t1 t2)
in (match (uu____26907) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g) -> begin
((force_trivial_guard env g);
true;
)
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___425_26922 = FStar_TypeChecker_Env.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___425_26922.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___425_26922.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ((((u1), (u2)))::[])); FStar_TypeChecker_Env.implicits = uu___425_26922.FStar_TypeChecker_Env.implicits}))


let check_subtyping : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.option = (fun env t1 t2 -> ((

let uu____26957 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____26957) with
| true -> begin
(

let uu____26958 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____26959 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "check_subtyping of %s and %s\n" uu____26958 uu____26959)))
end
| uu____26960 -> begin
()
end));
(

let uu____26961 = (new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____26961) with
| (prob, x, wl) -> begin
(

let g = (

let uu____26980 = (solve_and_commit env (singleton wl prob true) (fun uu____26990 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob) uu____26980))
in ((

let uu____27010 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____27010) with
| true -> begin
(

let uu____27011 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____27012 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____27013 = (

let uu____27014 = (FStar_Util.must g)
in (guard_to_string env uu____27014))
in (FStar_Util.print3 "check_subtyping succeeded: %s <: %s\n\tguard is %s\n" uu____27011 uu____27012 uu____27013))))
end
| uu____27015 -> begin
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


let get_subtyping_predicate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> (

let uu____27048 = (check_subtyping env t1 t2)
in (match (uu____27048) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (x, g) -> begin
(

let uu____27067 = (

let uu____27068 = (FStar_Syntax_Syntax.mk_binder x)
in (FStar_TypeChecker_Env.abstract_guard uu____27068 g))
in FStar_Pervasives_Native.Some (uu____27067))
end)))


let get_subtyping_prop : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> (

let uu____27086 = (check_subtyping env t1 t2)
in (match (uu____27086) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (x, g) -> begin
(

let uu____27105 = (

let uu____27106 = (

let uu____27107 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____27107)::[])
in (FStar_TypeChecker_Env.close_guard env uu____27106 g))
in FStar_Pervasives_Native.Some (uu____27105))
end)))


let subtype_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> ((

let uu____27144 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____27144) with
| true -> begin
(

let uu____27145 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____27146 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____27145 uu____27146)))
end
| uu____27147 -> begin
()
end));
(

let uu____27148 = (new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____27148) with
| (prob, x, wl) -> begin
(

let g = (

let uu____27163 = (solve_and_commit env (singleton wl prob false) (fun uu____27173 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob) uu____27163))
in (match (g) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (g1) -> begin
(

let g2 = (

let uu____27196 = (

let uu____27197 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____27197)::[])
in (FStar_TypeChecker_Env.close_guard env uu____27196 g1))
in (discharge_guard' FStar_Pervasives_Native.None env g2 false))
end))
end));
))


let subtype_nosmt_force : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____27234 = (subtype_nosmt env t1 t2)
in (match (uu____27234) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g) -> begin
((force_trivial_guard env g);
true;
)
end)))





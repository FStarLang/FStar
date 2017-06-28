
open Prims
open FStar_Pervasives

let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu____23; FStar_TypeChecker_Env.implicits = uu____24} -> begin
true
end
| uu____38 -> begin
false
end))


let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []}


let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun x g -> (match (g) with
| FStar_Pervasives_Native.None -> begin
g
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu____61; FStar_TypeChecker_Env.univ_ineqs = uu____62; FStar_TypeChecker_Env.implicits = uu____63}) -> begin
g
end
| FStar_Pervasives_Native.Some (g1) -> begin
(

let f = (match (g1.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| uu____78 -> begin
(failwith "impossible")
end)
in (

let uu____79 = (

let uu___135_80 = g1
in (

let uu____81 = (

let uu____82 = (

let uu____83 = (

let uu____84 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____84)::[])
in (FStar_Syntax_Util.abs uu____83 f (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0)))))
in (FStar_All.pipe_left (fun _0_39 -> FStar_TypeChecker_Common.NonTrivial (_0_39)) uu____82))
in {FStar_TypeChecker_Env.guard_f = uu____81; FStar_TypeChecker_Env.deferred = uu___135_80.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___135_80.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___135_80.FStar_TypeChecker_Env.implicits}))
in FStar_Pervasives_Native.Some (uu____79)))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___136_94 = g
in (

let uu____95 = (

let uu____96 = (

let uu____97 = (

let uu____100 = (

let uu____101 = (

let uu____111 = (

let uu____113 = (FStar_Syntax_Syntax.as_arg e)
in (uu____113)::[])
in ((f), (uu____111)))
in FStar_Syntax_Syntax.Tm_app (uu____101))
in (FStar_Syntax_Syntax.mk uu____100))
in (uu____97 (FStar_Pervasives_Native.Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _0_40 -> FStar_TypeChecker_Common.NonTrivial (_0_40)) uu____96))
in {FStar_TypeChecker_Env.guard_f = uu____95; FStar_TypeChecker_Env.deferred = uu___136_94.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___136_94.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___136_94.FStar_TypeChecker_Env.implicits}))
end))


let map_guard : FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  FStar_TypeChecker_Env.guard_t = (fun g map1 -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___137_137 = g
in (

let uu____138 = (

let uu____139 = (map1 f)
in FStar_TypeChecker_Common.NonTrivial (uu____139))
in {FStar_TypeChecker_Env.guard_f = uu____138; FStar_TypeChecker_Env.deferred = uu___137_137.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___137_137.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___137_137.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____144) -> begin
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

let uu____157 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (uu____157))
end))


let check_trivial : FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (

let uu____162 = (

let uu____163 = (FStar_Syntax_Util.unmeta t)
in uu____163.FStar_Syntax_Syntax.n)
in (match (uu____162) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____167 -> begin
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


let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (

let uu____203 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = uu____203; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (((FStar_List.append (FStar_Pervasives_Native.fst g1.FStar_TypeChecker_Env.univ_ineqs) (FStar_Pervasives_Native.fst g2.FStar_TypeChecker_Env.univ_ineqs))), ((FStar_List.append (FStar_Pervasives_Native.snd g1.FStar_TypeChecker_Env.univ_ineqs) (FStar_Pervasives_Native.snd g2.FStar_TypeChecker_Env.univ_ineqs)))); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard_univs : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun us bs g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let f1 = (FStar_List.fold_right2 (fun u b f1 -> (

let uu____259 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____259) with
| true -> begin
f1
end
| uu____260 -> begin
(FStar_Syntax_Util.mk_forall u (FStar_Pervasives_Native.fst b) f1)
end))) us bs f)
in (

let uu___138_261 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.NonTrivial (f1); FStar_TypeChecker_Env.deferred = uu___138_261.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___138_261.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___138_261.FStar_TypeChecker_Env.implicits}))
end))


let close_forall : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____281 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____281) with
| true -> begin
f1
end
| uu____282 -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Util.mk_forall u (FStar_Pervasives_Native.fst b) f1))
end))) bs f))


let close_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___139_297 = g
in (

let uu____298 = (

let uu____299 = (close_forall env binders f)
in FStar_TypeChecker_Common.NonTrivial (uu____299))
in {FStar_TypeChecker_Env.guard_f = uu____298; FStar_TypeChecker_Env.deferred = uu___139_297.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___139_297.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___139_297.FStar_TypeChecker_Env.implicits}))
end))


let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (

let uv = (FStar_Syntax_Unionfind.fresh ())
in (match (binders) with
| [] -> begin
(

let uv1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k)))) (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) r)
in ((uv1), (uv1)))
end
| uu____330 -> begin
(

let args = (FStar_All.pipe_right binders (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder))
in (

let k' = (

let uu____345 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders uu____345))
in (

let uv1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k')))) FStar_Pervasives_Native.None r)
in (

let uu____357 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((uv1), (args)))) (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) r)
in ((uu____357), (uv1))))))
end)))


let mk_eq2 : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t1 t2 -> (

let uu____389 = (FStar_Syntax_Util.type_u ())
in (match (uu____389) with
| (t_type, u) -> begin
(

let uu____394 = (

let uu____397 = (FStar_TypeChecker_Env.all_binders env)
in (new_uvar t1.FStar_Syntax_Syntax.pos uu____397 t_type))
in (match (uu____394) with
| (tt, uu____399) -> begin
(FStar_Syntax_Util.mk_eq2 u tt t1 t2)
end))
end)))

type uvi =
| TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)


let uu___is_TERM : uvi  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TERM (_0) -> begin
true
end
| uu____423 -> begin
false
end))


let __proj__TERM__item___0 : uvi  ->  ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| TERM (_0) -> begin
_0
end))


let uu___is_UNIV : uvi  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UNIV (_0) -> begin
true
end
| uu____451 -> begin
false
end))


let __proj__UNIV__item___0 : uvi  ->  (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe) = (fun projectee -> (match (projectee) with
| UNIV (_0) -> begin
_0
end))

type worklist =
{attempting : FStar_TypeChecker_Common.probs; wl_deferred : (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list; ctr : Prims.int; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_TypeChecker_Env.env}


let __proj__Mkworklist__item__attempting : worklist  ->  FStar_TypeChecker_Common.probs = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv} -> begin
__fname__attempting
end))


let __proj__Mkworklist__item__wl_deferred : worklist  ->  (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv} -> begin
__fname__wl_deferred
end))


let __proj__Mkworklist__item__ctr : worklist  ->  Prims.int = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv} -> begin
__fname__ctr
end))


let __proj__Mkworklist__item__defer_ok : worklist  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv} -> begin
__fname__defer_ok
end))


let __proj__Mkworklist__item__smt_ok : worklist  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv} -> begin
__fname__smt_ok
end))


let __proj__Mkworklist__item__tcenv : worklist  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv} -> begin
__fname__tcenv
end))

type solution =
| Success of FStar_TypeChecker_Common.deferred
| Failed of (FStar_TypeChecker_Common.prob * Prims.string)


let uu___is_Success : solution  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
true
end
| uu____601 -> begin
false
end))


let __proj__Success__item___0 : solution  ->  FStar_TypeChecker_Common.deferred = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
_0
end))


let uu___is_Failed : solution  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Failed (_0) -> begin
true
end
| uu____617 -> begin
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
| uu____636 -> begin
false
end))


let uu___is_CONTRAVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CONTRAVARIANT -> begin
true
end
| uu____641 -> begin
false
end))


let uu___is_INVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| INVARIANT -> begin
true
end
| uu____646 -> begin
false
end))


type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem


type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem


type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun uu___107_662 -> (match (uu___107_662) with
| FStar_TypeChecker_Common.EQ -> begin
"="
end
| FStar_TypeChecker_Common.SUB -> begin
"<:"
end
| FStar_TypeChecker_Common.SUBINV -> begin
":>"
end))


let term_to_string = (fun env t -> (

let uu____678 = (

let uu____679 = (FStar_Syntax_Subst.compress t)
in uu____679.FStar_Syntax_Syntax.n)
in (match (uu____678) with
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let uu____700 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____701 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s:%s)" uu____700 uu____701)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty); FStar_Syntax_Syntax.tk = uu____704; FStar_Syntax_Syntax.pos = uu____705; FStar_Syntax_Syntax.vars = uu____706}, args) -> begin
(

let uu____738 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____739 = (FStar_Syntax_Print.term_to_string ty)
in (

let uu____740 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "(%s:%s) %s" uu____738 uu____739 uu____740))))
end
| uu____741 -> begin
(FStar_Syntax_Print.term_to_string t)
end)))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env uu___108_749 -> (match (uu___108_749) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____753 = (

let uu____755 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____756 = (

let uu____758 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____759 = (

let uu____761 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (

let uu____762 = (

let uu____764 = (

let uu____766 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (

let uu____767 = (

let uu____769 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (

let uu____770 = (

let uu____772 = (FStar_TypeChecker_Normalize.term_to_string env (FStar_Pervasives_Native.fst p.FStar_TypeChecker_Common.logical_guard))
in (

let uu____773 = (

let uu____775 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (uu____775)::[])
in (uu____772)::uu____773))
in (uu____769)::uu____770))
in (uu____766)::uu____767))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::uu____764)
in (uu____761)::uu____762))
in (uu____758)::uu____759))
in (uu____755)::uu____756))
in (FStar_Util.format "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" uu____753))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____780 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____781 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____780 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____781)))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env uu___109_789 -> (match (uu___109_789) with
| UNIV (u, t) -> begin
(

let x = (

let uu____793 = (FStar_Options.hide_uvar_nums ())
in (match (uu____793) with
| true -> begin
"?"
end
| uu____794 -> begin
(

let uu____795 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____795 FStar_Util.string_of_int))
end))
in (

let uu____796 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x uu____796)))
end
| TERM ((u, uu____798), t) -> begin
(

let x = (

let uu____803 = (FStar_Options.hide_uvar_nums ())
in (match (uu____803) with
| true -> begin
"?"
end
| uu____804 -> begin
(

let uu____805 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____805 FStar_Util.string_of_int))
end))
in (

let uu____806 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x uu____806)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (

let uu____817 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right uu____817 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (

let uu____826 = (

let uu____828 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right uu____828 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right uu____826 (FStar_String.concat ", "))))


let args_to_string = (fun args -> (

let uu____848 = (FStar_All.pipe_right args (FStar_List.map (fun uu____859 -> (match (uu____859) with
| (x, uu____863) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____848 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> (

let uu____869 = (

let uu____870 = (FStar_Options.eager_inference ())
in (not (uu____870)))
in {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = uu____869; smt_ok = true; tcenv = env}))


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let uu___140_886 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = uu___140_886.wl_deferred; ctr = uu___140_886.ctr; defer_ok = uu___140_886.defer_ok; smt_ok = smt_ok; tcenv = uu___140_886.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard = (fun env g -> (

let uu___141_916 = (empty_worklist env)
in (

let uu____917 = (FStar_List.map FStar_Pervasives_Native.snd g)
in {attempting = uu____917; wl_deferred = uu___141_916.wl_deferred; ctr = uu___141_916.ctr; defer_ok = false; smt_ok = uu___141_916.smt_ok; tcenv = uu___141_916.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu___142_932 = wl
in {attempting = uu___142_932.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = uu___142_932.ctr; defer_ok = uu___142_932.defer_ok; smt_ok = uu___142_932.smt_ok; tcenv = uu___142_932.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let uu___143_946 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = uu___143_946.wl_deferred; ctr = uu___143_946.ctr; defer_ok = uu___143_946.defer_ok; smt_ok = uu___143_946.smt_ok; tcenv = uu___143_946.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> ((

let uu____960 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____960) with
| true -> begin
(

let uu____961 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason uu____961))
end
| uu____962 -> begin
()
end));
Failed (((prob), (reason)));
))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun uu___110_966 -> (match (uu___110_966) with
| FStar_TypeChecker_Common.EQ -> begin
FStar_TypeChecker_Common.EQ
end
| FStar_TypeChecker_Common.SUB -> begin
FStar_TypeChecker_Common.SUBINV
end
| FStar_TypeChecker_Common.SUBINV -> begin
FStar_TypeChecker_Common.SUB
end))


let invert = (fun p -> (

let uu___144_985 = p
in {FStar_TypeChecker_Common.pid = uu___144_985.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = uu___144_985.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___144_985.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___144_985.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___144_985.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___144_985.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___144_985.FStar_TypeChecker_Common.rank}))


let maybe_invert = (fun p -> (match ((p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV)) with
| true -> begin
(invert p)
end
| uu____1006 -> begin
p
end))


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___111_1010 -> (match (uu___111_1010) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_41 -> FStar_TypeChecker_Common.TProb (_0_41)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_42 -> FStar_TypeChecker_Common.CProb (_0_42)))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel uu___112_1028 -> (match (uu___112_1028) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun uu___113_1032 -> (match (uu___113_1032) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun uu___114_1042 -> (match (uu___114_1042) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun uu___115_1053 -> (match (uu___115_1053) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun uu___116_1064 -> (match (uu___116_1064) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun uu___117_1076 -> (match (uu___117_1076) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun uu___118_1088 -> (match (uu___118_1088) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___119_1098 -> (match (uu___119_1098) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _0_43 -> FStar_TypeChecker_Common.TProb (_0_43)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _0_44 -> FStar_TypeChecker_Common.CProb (_0_44)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> (

let uu____1113 = (FStar_All.pipe_right (p_reason p) FStar_List.length)
in (uu____1113 = (Prims.parse_int "1"))))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____1129 -> ((FStar_Util.incr ctr);
(FStar_ST.read ctr);
)))


let mk_problem = (fun scope orig lhs rel rhs elt reason -> (

let uu____1188 = (next_pid ())
in (

let uu____1189 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____1188; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____1189; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})))


let new_problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (

let uu____1245 = (next_pid ())
in (

let uu____1246 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____1245; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____1246; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (

let uu____1295 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____1295; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None}))


let guard_on_element = (fun wl problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| FStar_Pervasives_Native.None -> begin
(

let u = (wl.tcenv.FStar_TypeChecker_Env.universe_of wl.tcenv x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Util.mk_forall u x phi))
end
| FStar_Pervasives_Native.Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (

let uu____1355 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____1355) with
| true -> begin
(

let uu____1356 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (

let uu____1357 = (prob_to_string env d)
in (

let uu____1358 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" uu____1356 uu____1357 uu____1358 s))))
end
| uu____1360 -> begin
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
| uu____1363 -> begin
(failwith "impossible")
end)
in (

let uu____1364 = (match (d1) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____1372 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (

let uu____1373 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((uu____1372), (uu____1373))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____1377 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (

let uu____1378 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((uu____1377), (uu____1378))))
end)
in (match (uu____1364) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___120_1392 -> (match (uu___120_1392) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Syntax_Unionfind.univ_union u u')
end
| uu____1400 -> begin
(FStar_Syntax_Unionfind.univ_change u t)
end)
end
| TERM ((u, uu____1402), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : FStar_Syntax_Syntax.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun uv s -> (FStar_Util.find_map s (fun uu___121_1419 -> (match (uu___121_1419) with
| UNIV (uu____1421) -> begin
FStar_Pervasives_Native.None
end
| TERM ((u, uu____1425), t) -> begin
(

let uu____1429 = (FStar_Syntax_Unionfind.equiv uv u)
in (match (uu____1429) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____1431 -> begin
FStar_Pervasives_Native.None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe_uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun u s -> (FStar_Util.find_map s (fun uu___122_1447 -> (match (uu___122_1447) with
| UNIV (u', t) -> begin
(

let uu____1451 = (FStar_Syntax_Unionfind.univ_equiv u u')
in (match (uu____1451) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____1453 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____1454 -> begin
FStar_Pervasives_Native.None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1463 = (

let uu____1464 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____1464))
in (FStar_Syntax_Subst.compress uu____1463)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1473 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress uu____1473)))


let norm_arg = (fun env t -> (

let uu____1495 = (sn env (FStar_Pervasives_Native.fst t))
in ((uu____1495), ((FStar_Pervasives_Native.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____1518 -> (match (uu____1518) with
| (x, imp) -> begin
(

let uu____1525 = (

let uu___145_1526 = x
in (

let uu____1527 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___145_1526.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___145_1526.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1527}))
in ((uu____1525), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____1544 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____1544))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1547 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____1547))
end
| uu____1549 -> begin
u2
end)))
in (

let uu____1550 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1550))))


let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement = (fun env wl t1 -> (

let rec aux = (fun norm t11 -> (match (t11.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(match (norm) with
| true -> begin
((x.FStar_Syntax_Syntax.sort), (FStar_Pervasives_Native.Some (((x), (phi)))))
end
| uu____1665 -> begin
(

let uu____1666 = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (match (uu____1666) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x1, phi1); FStar_Syntax_Syntax.tk = uu____1678; FStar_Syntax_Syntax.pos = uu____1679; FStar_Syntax_Syntax.vars = uu____1680} -> begin
((x1.FStar_Syntax_Syntax.sort), (FStar_Pervasives_Native.Some (((x1), (phi1)))))
end
| tt -> begin
(

let uu____1701 = (

let uu____1702 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____1703 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1702 uu____1703)))
in (failwith uu____1701))
end))
end)
end
| FStar_Syntax_Syntax.Tm_uinst (uu____1713) -> begin
(match (norm) with
| true -> begin
((t11), (FStar_Pervasives_Native.None))
end
| uu____1738 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (

let uu____1740 = (

let uu____1741 = (FStar_Syntax_Subst.compress t1')
in uu____1741.FStar_Syntax_Syntax.n)
in (match (uu____1740) with
| FStar_Syntax_Syntax.Tm_refine (uu____1753) -> begin
(aux true t1')
end
| uu____1758 -> begin
((t11), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1770) -> begin
(match (norm) with
| true -> begin
((t11), (FStar_Pervasives_Native.None))
end
| uu____1791 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (

let uu____1793 = (

let uu____1794 = (FStar_Syntax_Subst.compress t1')
in uu____1794.FStar_Syntax_Syntax.n)
in (match (uu____1793) with
| FStar_Syntax_Syntax.Tm_refine (uu____1806) -> begin
(aux true t1')
end
| uu____1811 -> begin
((t11), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_app (uu____1823) -> begin
(match (norm) with
| true -> begin
((t11), (FStar_Pervasives_Native.None))
end
| uu____1853 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (

let uu____1855 = (

let uu____1856 = (FStar_Syntax_Subst.compress t1')
in uu____1856.FStar_Syntax_Syntax.n)
in (match (uu____1855) with
| FStar_Syntax_Syntax.Tm_refine (uu____1868) -> begin
(aux true t1')
end
| uu____1873 -> begin
((t11), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_type (uu____1885) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_constant (uu____1897) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_name (uu____1909) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1921) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1933) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_abs (uu____1952) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1973) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_let (uu____1995) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_match (uu____2014) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_meta (uu____2040) -> begin
(

let uu____2045 = (

let uu____2046 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____2047 = (FStar_Syntax_Print.tag_of_term t11)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2046 uu____2047)))
in (failwith uu____2045))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____2057) -> begin
(

let uu____2075 = (

let uu____2076 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____2077 = (FStar_Syntax_Print.tag_of_term t11)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2076 uu____2077)))
in (failwith uu____2075))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____2087) -> begin
(

let uu____2102 = (

let uu____2103 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____2104 = (FStar_Syntax_Print.tag_of_term t11)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2103 uu____2104)))
in (failwith uu____2102))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____2114 = (

let uu____2115 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____2116 = (FStar_Syntax_Print.tag_of_term t11)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2115 uu____2116)))
in (failwith uu____2114))
end))
in (

let uu____2126 = (whnf env t1)
in (aux false uu____2126))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____2137 = (

let uu____2147 = (empty_worklist env)
in (base_and_refinement env uu____2147 t))
in (FStar_All.pipe_right uu____2137 FStar_Pervasives_Native.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (

let uu____2172 = (FStar_Syntax_Syntax.null_bv t)
in ((uu____2172), (FStar_Syntax_Util.t_true))))


let as_refinement = (fun env wl t -> (

let uu____2196 = (base_and_refinement env wl t)
in (match (uu____2196) with
| (t_base, refinement) -> begin
(match (refinement) with
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end
| FStar_Pervasives_Native.Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement = (fun uu____2257 -> (match (uu____2257) with
| (t_base, refopt) -> begin
(

let uu____2271 = (match (refopt) with
| FStar_Pervasives_Native.Some (y, phi) -> begin
((y), (phi))
end
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end)
in (match (uu____2271) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl uu___123_2297 -> (match (uu___123_2297) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____2301 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____2302 = (

let uu____2303 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string uu____2303))
in (

let uu____2304 = (

let uu____2305 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string uu____2305))
in (FStar_Util.format4 "%s: %s  (%s)  %s" uu____2301 uu____2302 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2304))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____2309 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____2310 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____2311 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" uu____2309 uu____2310 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2311))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (

let uu____2316 = (

let uu____2318 = (

let uu____2320 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____2334 -> (match (uu____2334) with
| (uu____2338, uu____2339, x) -> begin
x
end))))
in (FStar_List.append wl.attempting uu____2320))
in (FStar_List.map (wl_prob_to_string wl) uu____2318))
in (FStar_All.pipe_right uu____2316 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____2360 = (

let uu____2370 = (

let uu____2371 = (FStar_Syntax_Subst.compress k)
in uu____2371.FStar_Syntax_Syntax.n)
in (match (uu____2370) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (((FStar_List.length bs) = (FStar_List.length ys))) with
| true -> begin
(

let uu____2416 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (uu____2416)))
end
| uu____2429 -> begin
(

let uu____2430 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____2430) with
| (ys', t1, uu____2446) -> begin
(

let uu____2449 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t1))), (uu____2449)))
end))
end)
end
| uu____2470 -> begin
(

let uu____2471 = (

let uu____2477 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____2477)))
in ((((ys), (t))), (uu____2471)))
end))
in (match (uu____2360) with
| ((ys1, t1), (xs, c)) -> begin
(match (((FStar_List.length xs) <> (FStar_List.length ys1))) with
| true -> begin
(FStar_Syntax_Util.abs ys1 t1 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None []))))
end
| uu____2527 -> begin
(

let c1 = (

let uu____2529 = (FStar_Syntax_Util.rename_binders xs ys1)
in (FStar_Syntax_Subst.subst_comp uu____2529 c))
in (FStar_Syntax_Util.abs ys1 t1 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c1)))))
end)
end)))


let solve_prob' : Prims.bool  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun resolve_ok prob logical_guard uvis wl -> (

let phi = (match (logical_guard) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Util.t_true
end
| FStar_Pervasives_Native.Some (phi) -> begin
phi
end)
in (

let uu____2557 = (p_guard prob)
in (match (uu____2557) with
| (uu____2560, uv) -> begin
((

let uu____2563 = (

let uu____2564 = (FStar_Syntax_Subst.compress uv)
in uu____2564.FStar_Syntax_Syntax.n)
in (match (uu____2563) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi1 = (u_abs k bs phi)
in ((

let uu____2588 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____2588) with
| true -> begin
(

let uu____2589 = (FStar_Util.string_of_int (p_pid prob))
in (

let uu____2590 = (FStar_Syntax_Print.term_to_string uv)
in (

let uu____2591 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" uu____2589 uu____2590 uu____2591))))
end
| uu____2592 -> begin
()
end));
(FStar_Syntax_Util.set_uvar uvar phi1);
)))
end
| uu____2593 -> begin
(match ((not (resolve_ok))) with
| true -> begin
(failwith "Impossible: this instance has already been assigned a solution")
end
| uu____2594 -> begin
()
end)
end));
(commit uvis);
(

let uu___146_2596 = wl
in {attempting = uu___146_2596.attempting; wl_deferred = uu___146_2596.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___146_2596.defer_ok; smt_ok = uu___146_2596.smt_ok; tcenv = uu___146_2596.tcenv});
)
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____2612 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____2612) with
| true -> begin
(

let uu____2613 = (FStar_Util.string_of_int pid)
in (

let uu____2614 = (

let uu____2615 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right uu____2615 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____2613 uu____2614)))
end
| uu____2618 -> begin
()
end));
(commit sol);
(

let uu___147_2620 = wl
in {attempting = uu___147_2620.attempting; wl_deferred = uu___147_2620.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___147_2620.defer_ok; smt_ok = uu___147_2620.smt_ok; tcenv = uu___147_2620.tcenv});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard1 = (fun t g -> (match (((t), (g))) with
| (uu____2653, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (FStar_Pervasives_Native.None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
FStar_Pervasives_Native.Some (f)
end
| (FStar_Pervasives_Native.Some (t1), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(

let uu____2661 = (FStar_Syntax_Util.mk_conj t1 f)
in FStar_Pervasives_Native.Some (uu____2661))
end))
in ((

let uu____2667 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____2667) with
| true -> begin
(

let uu____2668 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (

let uu____2669 = (

let uu____2670 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right uu____2670 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____2668 uu____2669)))
end
| uu____2673 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
)))


let rec occurs = (fun wl uk t -> (

let uu____2699 = (

let uu____2703 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right uu____2703 FStar_Util.set_elements))
in (FStar_All.pipe_right uu____2699 (FStar_Util.for_some (fun uu____2723 -> (match (uu____2723) with
| (uv, uu____2727) -> begin
(FStar_Syntax_Unionfind.equiv uv (FStar_Pervasives_Native.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (

let uu____2766 = (occurs wl uk t)
in (not (uu____2766)))
in (

let msg = (match (occurs_ok) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____2770 -> begin
(

let uu____2771 = (

let uu____2772 = (FStar_Syntax_Print.uvar_to_string (FStar_Pervasives_Native.fst uk))
in (

let uu____2773 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" uu____2772 uu____2773)))
in FStar_Pervasives_Native.Some (uu____2771))
end)
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let uu____2828 = (occurs_check env wl uk t)
in (match (uu____2828) with
| (occurs_ok, msg) -> begin
(

let uu____2845 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (uu____2845), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set1 = (fun v3 -> (FStar_All.pipe_right v3 (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set1 v1)
in (

let uu____2915 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____2946 uu____2947 -> (match (((uu____2946), (uu____2947))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____2990 = (

let uu____2991 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation uu____2991))
in (match (uu____2990) with
| true -> begin
((isect), (isect_set))
end
| uu____3002 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____3005 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____3005) with
| true -> begin
(

let uu____3012 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (uu____3012)))
end
| uu____3020 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (uu____2915) with
| (isect, uu____3034) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____3097 uu____3098 -> (match (((uu____3097), (uu____3098))) with
| ((a, uu____3108), (b, uu____3110)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd1 = (norm_arg env arg)
in (match ((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(

let uu____3159 = (FStar_All.pipe_right seen (FStar_Util.for_some (fun uu____3168 -> (match (uu____3168) with
| (b, uu____3172) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end))))
in (match (uu____3159) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3178 -> begin
FStar_Pervasives_Native.Some (((a), ((FStar_Pervasives_Native.snd hd1))))
end))
end
| uu____3181 -> begin
FStar_Pervasives_Native.None
end)))


let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option = (fun env seen args -> (match (args) with
| [] -> begin
FStar_Pervasives_Native.Some ((FStar_List.rev seen))
end
| (hd1)::rest -> begin
(

let uu____3226 = (pat_var_opt env seen hd1)
in (match (uu____3226) with
| FStar_Pervasives_Native.None -> begin
((

let uu____3234 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____3234) with
| true -> begin
(

let uu____3235 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (FStar_Pervasives_Native.fst hd1))
in (FStar_Util.print1 "Not a pattern: %s\n" uu____3235))
end
| uu____3236 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end))
end))


let is_flex : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____3248 = (

let uu____3249 = (FStar_Syntax_Subst.compress t)
in uu____3249.FStar_Syntax_Syntax.n)
in (match (uu____3248) with
| FStar_Syntax_Syntax.Tm_uvar (uu____3252) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____3263); FStar_Syntax_Syntax.tk = uu____3264; FStar_Syntax_Syntax.pos = uu____3265; FStar_Syntax_Syntax.vars = uu____3266}, uu____3267) -> begin
true
end
| uu____3292 -> begin
false
end)))


let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = uu____3364; FStar_Syntax_Syntax.pos = uu____3365; FStar_Syntax_Syntax.vars = uu____3366}, args) -> begin
((t), (uv), (k), (args))
end
| uu____3413 -> begin
(failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let uu____3474 = (destruct_flex_t t)
in (match (uu____3474) with
| (t1, uv, k, args) -> begin
(

let uu____3550 = (pat_vars env [] args)
in (match (uu____3550) with
| FStar_Pervasives_Native.Some (vars) -> begin
((((t1), (uv), (k), (args))), (FStar_Pervasives_Native.Some (vars)))
end
| uu____3612 -> begin
((((t1), (uv), (k), (args))), (FStar_Pervasives_Native.None))
end))
end)))

type match_result =
| MisMatch of (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
| HeadMatch
| FullMatch


let uu___is_MisMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MisMatch (_0) -> begin
true
end
| uu____3666 -> begin
false
end))


let __proj__MisMatch__item___0 : match_result  ->  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| MisMatch (_0) -> begin
_0
end))


let uu___is_HeadMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HeadMatch -> begin
true
end
| uu____3691 -> begin
false
end))


let uu___is_FullMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullMatch -> begin
true
end
| uu____3696 -> begin
false
end))


let head_match : match_result  ->  match_result = (fun uu___124_3700 -> (match (uu___124_3700) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____3709 -> begin
HeadMatch
end))


let fv_delta_depth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.delta_depth = (fun env fv -> (match (fv.FStar_Syntax_Syntax.fv_delta) with
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(match ((env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)) with
| true -> begin
d
end
| uu____3719 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
end
| FStar_Syntax_Syntax.Delta_defined_at_level (uu____3720) -> begin
(

let uu____3721 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3721) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Syntax.Delta_constant
end
| uu____3727 -> begin
fv.FStar_Syntax_Syntax.fv_delta
end))
end
| d -> begin
d
end))


let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____3743) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____3749) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3765) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_name (uu____3766) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3767) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_let (uu____3778) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_match (uu____3786) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____3802) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____3808, uu____3809) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____3839) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____3854; FStar_Syntax_Syntax.index = uu____3855; FStar_Syntax_Syntax.sort = t2}, uu____3857) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_constant (uu____3864) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_type (uu____3865) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3866) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_abs (uu____3874) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3885 = (fv_delta_depth env fv)
in FStar_Pervasives_Native.Some (uu____3885))
end)))


let rec head_matches : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  match_result = (fun env t1 t2 -> (

let t11 = (FStar_Syntax_Util.unmeta t1)
in (

let t21 = (FStar_Syntax_Util.unmeta t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_name (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(match ((FStar_Syntax_Syntax.bv_eq x y)) with
| true -> begin
FullMatch
end
| uu____3902 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____3907 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____3907) with
| true -> begin
FullMatch
end
| uu____3908 -> begin
(

let uu____3909 = (

let uu____3914 = (

let uu____3916 = (fv_delta_depth env f)
in FStar_Pervasives_Native.Some (uu____3916))
in (

let uu____3917 = (

let uu____3919 = (fv_delta_depth env g)
in FStar_Pervasives_Native.Some (uu____3919))
in ((uu____3914), (uu____3917))))
in MisMatch (uu____3909))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____3923), FStar_Syntax_Syntax.Tm_uinst (g, uu____3925)) -> begin
(

let uu____3934 = (head_matches env f g)
in (FStar_All.pipe_right uu____3934 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(match ((c = d)) with
| true -> begin
FullMatch
end
| uu____3937 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end)
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, uu____3941), FStar_Syntax_Syntax.Tm_uvar (uv', uu____3943)) -> begin
(

let uu____3976 = (FStar_Syntax_Unionfind.equiv uv uv')
in (match (uu____3976) with
| true -> begin
FullMatch
end
| uu____3977 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____3981), FStar_Syntax_Syntax.Tm_refine (y, uu____3983)) -> begin
(

let uu____3992 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____3992 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____3994), uu____3995) -> begin
(

let uu____4000 = (head_matches env x.FStar_Syntax_Syntax.sort t21)
in (FStar_All.pipe_right uu____4000 head_match))
end
| (uu____4001, FStar_Syntax_Syntax.Tm_refine (x, uu____4003)) -> begin
(

let uu____4008 = (head_matches env t11 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____4008 head_match))
end
| (FStar_Syntax_Syntax.Tm_type (uu____4009), FStar_Syntax_Syntax.Tm_type (uu____4010)) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_arrow (uu____4011), FStar_Syntax_Syntax.Tm_arrow (uu____4012)) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____4028), FStar_Syntax_Syntax.Tm_app (head', uu____4030)) -> begin
(

let uu____4059 = (head_matches env head1 head')
in (FStar_All.pipe_right uu____4059 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____4061), uu____4062) -> begin
(

let uu____4077 = (head_matches env head1 t21)
in (FStar_All.pipe_right uu____4077 head_match))
end
| (uu____4078, FStar_Syntax_Syntax.Tm_app (head1, uu____4080)) -> begin
(

let uu____4095 = (head_matches env t11 head1)
in (FStar_All.pipe_right uu____4095 head_match))
end
| uu____4096 -> begin
(

let uu____4099 = (

let uu____4104 = (delta_depth_of_term env t11)
in (

let uu____4106 = (delta_depth_of_term env t21)
in ((uu____4104), (uu____4106))))
in MisMatch (uu____4099))
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let uu____4147 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____4147) with
| (head1, uu____4159) -> begin
(

let uu____4174 = (

let uu____4175 = (FStar_Syntax_Util.un_uinst head1)
in uu____4175.FStar_Syntax_Syntax.n)
in (match (uu____4174) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____4180 = (

let uu____4181 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____4181 FStar_Option.isSome))
in (match (uu____4180) with
| true -> begin
(

let uu____4191 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right uu____4191 (fun _0_45 -> FStar_Pervasives_Native.Some (_0_45))))
end
| uu____4193 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4194 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (

let success = (fun d r t11 t21 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (((t11), (t21)))
end
| uu____4221 -> begin
FStar_Pervasives_Native.None
end))))
in (

let fail = (fun r -> ((r), (FStar_Pervasives_Native.None)))
in (

let rec aux = (fun retry n_delta t11 t21 -> (

let r = (head_matches env t11 t21)
in (match (r) with
| MisMatch (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational), uu____4262) -> begin
(match ((not (retry))) with
| true -> begin
(fail r)
end
| uu____4271 -> begin
(

let uu____4272 = (

let uu____4277 = (maybe_inline t11)
in (

let uu____4279 = (maybe_inline t21)
in ((uu____4277), (uu____4279))))
in (match (uu____4272) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(fail r)
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
| MisMatch (uu____4300, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational)) -> begin
(match ((not (retry))) with
| true -> begin
(fail r)
end
| uu____4309 -> begin
(

let uu____4310 = (

let uu____4315 = (maybe_inline t11)
in (

let uu____4317 = (maybe_inline t21)
in ((uu____4315), (uu____4317))))
in (match (uu____4310) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(fail r)
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
| MisMatch (FStar_Pervasives_Native.Some (d1), FStar_Pervasives_Native.Some (d2)) when (d1 = d2) -> begin
(

let uu____4342 = (FStar_TypeChecker_Common.decr_delta_depth d1)
in (match (uu____4342) with
| FStar_Pervasives_Native.None -> begin
(fail r)
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let t12 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (

let t22 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t21)
in (aux retry (n_delta + (Prims.parse_int "1")) t12 t22)))
end))
end
| MisMatch (FStar_Pervasives_Native.Some (d1), FStar_Pervasives_Native.Some (d2)) -> begin
(

let d1_greater_than_d2 = (FStar_TypeChecker_Common.delta_depth_greater_than d1 d2)
in (

let uu____4357 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in ((t1'), (t21)))
end
| uu____4363 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t21)
in ((t11), (t2')))
end)
in (match (uu____4357) with
| (t12, t22) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
end)))
end
| MisMatch (uu____4372) -> begin
(fail r)
end
| uu____4377 -> begin
(success n_delta r t11 t21)
end)))
in (aux true (Prims.parse_int "0") t1 t2))))))

type tc =
| T of (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term))
| C of FStar_Syntax_Syntax.comp


let uu___is_T : tc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| T (_0) -> begin
true
end
| uu____4407 -> begin
false
end))


let __proj__T__item___0 : tc  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term)) = (fun projectee -> (match (projectee) with
| T (_0) -> begin
_0
end))


let uu___is_C : tc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C (_0) -> begin
true
end
| uu____4439 -> begin
false
end))


let __proj__C__item___0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_0) -> begin
_0
end))


type tcs =
tc Prims.list


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____4457 = (FStar_Syntax_Util.type_u ())
in (match (uu____4457) with
| (t, uu____4461) -> begin
(

let uu____4462 = (new_uvar r binders t)
in (FStar_Pervasives_Native.fst uu____4462))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____4473 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____4473 FStar_Pervasives_Native.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * variance * tc) Prims.list) = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (

let uu____4517 = (head_matches env t1 t')
in (match (uu____4517) with
| MisMatch (uu____4518) -> begin
false
end
| uu____4523 -> begin
true
end)))
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let rebuild = (fun args' -> (

let args1 = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((uu____4589, imp), T (t2, uu____4592)) -> begin
((t2), (imp))
end
| uu____4609 -> begin
(failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd1), (args1)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun uu____4652 -> (match (uu____4652) with
| (t2, uu____4660) -> begin
((FStar_Pervasives_Native.None), (INVARIANT), (T (((t2), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____4690 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4690) with
| (bs1, c1) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs2 tcs1 -> (match (((bs2), (tcs1))) with
| (((x, imp))::bs3, (T (t2, uu____4743))::tcs2) -> begin
(aux (((((

let uu___148_4766 = x
in {FStar_Syntax_Syntax.ppname = uu___148_4766.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___148_4766.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (imp)))::out) bs3 tcs2)
end
| ([], (C (c2))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c2)
end
| uu____4776 -> begin
(failwith "Bad reconstruction")
end))
in (aux [] bs1 tcs)))
in (

let rec decompose1 = (fun out uu___125_4807 -> (match (uu___125_4807) with
| [] -> begin
(FStar_List.rev ((((FStar_Pervasives_Native.None), (COVARIANT), (C (c1))))::out))
end
| (hd1)::rest -> begin
(decompose1 ((((FStar_Pervasives_Native.Some (hd1)), (CONTRAVARIANT), (T ((((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (

let uu____4870 = (decompose1 [] bs1)
in ((rebuild), (matches), (uu____4870)))))
end))
end
| uu____4898 -> begin
(

let rebuild = (fun uu___126_4903 -> (match (uu___126_4903) with
| [] -> begin
t1
end
| uu____4905 -> begin
(failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t2 -> true)), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun uu___127_4926 -> (match (uu___127_4926) with
| T (t, uu____4928) -> begin
t
end
| uu____4937 -> begin
(failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun uu___128_4941 -> (match (uu___128_4941) with
| T (t, uu____4943) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| uu____4952 -> begin
(failwith "Impossible")
end))


let imitation_sub_probs : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * variance * tc) Prims.list  ->  (FStar_TypeChecker_Common.prob Prims.list * tc Prims.list * FStar_Syntax_Syntax.formula) = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope1 args q -> (match (q) with
| (uu____5026, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope1 r)
in (

let uu____5045 = (new_uvar r scope1 k)
in (match (uu____5045) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| uu____5057 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) FStar_Pervasives_Native.None r)
end)
in (

let uu____5072 = (

let uu____5073 = (mk_problem scope1 orig gi_ps (vary_rel rel variance) ti FStar_Pervasives_Native.None "type subterm")
in (FStar_All.pipe_left (fun _0_46 -> FStar_TypeChecker_Common.TProb (_0_46)) uu____5073))
in ((T (((gi_xs), (mk_kind)))), (uu____5072))))
end)))
end
| (uu____5082, uu____5083, C (uu____5084)) -> begin
(failwith "impos")
end))
in (

let rec aux = (fun scope1 args qs1 -> (match (qs1) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs2 -> begin
(

let uu____5166 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.tk = uu____5177; FStar_Syntax_Syntax.pos = uu____5178; FStar_Syntax_Syntax.vars = uu____5179})) -> begin
(

let uu____5194 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____5194) with
| (T (gi_xs, uu____5210), prob) -> begin
(

let uu____5220 = (

let uu____5221 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_47 -> C (_0_47)) uu____5221))
in ((uu____5220), ((prob)::[])))
end
| uu____5223 -> begin
(failwith "impossible")
end))
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.tk = uu____5233; FStar_Syntax_Syntax.pos = uu____5234; FStar_Syntax_Syntax.vars = uu____5235})) -> begin
(

let uu____5250 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____5250) with
| (T (gi_xs, uu____5266), prob) -> begin
(

let uu____5276 = (

let uu____5277 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_48 -> C (_0_48)) uu____5277))
in ((uu____5276), ((prob)::[])))
end
| uu____5279 -> begin
(failwith "impossible")
end))
end
| (uu____5285, uu____5286, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = uu____5288; FStar_Syntax_Syntax.pos = uu____5289; FStar_Syntax_Syntax.vars = uu____5290})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((FStar_Pervasives_Native.None), (INVARIANT), (T ((((FStar_Pervasives_Native.fst t)), (generic_kind))))))))
in (

let components1 = (((FStar_Pervasives_Native.None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let uu____5365 = (

let uu____5370 = (FStar_List.map (sub_prob scope1 args) components1)
in (FStar_All.pipe_right uu____5370 FStar_List.unzip))
in (match (uu____5365) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (

let uu____5399 = (

let uu____5400 = (

let uu____5403 = (FStar_List.hd tcs)
in (FStar_All.pipe_right uu____5403 un_T))
in (

let uu____5404 = (

let uu____5410 = (FStar_List.tl tcs)
in (FStar_All.pipe_right uu____5410 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____5400; FStar_Syntax_Syntax.effect_args = uu____5404; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____5399))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| uu____5415 -> begin
(

let uu____5422 = (sub_prob scope1 args q)
in (match (uu____5422) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (uu____5166) with
| (tc, probs) -> begin
(

let uu____5440 = (match (q) with
| (FStar_Pervasives_Native.Some (b), uu____5466, uu____5467) -> begin
(

let uu____5475 = (

let uu____5479 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (uu____5479)::args)
in ((FStar_Pervasives_Native.Some (b)), ((b)::scope1), (uu____5475)))
end
| uu____5497 -> begin
((FStar_Pervasives_Native.None), (scope1), (args))
end)
in (match (uu____5440) with
| (bopt, scope2, args1) -> begin
(

let uu____5540 = (aux scope2 args1 qs2)
in (match (uu____5540) with
| (sub_probs, tcs, f) -> begin
(

let f1 = (match (bopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5561 = (

let uu____5563 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst))))
in (f)::uu____5563)
in (FStar_Syntax_Util.mk_conj_l uu____5561))
end
| FStar_Pervasives_Native.Some (b) -> begin
(

let u_b = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (

let uu____5577 = (

let uu____5579 = (FStar_Syntax_Util.mk_forall u_b (FStar_Pervasives_Native.fst b) f)
in (

let uu____5580 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst))))
in (uu____5579)::uu____5580))
in (FStar_Syntax_Util.mk_conj_l uu____5577)))
end)
in (((FStar_List.append probs sub_probs)), ((tc)::tcs), (f1)))
end))
end))
end))
end))
in (aux scope ps qs))))))


type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)


type im_or_proj_t =
(((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) * FStar_Syntax_Syntax.arg Prims.list * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * variance * tc) Prims.list))


let rigid_rigid : Prims.int = (Prims.parse_int "0")


let flex_rigid_eq : Prims.int = (Prims.parse_int "1")


let flex_refine_inner : Prims.int = (Prims.parse_int "2")


let flex_refine : Prims.int = (Prims.parse_int "3")


let flex_rigid : Prims.int = (Prims.parse_int "4")


let rigid_flex : Prims.int = (Prims.parse_int "5")


let refine_flex : Prims.int = (Prims.parse_int "6")


let flex_flex : Prims.int = (Prims.parse_int "7")


let compress_tprob = (fun wl p -> (

let uu___149_5637 = p
in (

let uu____5640 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____5641 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___149_5637.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____5640; FStar_TypeChecker_Common.relation = uu___149_5637.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____5641; FStar_TypeChecker_Common.element = uu___149_5637.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___149_5637.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___149_5637.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___149_5637.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___149_5637.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___149_5637.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p1) -> begin
(

let uu____5653 = (compress_tprob wl p1)
in (FStar_All.pipe_right uu____5653 (fun _0_49 -> FStar_TypeChecker_Common.TProb (_0_49))))
end
| FStar_TypeChecker_Common.CProb (uu____5658) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (

let uu____5674 = (compress_prob wl pr)
in (FStar_All.pipe_right uu____5674 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____5680 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____5680) with
| (lh, uu____5693) -> begin
(

let uu____5708 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____5708) with
| (rh, uu____5721) -> begin
(

let uu____5736 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____5745), FStar_Syntax_Syntax.Tm_uvar (uu____5746)) -> begin
((flex_flex), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____5769), uu____5770) when ((tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (uu____5783, FStar_Syntax_Syntax.Tm_uvar (uu____5784)) when ((tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____5797), uu____5798) -> begin
(

let uu____5809 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (uu____5809) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
((flex_rigid), (tp))
end
| uu____5849 -> begin
(

let rank = (

let uu____5856 = (is_top_level_prob prob)
in (match (uu____5856) with
| true -> begin
flex_refine
end
| uu____5857 -> begin
flex_refine_inner
end))
in (

let uu____5858 = (

let uu___150_5861 = tp
in (

let uu____5864 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___150_5861.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___150_5861.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___150_5861.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____5864; FStar_TypeChecker_Common.element = uu___150_5861.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___150_5861.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___150_5861.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___150_5861.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___150_5861.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___150_5861.FStar_TypeChecker_Common.rank}))
in ((rank), (uu____5858))))
end)
end))
end
| (uu____5874, FStar_Syntax_Syntax.Tm_uvar (uu____5875)) -> begin
(

let uu____5886 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (uu____5886) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
((rigid_flex), (tp))
end
| uu____5926 -> begin
(

let uu____5932 = (

let uu___151_5937 = tp
in (

let uu____5940 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___151_5937.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____5940; FStar_TypeChecker_Common.relation = uu___151_5937.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___151_5937.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___151_5937.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___151_5937.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___151_5937.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___151_5937.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___151_5937.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___151_5937.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (uu____5932)))
end)
end))
end
| (uu____5956, uu____5957) -> begin
((rigid_rigid), (tp))
end)
in (match (uu____5736) with
| (rank, tp1) -> begin
(

let uu____5968 = (FStar_All.pipe_right (

let uu___152_5972 = tp1
in {FStar_TypeChecker_Common.pid = uu___152_5972.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___152_5972.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___152_5972.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___152_5972.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___152_5972.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___152_5972.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___152_5972.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___152_5972.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___152_5972.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rank)}) (fun _0_50 -> FStar_TypeChecker_Common.TProb (_0_50)))
in ((rank), (uu____5968)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____5978 = (FStar_All.pipe_right (

let uu___153_5982 = cp
in {FStar_TypeChecker_Common.pid = uu___153_5982.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___153_5982.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___153_5982.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___153_5982.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___153_5982.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___153_5982.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___153_5982.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___153_5982.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___153_5982.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rigid_rigid)}) (fun _0_51 -> FStar_TypeChecker_Common.CProb (_0_51)))
in ((rigid_rigid), (uu____5978)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun uu____6015 probs -> (match (uu____6015) with
| (min_rank, min1, out) -> begin
(match (probs) with
| [] -> begin
((min1), (out), (min_rank))
end
| (hd1)::tl1 -> begin
(

let uu____6045 = (rank wl hd1)
in (match (uu____6045) with
| (rank1, hd2) -> begin
(match ((rank1 <= flex_rigid_eq)) with
| true -> begin
(match (min1) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.Some (hd2)), ((FStar_List.append out tl1)), (rank1))
end
| FStar_Pervasives_Native.Some (m) -> begin
((FStar_Pervasives_Native.Some (hd2)), ((FStar_List.append out ((m)::tl1))), (rank1))
end)
end
| uu____6070 -> begin
(match ((rank1 < min_rank)) with
| true -> begin
(match (min1) with
| FStar_Pervasives_Native.None -> begin
(aux ((rank1), (FStar_Pervasives_Native.Some (hd2)), (out)) tl1)
end
| FStar_Pervasives_Native.Some (m) -> begin
(aux ((rank1), (FStar_Pervasives_Native.Some (hd2)), ((m)::out)) tl1)
end)
end
| uu____6086 -> begin
(aux ((min_rank), (min1), ((hd2)::out)) tl1)
end)
end)
end))
end)
end))
in (aux (((flex_flex + (Prims.parse_int "1"))), (FStar_Pervasives_Native.None), ([])) wl.attempting)))


let is_flex_rigid : Prims.int  ->  Prims.bool = (fun rank1 -> ((flex_refine_inner <= rank1) && (rank1 <= flex_rigid)))


let is_rigid_flex : Prims.int  ->  Prims.bool = (fun rank1 -> ((rigid_flex <= rank1) && (rank1 <= refine_flex)))

type univ_eq_sol =
| UDeferred of worklist
| USolved of worklist
| UFailed of Prims.string


let uu___is_UDeferred : univ_eq_sol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UDeferred (_0) -> begin
true
end
| uu____6116 -> begin
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
| uu____6130 -> begin
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
| uu____6144 -> begin
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

let uu____6187 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____6187) with
| (k, uu____6191) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Syntax_Unionfind.univ_equiv v1 v2)
end
| uu____6197 -> begin
false
end)
end)))))
end
| uu____6198 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (

let try_umax_components = (fun u12 u22 msg -> (match (((u12), (u22))) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(match (((FStar_List.length us1) = (FStar_List.length us2))) with
| true -> begin
(

let rec aux = (fun wl1 us11 us21 -> (match (((us11), (us21))) with
| ((u13)::us12, (u23)::us22) -> begin
(

let uu____6245 = (really_solve_universe_eq pid_orig wl1 u13 u23)
in (match (uu____6245) with
| USolved (wl2) -> begin
(aux wl2 us12 us22)
end
| failed -> begin
failed
end))
end
| uu____6248 -> begin
USolved (wl1)
end))
in (aux wl us1 us2))
end
| uu____6253 -> begin
(

let uu____6254 = (

let uu____6255 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____6256 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" uu____6255 uu____6256)))
in UFailed (uu____6254))
end)
end
| (FStar_Syntax_Syntax.U_max (us), u') -> begin
(

let rec aux = (fun wl1 us1 -> (match (us1) with
| [] -> begin
USolved (wl1)
end
| (u)::us2 -> begin
(

let uu____6272 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____6272) with
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

let uu____6290 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____6290) with
| USolved (wl2) -> begin
(aux wl2 us2)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____6293 -> begin
(

let uu____6296 = (

let uu____6297 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____6298 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" uu____6297 uu____6298 msg)))
in UFailed (uu____6296))
end))
in (match (((u11), (u21))) with
| (FStar_Syntax_Syntax.U_bvar (uu____6299), uu____6300) -> begin
(

let uu____6301 = (

let uu____6302 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____6303 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____6302 uu____6303)))
in (failwith uu____6301))
end
| (FStar_Syntax_Syntax.U_unknown, uu____6304) -> begin
(

let uu____6305 = (

let uu____6306 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____6307 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____6306 uu____6307)))
in (failwith uu____6305))
end
| (uu____6308, FStar_Syntax_Syntax.U_bvar (uu____6309)) -> begin
(

let uu____6310 = (

let uu____6311 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____6312 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____6311 uu____6312)))
in (failwith uu____6310))
end
| (uu____6313, FStar_Syntax_Syntax.U_unknown) -> begin
(

let uu____6314 = (

let uu____6315 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____6316 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____6315 uu____6316)))
in (failwith uu____6314))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((x.FStar_Ident.idText = y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____6319 -> begin
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

let uu____6332 = (FStar_Syntax_Unionfind.univ_equiv v1 v2)
in (match (uu____6332) with
| true -> begin
USolved (wl)
end
| uu____6333 -> begin
(

let wl1 = (extend_solution pid_orig ((UNIV (((v1), (u21))))::[]) wl)
in USolved (wl1))
end))
end
| (FStar_Syntax_Syntax.U_unif (v1), u) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____6346 = (occurs_univ v1 u3)
in (match (uu____6346) with
| true -> begin
(

let uu____6347 = (

let uu____6348 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____6349 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____6348 uu____6349)))
in (try_umax_components u11 u21 uu____6347))
end
| uu____6350 -> begin
(

let uu____6351 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____6351))
end)))
end
| (u, FStar_Syntax_Syntax.U_unif (v1)) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____6363 = (occurs_univ v1 u3)
in (match (uu____6363) with
| true -> begin
(

let uu____6364 = (

let uu____6365 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____6366 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____6365 uu____6366)))
in (try_umax_components u11 u21 uu____6364))
end
| uu____6367 -> begin
(

let uu____6368 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____6368))
end)))
end
| (FStar_Syntax_Syntax.U_max (uu____6373), uu____6374) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____6376 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____6379 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____6379) with
| true -> begin
USolved (wl)
end
| uu____6380 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (uu____6381, FStar_Syntax_Syntax.U_max (uu____6382)) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____6384 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____6387 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____6387) with
| true -> begin
USolved (wl)
end
| uu____6388 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (FStar_Syntax_Syntax.U_succ (uu____6389), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_succ (uu____6390), FStar_Syntax_Syntax.U_name (uu____6391)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ (uu____6392)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name (uu____6393)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____6394), FStar_Syntax_Syntax.U_succ (uu____6395)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____6396), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end))))))


let solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (match (wl.tcenv.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
USolved (wl)
end
| uu____6413 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders = (fun bc1 bc2 -> (

let uu____6466 = bc1
in (match (uu____6466) with
| (bs1, mk_cod1) -> begin
(

let uu____6491 = bc2
in (match (uu____6491) with
| (bs2, mk_cod2) -> begin
(

let curry = (fun n1 bs mk_cod -> (

let uu____6538 = (FStar_Util.first_N n1 bs)
in (match (uu____6538) with
| (bs3, rest) -> begin
(

let uu____6552 = (mk_cod rest)
in ((bs3), (uu____6552)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(

let uu____6576 = (

let uu____6580 = (mk_cod1 [])
in ((bs1), (uu____6580)))
in (

let uu____6582 = (

let uu____6586 = (mk_cod2 [])
in ((bs2), (uu____6586)))
in ((uu____6576), (uu____6582))))
end
| uu____6594 -> begin
(match ((l1 > l2)) with
| true -> begin
(

let uu____6613 = (curry l2 bs1 mk_cod1)
in (

let uu____6623 = (

let uu____6627 = (mk_cod2 [])
in ((bs2), (uu____6627)))
in ((uu____6613), (uu____6623))))
end
| uu____6635 -> begin
(

let uu____6636 = (

let uu____6640 = (mk_cod1 [])
in ((bs1), (uu____6640)))
in (

let uu____6642 = (curry l1 bs2 mk_cod2)
in ((uu____6636), (uu____6642))))
end)
end))))
end))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____6749 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6749) with
| true -> begin
(

let uu____6750 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" uu____6750))
end
| uu____6751 -> begin
()
end));
(

let uu____6752 = (next_prob probs)
in (match (uu____6752) with
| (FStar_Pervasives_Native.Some (hd1), tl1, rank1) -> begin
(

let probs1 = (

let uu___154_6765 = probs
in {attempting = tl1; wl_deferred = uu___154_6765.wl_deferred; ctr = uu___154_6765.ctr; defer_ok = uu___154_6765.defer_ok; smt_ok = uu___154_6765.smt_ok; tcenv = uu___154_6765.tcenv})
in (match (hd1) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs1)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match ((((not (probs1.defer_ok)) && (flex_refine_inner <= rank1)) && (rank1 <= flex_rigid))) with
| true -> begin
(

let uu____6772 = (solve_flex_rigid_join env tp probs1)
in (match (uu____6772) with
| FStar_Pervasives_Native.None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| FStar_Pervasives_Native.Some (wl) -> begin
(solve env wl)
end))
end
| uu____6775 -> begin
(match ((((not (probs1.defer_ok)) && (rigid_flex <= rank1)) && (rank1 <= refine_flex))) with
| true -> begin
(

let uu____6776 = (solve_rigid_flex_meet env tp probs1)
in (match (uu____6776) with
| FStar_Pervasives_Native.None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| FStar_Pervasives_Native.Some (wl) -> begin
(solve env wl)
end))
end
| uu____6779 -> begin
(solve_t' env (maybe_invert tp) probs1)
end)
end)
end))
end
| (FStar_Pervasives_Native.None, uu____6780, uu____6781) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| uu____6790 -> begin
(

let uu____6795 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____6827 -> (match (uu____6827) with
| (c, uu____6832, uu____6833) -> begin
(c < probs.ctr)
end))))
in (match (uu____6795) with
| (attempt1, rest) -> begin
(match (attempt1) with
| [] -> begin
(

let uu____6855 = (FStar_List.map (fun uu____6865 -> (match (uu____6865) with
| (uu____6871, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (uu____6855))
end
| uu____6874 -> begin
(

let uu____6879 = (

let uu___155_6880 = probs
in (

let uu____6881 = (FStar_All.pipe_right attempt1 (FStar_List.map (fun uu____6894 -> (match (uu____6894) with
| (uu____6898, uu____6899, y) -> begin
y
end))))
in {attempting = uu____6881; wl_deferred = rest; ctr = uu___155_6880.ctr; defer_ok = uu___155_6880.defer_ok; smt_ok = uu___155_6880.smt_ok; tcenv = uu___155_6880.tcenv}))
in (solve env uu____6879))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____6906 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____6906) with
| USolved (wl1) -> begin
(

let uu____6908 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____6908))
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

let uu____6942 = (solve_universe_eq (p_pid orig) wl1 u1 u2)
in (match (uu____6942) with
| USolved (wl2) -> begin
(aux wl2 us11 us21)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____6945 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t11 = (whnf env t1)
in (

let t21 = (whnf env t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = uu____6953; FStar_Syntax_Syntax.pos = uu____6954; FStar_Syntax_Syntax.vars = uu____6955}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = uu____6958; FStar_Syntax_Syntax.pos = uu____6959; FStar_Syntax_Syntax.vars = uu____6960}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____6973), uu____6974) -> begin
(failwith "Impossible: expect head symbols to match")
end
| (uu____6979, FStar_Syntax_Syntax.Tm_uinst (uu____6980)) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____6985 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____6993 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6993) with
| true -> begin
(

let uu____6994 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" uu____6994 msg))
end
| uu____6995 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____6996 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist FStar_Pervasives_Native.option = (fun env tp wl -> ((

let uu____7002 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____7002) with
| true -> begin
(

let uu____7003 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" uu____7003))
end
| uu____7004 -> begin
()
end));
(

let uu____7005 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____7005) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let uu____7047 = (head_matches_delta env () t1 t2)
in (match (uu____7047) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (uu____7069) -> begin
FStar_Pervasives_Native.None
end
| FullMatch -> begin
(match (ts) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((t1), ([])))
end
| FStar_Pervasives_Native.Some (t11, t21) -> begin
FStar_Pervasives_Native.Some (((t11), ([])))
end)
end
| HeadMatch -> begin
(

let uu____7095 = (match (ts) with
| FStar_Pervasives_Native.Some (t11, t21) -> begin
(

let uu____7104 = (FStar_Syntax_Subst.compress t11)
in (

let uu____7105 = (FStar_Syntax_Subst.compress t21)
in ((uu____7104), (uu____7105))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____7108 = (FStar_Syntax_Subst.compress t1)
in (

let uu____7109 = (FStar_Syntax_Subst.compress t2)
in ((uu____7108), (uu____7109))))
end)
in (match (uu____7095) with
| (t11, t21) -> begin
(

let eq_prob = (fun t12 t22 -> (

let uu____7131 = (new_problem env t12 FStar_TypeChecker_Common.EQ t22 FStar_Pervasives_Native.None t12.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _0_52 -> FStar_TypeChecker_Common.TProb (_0_52)) uu____7131)))
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(

let uu____7154 = (

let uu____7160 = (

let uu____7163 = (

let uu____7166 = (

let uu____7167 = (

let uu____7172 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (uu____7172)))
in FStar_Syntax_Syntax.Tm_refine (uu____7167))
in (FStar_Syntax_Syntax.mk uu____7166))
in (uu____7163 FStar_Pervasives_Native.None t11.FStar_Syntax_Syntax.pos))
in (

let uu____7185 = (

let uu____7187 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (uu____7187)::[])
in ((uu____7160), (uu____7185))))
in FStar_Pervasives_Native.Some (uu____7154))
end
| (uu____7196, FStar_Syntax_Syntax.Tm_refine (x, uu____7198)) -> begin
(

let uu____7203 = (

let uu____7207 = (

let uu____7209 = (eq_prob x.FStar_Syntax_Syntax.sort t11)
in (uu____7209)::[])
in ((t11), (uu____7207)))
in FStar_Pervasives_Native.Some (uu____7203))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____7215), uu____7216) -> begin
(

let uu____7221 = (

let uu____7225 = (

let uu____7227 = (eq_prob x.FStar_Syntax_Syntax.sort t21)
in (uu____7227)::[])
in ((t21), (uu____7225)))
in FStar_Pervasives_Native.Some (uu____7221))
end
| uu____7232 -> begin
(

let uu____7235 = (FStar_Syntax_Util.head_and_args t11)
in (match (uu____7235) with
| (head1, uu____7250) -> begin
(

let uu____7265 = (

let uu____7266 = (FStar_Syntax_Util.un_uinst head1)
in uu____7266.FStar_Syntax_Syntax.n)
in (match (uu____7265) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____7273; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (i); FStar_Syntax_Syntax.fv_qual = uu____7275}) -> begin
(

let prev = (match ((i > (Prims.parse_int "1"))) with
| true -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i - (Prims.parse_int "1")))
end
| uu____7278 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
in (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t21)
in (disjoin t12 t22))))
end
| uu____7281 -> begin
FStar_Pervasives_Native.None
end))
end))
end))
end))
end)
end)))
in (

let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____7290) -> begin
(

let uu____7307 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___129_7325 -> (match (uu___129_7325) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| FStar_Pervasives_Native.Some (rank1) when (is_rigid_flex rank1) -> begin
(

let uu____7330 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.rhs)
in (match (uu____7330) with
| (u', uu____7341) -> begin
(

let uu____7356 = (

let uu____7357 = (whnf env u')
in uu____7357.FStar_Syntax_Syntax.n)
in (match (uu____7356) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____7361) -> begin
(FStar_Syntax_Unionfind.equiv uv uv')
end
| uu____7378 -> begin
false
end))
end))
end
| uu____7379 -> begin
false
end)
end
| uu____7381 -> begin
false
end))))
in (match (uu____7307) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun uu____7402 tps -> (match (uu____7402) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
FStar_Pervasives_Native.Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____7429 = (

let uu____7434 = (whnf env hd1.FStar_TypeChecker_Common.lhs)
in (disjoin bound uu____7434))
in (match (uu____7429) with
| FStar_Pervasives_Native.Some (bound1, sub1) -> begin
(make_lower_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7453 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let uu____7458 = (

let uu____7463 = (

let uu____7467 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((uu____7467), ([])))
in (make_lower_bound uu____7463 lower_bounds))
in (match (uu____7458) with
| FStar_Pervasives_Native.None -> begin
((

let uu____7474 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____7474) with
| true -> begin
(FStar_Util.print_string "No lower bounds\n")
end
| uu____7475 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (lhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in ((

let uu____7487 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____7487) with
| true -> begin
(

let wl' = (

let uu___156_7489 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___156_7489.wl_deferred; ctr = uu___156_7489.ctr; defer_ok = uu___156_7489.defer_ok; smt_ok = uu___156_7489.smt_ok; tcenv = uu___156_7489.tcenv})
in (

let uu____7490 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" uu____7490)))
end
| uu____7491 -> begin
()
end));
(

let uu____7492 = (solve_t env eq_prob (

let uu___157_7494 = wl
in {attempting = sub_probs; wl_deferred = uu___157_7494.wl_deferred; ctr = uu___157_7494.ctr; defer_ok = uu___157_7494.defer_ok; smt_ok = uu___157_7494.smt_ok; tcenv = uu___157_7494.tcenv}))
in (match (uu____7492) with
| Success (uu____7496) -> begin
(

let wl1 = (

let uu___158_7498 = wl
in {attempting = rest; wl_deferred = uu___158_7498.wl_deferred; ctr = uu___158_7498.ctr; defer_ok = uu___158_7498.defer_ok; smt_ok = uu___158_7498.smt_ok; tcenv = uu___158_7498.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) FStar_Pervasives_Native.None [] wl1)
in (

let uu____7500 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p FStar_Pervasives_Native.None [] wl3)) wl2 lower_bounds)
in FStar_Pervasives_Native.Some (wl2))))
end
| uu____7505 -> begin
FStar_Pervasives_Native.None
end));
))
end)))
end))
end
| uu____7506 -> begin
(failwith "Impossible: Not a rigid-flex")
end)))
end));
))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist FStar_Pervasives_Native.option = (fun env tp wl -> ((

let uu____7513 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____7513) with
| true -> begin
(

let uu____7514 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" uu____7514))
end
| uu____7515 -> begin
()
end));
(

let uu____7516 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____7516) with
| (u, args) -> begin
(

let uu____7543 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (uu____7543) with
| (ok, head_match1, partial_match, fallback, failed_match) -> begin
(

let max1 = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____7562 -> begin
i
end))
in (

let base_types_match = (fun t1 t2 -> (

let uu____7574 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____7574) with
| (h1, args1) -> begin
(

let uu____7602 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____7602) with
| (h2, uu____7615) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
(

let uu____7634 = (FStar_Syntax_Syntax.fv_eq tc1 tc2)
in (match (uu____7634) with
| true -> begin
(match (((FStar_List.length args1) = (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____7648 -> begin
(

let uu____7649 = (

let uu____7651 = (

let uu____7652 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_53 -> FStar_TypeChecker_Common.TProb (_0_53)) uu____7652))
in (uu____7651)::[])
in FStar_Pervasives_Native.Some (uu____7649))
end)
end
| uu____7658 -> begin
FStar_Pervasives_Native.None
end))
end
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(match ((FStar_Syntax_Syntax.bv_eq a b)) with
| true -> begin
(match (((FStar_List.length args1) = (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____7675 -> begin
(

let uu____7676 = (

let uu____7678 = (

let uu____7679 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_54 -> FStar_TypeChecker_Common.TProb (_0_54)) uu____7679))
in (uu____7678)::[])
in FStar_Pervasives_Native.Some (uu____7676))
end)
end
| uu____7685 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____7687 -> begin
FStar_Pervasives_Native.None
end)
end))
end)))
in (

let conjoin = (fun t1 t2 -> (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(

let m = (base_types_match x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (match (m) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (m1) -> begin
(

let x1 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let subst1 = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x1))))::[]
in (

let phi11 = (FStar_Syntax_Subst.subst subst1 phi1)
in (

let phi21 = (FStar_Syntax_Subst.subst subst1 phi2)
in (

let uu____7753 = (

let uu____7759 = (

let uu____7762 = (FStar_Syntax_Util.mk_conj phi11 phi21)
in (FStar_Syntax_Util.refine x1 uu____7762))
in ((uu____7759), (m1)))
in FStar_Pervasives_Native.Some (uu____7753))))))
end))
end
| (uu____7771, FStar_Syntax_Syntax.Tm_refine (y, uu____7773)) -> begin
(

let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (m1) -> begin
FStar_Pervasives_Native.Some (((t2), (m1)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____7805), uu____7806) -> begin
(

let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (m1) -> begin
FStar_Pervasives_Native.Some (((t1), (m1)))
end))
end
| uu____7837 -> begin
(

let m = (base_types_match t1 t2)
in (match (m) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (m1) -> begin
FStar_Pervasives_Native.Some (((t1), (m1)))
end))
end))
in (

let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____7871) -> begin
(

let uu____7888 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___130_7906 -> (match (uu___130_7906) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| FStar_Pervasives_Native.Some (rank1) when (is_flex_rigid rank1) -> begin
(

let uu____7911 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.lhs)
in (match (uu____7911) with
| (u', uu____7922) -> begin
(

let uu____7937 = (

let uu____7938 = (whnf env u')
in uu____7938.FStar_Syntax_Syntax.n)
in (match (uu____7937) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____7942) -> begin
(FStar_Syntax_Unionfind.equiv uv uv')
end
| uu____7959 -> begin
false
end))
end))
end
| uu____7960 -> begin
false
end)
end
| uu____7962 -> begin
false
end))))
in (match (uu____7888) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun uu____7987 tps -> (match (uu____7987) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
FStar_Pervasives_Native.Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____8028 = (

let uu____8035 = (whnf env hd1.FStar_TypeChecker_Common.rhs)
in (conjoin bound uu____8035))
in (match (uu____8028) with
| FStar_Pervasives_Native.Some (bound1, sub1) -> begin
(make_upper_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____8070 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let uu____8077 = (

let uu____8084 = (

let uu____8090 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((uu____8090), ([])))
in (make_upper_bound uu____8084 upper_bounds))
in (match (uu____8077) with
| FStar_Pervasives_Native.None -> begin
((

let uu____8099 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____8099) with
| true -> begin
(FStar_Util.print_string "No upper bounds\n")
end
| uu____8100 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "joining refinements")
in ((

let uu____8118 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____8118) with
| true -> begin
(

let wl' = (

let uu___159_8120 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___159_8120.wl_deferred; ctr = uu___159_8120.ctr; defer_ok = uu___159_8120.defer_ok; smt_ok = uu___159_8120.smt_ok; tcenv = uu___159_8120.tcenv})
in (

let uu____8121 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" uu____8121)))
end
| uu____8122 -> begin
()
end));
(

let uu____8123 = (solve_t env eq_prob (

let uu___160_8125 = wl
in {attempting = sub_probs; wl_deferred = uu___160_8125.wl_deferred; ctr = uu___160_8125.ctr; defer_ok = uu___160_8125.defer_ok; smt_ok = uu___160_8125.smt_ok; tcenv = uu___160_8125.tcenv}))
in (match (uu____8123) with
| Success (uu____8127) -> begin
(

let wl1 = (

let uu___161_8129 = wl
in {attempting = rest; wl_deferred = uu___161_8129.wl_deferred; ctr = uu___161_8129.ctr; defer_ok = uu___161_8129.defer_ok; smt_ok = uu___161_8129.smt_ok; tcenv = uu___161_8129.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) FStar_Pervasives_Native.None [] wl1)
in (

let uu____8131 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p FStar_Pervasives_Native.None [] wl3)) wl2 upper_bounds)
in FStar_Pervasives_Native.Some (wl2))))
end
| uu____8136 -> begin
FStar_Pervasives_Native.None
end));
))
end)))
end))
end
| uu____8137 -> begin
(failwith "Impossible: Not a flex-rigid")
end)))))
end))
end));
))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (

let rec aux = (fun scope env1 subst1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
(

let rhs_prob = (rhs (FStar_List.rev scope) env1 subst1)
in ((

let uu____8198 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____8198) with
| true -> begin
(

let uu____8199 = (prob_to_string env1 rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" uu____8199))
end
| uu____8200 -> begin
()
end));
(

let formula = (FStar_All.pipe_right (p_guard rhs_prob) FStar_Pervasives_Native.fst)
in FStar_Util.Inl ((((rhs_prob)::[]), (formula))));
))
end
| (((hd1, imp))::xs1, ((hd2, imp'))::ys1) when (imp = imp') -> begin
(

let hd11 = (

let uu___162_8231 = hd1
in (

let uu____8232 = (FStar_Syntax_Subst.subst subst1 hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___162_8231.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___162_8231.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____8232}))
in (

let hd21 = (

let uu___163_8236 = hd2
in (

let uu____8237 = (FStar_Syntax_Subst.subst subst1 hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___163_8236.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___163_8236.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____8237}))
in (

let prob = (

let uu____8241 = (

let uu____8244 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd11.FStar_Syntax_Syntax.sort uu____8244 hd21.FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None "Formal parameter"))
in (FStar_All.pipe_left (fun _0_55 -> FStar_TypeChecker_Common.TProb (_0_55)) uu____8241))
in (

let hd12 = (FStar_Syntax_Syntax.freshen_bv hd11)
in (

let subst2 = (

let uu____8252 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd12))))::uu____8252)
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 hd12)
in (

let uu____8255 = (aux ((((hd12), (imp)))::scope) env2 subst2 xs1 ys1)
in (match (uu____8255) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi1 = (

let uu____8273 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (

let uu____8276 = (close_forall env2 ((((hd12), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj uu____8273 uu____8276)))
in ((

let uu____8282 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____8282) with
| true -> begin
(

let uu____8283 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____8284 = (FStar_Syntax_Print.bv_to_string hd12)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" uu____8283 uu____8284)))
end
| uu____8285 -> begin
()
end));
FStar_Util.Inl ((((prob)::sub_probs), (phi1)));
))
end
| fail -> begin
fail
end))))))))
end
| uu____8299 -> begin
FStar_Util.Inr ("arity or argument-qualifier mismatch")
end))
in (

let scope = (p_scope orig)
in (

let uu____8305 = (aux scope env [] bs1 bs2)
in (match (uu____8305) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (phi)) [] wl)
in (solve env (attempt sub_probs wl1)))
end)))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let uu____8321 = (compress_tprob wl problem)
in (solve_t' env uu____8321 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer1 = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env1 orig wl1 head1 head2 t1 t2 -> (

let uu____8354 = (head_matches_delta env1 wl1 t1 t2)
in (match (uu____8354) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____8371), uu____8372) -> begin
(

let may_relate = (fun head3 -> (

let uu____8387 = (

let uu____8388 = (FStar_Syntax_Util.un_uinst head3)
in uu____8388.FStar_Syntax_Syntax.n)
in (match (uu____8387) with
| FStar_Syntax_Syntax.Tm_name (uu____8391) -> begin
true
end
| FStar_Syntax_Syntax.Tm_match (uu____8392) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____8408 -> begin
false
end)))
in (

let uu____8409 = (((may_relate head1) || (may_relate head2)) && wl1.smt_ok)
in (match (uu____8409) with
| true -> begin
(

let guard = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_eq2 env1 t1 t2)
end
| uu____8411 -> begin
(

let has_type_guard = (fun t11 t21 -> (match (problem.FStar_TypeChecker_Common.element) with
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t11 t t21)
end
| FStar_Pervasives_Native.None -> begin
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None t11)
in (

let u_x = (env1.FStar_TypeChecker_Env.universe_of env1 t11)
in (

let uu____8426 = (

let uu____8427 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t11 uu____8427 t21))
in (FStar_Syntax_Util.mk_forall u_x x uu____8426))))
end))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB)) with
| true -> begin
(has_type_guard t1 t2)
end
| uu____8428 -> begin
(has_type_guard t2 t1)
end))
end)
in (

let uu____8429 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl1)
in (solve env1 uu____8429)))
end
| uu____8430 -> begin
(

let uu____8431 = (

let uu____8432 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____8433 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.format2 "head mismatch (%s vs %s)" uu____8432 uu____8433)))
in (giveup env1 uu____8431 orig))
end)))
end
| (uu____8434, FStar_Pervasives_Native.Some (t11, t21)) -> begin
(solve_t env1 (

let uu___164_8443 = problem
in {FStar_TypeChecker_Common.pid = uu___164_8443.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___164_8443.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___164_8443.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_8443.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_8443.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_8443.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_8443.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_8443.FStar_TypeChecker_Common.rank}) wl1)
end
| (uu____8444, FStar_Pervasives_Native.None) -> begin
((

let uu____8451 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____8451) with
| true -> begin
(

let uu____8452 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____8453 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____8454 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____8455 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" uu____8452 uu____8453 uu____8454 uu____8455)))))
end
| uu____8456 -> begin
()
end));
(

let uu____8457 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____8457) with
| (head11, args1) -> begin
(

let uu____8483 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____8483) with
| (head21, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((nargs <> (FStar_List.length args2))) with
| true -> begin
(

let uu____8528 = (

let uu____8529 = (FStar_Syntax_Print.term_to_string head11)
in (

let uu____8530 = (args_to_string args1)
in (

let uu____8531 = (FStar_Syntax_Print.term_to_string head21)
in (

let uu____8532 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____8529 uu____8530 uu____8531 uu____8532)))))
in (giveup env1 uu____8528 orig))
end
| uu____8533 -> begin
(

let uu____8534 = ((nargs = (Prims.parse_int "0")) || (

let uu____8540 = (FStar_Syntax_Util.eq_args args1 args2)
in (uu____8540 = FStar_Syntax_Util.Equal)))
in (match (uu____8534) with
| true -> begin
(

let uu____8541 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____8541) with
| USolved (wl2) -> begin
(

let uu____8543 = (solve_prob orig FStar_Pervasives_Native.None [] wl2)
in (solve env1 uu____8543))
end
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end))
end
| uu____8546 -> begin
(

let uu____8547 = (base_and_refinement env1 wl1 t1)
in (match (uu____8547) with
| (base1, refinement1) -> begin
(

let uu____8573 = (base_and_refinement env1 wl1 t2)
in (match (uu____8573) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(

let uu____8627 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____8627) with
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end
| USolved (wl2) -> begin
(

let subprobs = (FStar_List.map2 (fun uu____8644 uu____8645 -> (match (((uu____8644), (uu____8645))) with
| ((a, uu____8655), (a', uu____8657)) -> begin
(

let uu____8662 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' FStar_Pervasives_Native.None "index")
in (FStar_All.pipe_left (fun _0_56 -> FStar_TypeChecker_Common.TProb (_0_56)) uu____8662))
end)) args1 args2)
in (

let formula = (

let uu____8668 = (FStar_List.map (fun p -> (FStar_Pervasives_Native.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____8668))
in (

let wl3 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) [] wl2)
in (solve env1 (attempt subprobs wl3)))))
end))
end
| uu____8673 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env1 (

let uu___165_8707 = problem
in {FStar_TypeChecker_Common.pid = uu___165_8707.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___165_8707.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___165_8707.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___165_8707.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___165_8707.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___165_8707.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___165_8707.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___165_8707.FStar_TypeChecker_Common.rank}) wl1)))
end)
end))
end))
end))
end))
end))
end));
)
end)
end)))
in (

let imitate = (fun orig env1 wl1 p -> (

let uu____8727 = p
in (match (uu____8727) with
| (((u, k), xs, c), ps, (h, uu____8738, qs)) -> begin
(

let xs1 = (sn_binders env1 xs)
in (

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____8787 = (imitation_sub_probs orig env1 xs1 ps qs)
in (match (uu____8787) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (

let uu____8801 = (h gs_xs)
in (

let uu____8802 = (FStar_All.pipe_right (FStar_Syntax_Util.residual_comp_of_comp c) (fun _0_57 -> FStar_Pervasives_Native.Some (_0_57)))
in (FStar_Syntax_Util.abs xs1 uu____8801 uu____8802)))
in ((

let uu____8806 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____8806) with
| true -> begin
(

let uu____8807 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____8808 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____8809 = (FStar_Syntax_Print.term_to_string im)
in (

let uu____8810 = (FStar_Syntax_Print.tag_of_term im)
in (

let uu____8811 = (

let uu____8812 = (FStar_List.map (prob_to_string env1) sub_probs)
in (FStar_All.pipe_right uu____8812 (FStar_String.concat ", ")))
in (

let uu____8815 = (FStar_TypeChecker_Normalize.term_to_string env1 formula)
in (FStar_Util.print6 "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" uu____8807 uu____8808 uu____8809 uu____8810 uu____8811 uu____8815)))))))
end
| uu____8816 -> begin
()
end));
(

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl1)
in (solve env1 (attempt sub_probs wl2)));
))
end))))
end)))
in (

let imitate' = (fun orig env1 wl1 uu___131_8833 -> (match (uu___131_8833) with
| FStar_Pervasives_Native.None -> begin
(giveup env1 "unable to compute subterms" orig)
end
| FStar_Pervasives_Native.Some (p) -> begin
(imitate orig env1 wl1 p)
end))
in (

let project = (fun orig env1 wl1 i p -> (

let uu____8862 = p
in (match (uu____8862) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____8920 = (FStar_List.nth ps i)
in (match (uu____8920) with
| (pi, uu____8923) -> begin
(

let uu____8928 = (FStar_List.nth xs i)
in (match (uu____8928) with
| (xi, uu____8935) -> begin
(

let rec gs = (fun k -> (

let uu____8944 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____8944) with
| (bs, k1) -> begin
(

let rec aux = (fun subst1 bs1 -> (match (bs1) with
| [] -> begin
(([]), ([]))
end
| ((a, uu____8996))::tl1 -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst1 a.FStar_Syntax_Syntax.sort)
in (

let uu____9004 = (new_uvar r xs k_a)
in (match (uu____9004) with
| (gi_xs, gi) -> begin
(

let gi_xs1 = (FStar_TypeChecker_Normalize.eta_expand env1 gi_xs)
in (

let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (FStar_Pervasives_Native.Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((a), (gi_xs1))))::subst1
in (

let uu____9021 = (aux subst2 tl1)
in (match (uu____9021) with
| (gi_xs', gi_ps') -> begin
(

let uu____9036 = (

let uu____9038 = (FStar_Syntax_Syntax.as_arg gi_xs1)
in (uu____9038)::gi_xs')
in (

let uu____9039 = (

let uu____9041 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (uu____9041)::gi_ps')
in ((uu____9036), (uu____9039))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in (

let uu____9044 = (

let uu____9045 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation uu____9045))
in (match (uu____9044) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____9047 -> begin
(

let uu____9048 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (uu____9048) with
| (g_xs, uu____9055) -> begin
(

let xi1 = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (

let uu____9062 = (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs FStar_Pervasives_Native.None r)
in (

let uu____9065 = (FStar_All.pipe_right (FStar_Syntax_Util.residual_comp_of_comp c) (fun _0_58 -> FStar_Pervasives_Native.Some (_0_58)))
in (FStar_Syntax_Util.abs xs uu____9062 uu____9065)))
in (

let sub1 = (

let uu____9069 = (

let uu____9072 = (FStar_Syntax_Syntax.mk_Tm_app proj ps FStar_Pervasives_Native.None r)
in (

let uu____9077 = (

let uu____9080 = (FStar_List.map (fun uu____9090 -> (match (uu____9090) with
| (uu____9095, uu____9096, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h uu____9080))
in (mk_problem (p_scope orig) orig uu____9072 (p_rel orig) uu____9077 FStar_Pervasives_Native.None "projection")))
in (FStar_All.pipe_left (fun _0_59 -> FStar_TypeChecker_Common.TProb (_0_59)) uu____9069))
in ((

let uu____9106 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____9106) with
| true -> begin
(

let uu____9107 = (FStar_Syntax_Print.term_to_string proj)
in (

let uu____9108 = (prob_to_string env1 sub1)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" uu____9107 uu____9108)))
end
| uu____9109 -> begin
()
end));
(

let wl2 = (

let uu____9111 = (

let uu____9113 = (FStar_All.pipe_left FStar_Pervasives_Native.fst (p_guard sub1))
in FStar_Pervasives_Native.Some (uu____9113))
in (solve_prob orig uu____9111 ((TERM (((u), (proj))))::[]) wl1))
in (

let uu____9118 = (solve env1 (attempt ((sub1)::[]) wl2))
in (FStar_All.pipe_left (fun _0_60 -> FStar_Pervasives_Native.Some (_0_60)) uu____9118)));
))))
end))
end)))
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl1 -> (

let uu____9142 = lhs
in (match (uu____9142) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let uu____9165 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (uu____9165) with
| (xs, c) -> begin
(match (((FStar_List.length xs) = (FStar_List.length ps))) with
| true -> begin
(

let uu____9191 = (

let uu____9217 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____9217)))
in FStar_Pervasives_Native.Some (uu____9191))
end
| uu____9283 -> begin
(

let k_uv1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (

let uu____9300 = (

let uu____9304 = (

let uu____9305 = (FStar_Syntax_Subst.compress k)
in uu____9305.FStar_Syntax_Syntax.n)
in ((uu____9304), (args)))
in (match (uu____9300) with
| (uu____9312, []) -> begin
(

let uu____9314 = (

let uu____9320 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____9320)))
in FStar_Pervasives_Native.Some (uu____9314))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____9331), uu____9332) -> begin
(

let uu____9345 = (FStar_Syntax_Util.head_and_args k)
in (match (uu____9345) with
| (uv1, uv_args) -> begin
(

let uu____9374 = (

let uu____9375 = (FStar_Syntax_Subst.compress uv1)
in uu____9375.FStar_Syntax_Syntax.n)
in (match (uu____9374) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____9382) -> begin
(

let uu____9399 = (pat_vars env [] uv_args)
in (match (uu____9399) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (scope) -> begin
(

let xs1 = (FStar_All.pipe_right args (FStar_List.map (fun uu____9415 -> (

let uu____9416 = (

let uu____9417 = (

let uu____9418 = (

let uu____9421 = (

let uu____9422 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____9422 FStar_Pervasives_Native.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____9421))
in (FStar_Pervasives_Native.fst uu____9418))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.pos)) uu____9417))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____9416)))))
in (

let c1 = (

let uu____9428 = (

let uu____9429 = (

let uu____9432 = (

let uu____9433 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____9433 FStar_Pervasives_Native.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____9432))
in (FStar_Pervasives_Native.fst uu____9429))
in (FStar_Syntax_Syntax.mk_Total uu____9428))
in (

let k' = (FStar_Syntax_Util.arrow xs1 c1)
in (

let uv_sol = (

let uu____9442 = (

let uu____9444 = (

let uu____9445 = (

let uu____9448 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____9448 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Util.residual_tot uu____9445))
in FStar_Pervasives_Native.Some (uu____9444))
in (FStar_Syntax_Util.abs scope k' uu____9442))
in ((FStar_Syntax_Unionfind.change uvar uv_sol);
FStar_Pervasives_Native.Some (((xs1), (c1)));
)))))
end))
end
| uu____9458 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_app (uu____9461), uu____9462) -> begin
(

let uu____9474 = (FStar_Syntax_Util.head_and_args k)
in (match (uu____9474) with
| (uv1, uv_args) -> begin
(

let uu____9503 = (

let uu____9504 = (FStar_Syntax_Subst.compress uv1)
in uu____9504.FStar_Syntax_Syntax.n)
in (match (uu____9503) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____9511) -> begin
(

let uu____9528 = (pat_vars env [] uv_args)
in (match (uu____9528) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (scope) -> begin
(

let xs1 = (FStar_All.pipe_right args (FStar_List.map (fun uu____9544 -> (

let uu____9545 = (

let uu____9546 = (

let uu____9547 = (

let uu____9550 = (

let uu____9551 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____9551 FStar_Pervasives_Native.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____9550))
in (FStar_Pervasives_Native.fst uu____9547))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.pos)) uu____9546))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____9545)))))
in (

let c1 = (

let uu____9557 = (

let uu____9558 = (

let uu____9561 = (

let uu____9562 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____9562 FStar_Pervasives_Native.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____9561))
in (FStar_Pervasives_Native.fst uu____9558))
in (FStar_Syntax_Syntax.mk_Total uu____9557))
in (

let k' = (FStar_Syntax_Util.arrow xs1 c1)
in (

let uv_sol = (

let uu____9571 = (

let uu____9573 = (

let uu____9574 = (

let uu____9577 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____9577 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Util.residual_tot uu____9574))
in FStar_Pervasives_Native.Some (uu____9573))
in (FStar_Syntax_Util.abs scope k' uu____9571))
in ((FStar_Syntax_Unionfind.change uvar uv_sol);
FStar_Pervasives_Native.Some (((xs1), (c1)));
)))))
end))
end
| uu____9587 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs1, c1), uu____9592) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs1)
in (match ((n_xs = n_args)) with
| true -> begin
(

let uu____9624 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (FStar_All.pipe_right uu____9624 (fun _0_61 -> FStar_Pervasives_Native.Some (_0_61))))
end
| uu____9634 -> begin
(match ((n_xs < n_args)) with
| true -> begin
(

let uu____9648 = (FStar_Util.first_N n_xs args)
in (match (uu____9648) with
| (args1, rest) -> begin
(

let uu____9666 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (match (uu____9666) with
| (xs2, c2) -> begin
(

let uu____9674 = (elim (FStar_Syntax_Util.comp_result c2) rest)
in (FStar_Util.bind_opt uu____9674 (fun uu____9688 -> (match (uu____9688) with
| (xs', c3) -> begin
FStar_Pervasives_Native.Some ((((FStar_List.append xs2 xs')), (c3)))
end))))
end))
end))
end
| uu____9709 -> begin
(

let uu____9710 = (FStar_Util.first_N n_args xs1)
in (match (uu____9710) with
| (xs2, rest) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c1)))) FStar_Pervasives_Native.None k.FStar_Syntax_Syntax.pos)
in (

let uu____9754 = (

let uu____9757 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs2 uu____9757))
in (FStar_All.pipe_right uu____9754 (fun _0_62 -> FStar_Pervasives_Native.Some (_0_62)))))
end))
end)
end)))
end
| uu____9765 -> begin
(

let uu____9769 = (

let uu____9770 = (FStar_Syntax_Print.uvar_to_string uv)
in (

let uu____9771 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____9772 = (FStar_Syntax_Print.term_to_string k_uv1)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" uu____9770 uu____9771 uu____9772))))
in (failwith uu____9769))
end)))
in (

let uu____9776 = (elim k_uv1 ps)
in (FStar_Util.bind_opt uu____9776 (fun uu____9808 -> (match (uu____9808) with
| (xs1, c1) -> begin
(

let uu____9836 = (

let uu____9859 = (decompose env t2)
in ((((((uv), (k_uv1))), (xs1), (c1))), (ps), (uu____9859)))
in FStar_Pervasives_Native.Some (uu____9836))
end))))))
end)
end)))
in (

let rec imitate_or_project = (fun n1 stopt i -> (match (((i >= n1) || (FStar_Option.isNone stopt))) with
| true -> begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end
| uu____9928 -> begin
(

let st = (FStar_Option.get stopt)
in (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (match ((i = (~- ((Prims.parse_int "1"))))) with
| true -> begin
(

let uu____9931 = (imitate orig env wl1 st)
in (match (uu____9931) with
| Failed (uu____9936) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(imitate_or_project n1 stopt (i + (Prims.parse_int "1")));
)
end
| sol -> begin
sol
end))
end
| uu____9941 -> begin
(

let uu____9942 = (project orig env wl1 i st)
in (match (uu____9942) with
| FStar_Pervasives_Native.None -> begin
((FStar_Syntax_Unionfind.rollback tx);
(imitate_or_project n1 stopt (i + (Prims.parse_int "1")));
)
end
| FStar_Pervasives_Native.Some (Failed (uu____9949)) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(imitate_or_project n1 stopt (i + (Prims.parse_int "1")));
)
end
| FStar_Pervasives_Native.Some (sol) -> begin
sol
end))
end)))
end))
in (

let check_head = (fun fvs1 t21 -> (

let uu____9963 = (FStar_Syntax_Util.head_and_args t21)
in (match (uu____9963) with
| (hd1, uu____9974) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____9989) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____9997) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____9998) -> begin
true
end
| uu____10008 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd1)
in (

let uu____10011 = (FStar_Util.set_is_subset_of fvs_hd fvs1)
in (match (uu____10011) with
| true -> begin
true
end
| uu____10012 -> begin
((

let uu____10014 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10014) with
| true -> begin
(

let uu____10015 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" uu____10015))
end
| uu____10016 -> begin
()
end));
false;
)
end)))
end)
end)))
in (

let imitate_ok = (fun t21 -> (

let fvs_hd = (

let uu____10023 = (

let uu____10026 = (FStar_Syntax_Util.head_and_args t21)
in (FStar_All.pipe_right uu____10026 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____10023 FStar_Syntax_Free.names))
in (

let uu____10057 = (FStar_Util.set_is_empty fvs_hd)
in (match (uu____10057) with
| true -> begin
(~- ((Prims.parse_int "1")))
end
| uu____10058 -> begin
(Prims.parse_int "0")
end))))
in (match (maybe_pat_vars) with
| FStar_Pervasives_Native.Some (vars) -> begin
(

let t11 = (sn env t1)
in (

let t21 = (sn env t2)
in (

let fvs1 = (FStar_Syntax_Free.names t11)
in (

let fvs2 = (FStar_Syntax_Free.names t21)
in (

let uu____10066 = (occurs_check env wl1 ((uv), (k_uv)) t21)
in (match (uu____10066) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____10074 = (

let uu____10075 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____10075))
in (giveup_or_defer1 orig uu____10074))
end
| uu____10076 -> begin
(

let uu____10077 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____10077) with
| true -> begin
(

let uu____10078 = (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t21)) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))
in (match (uu____10078) with
| true -> begin
(

let uu____10079 = (subterms args_lhs)
in (imitate' orig env wl1 uu____10079))
end
| uu____10081 -> begin
((

let uu____10083 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10083) with
| true -> begin
(

let uu____10084 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____10085 = (names_to_string fvs1)
in (

let uu____10086 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" uu____10084 uu____10085 uu____10086))))
end
| uu____10087 -> begin
()
end));
(

let sol = (match (vars) with
| [] -> begin
t21
end
| uu____10091 -> begin
(

let uu____10092 = (sn_binders env vars)
in (u_abs k_uv uu____10092 t21))
end)
in (

let wl2 = (solve_prob orig FStar_Pervasives_Native.None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl1)
in (solve env wl2)));
)
end))
end
| uu____10099 -> begin
(match ((((not (patterns_only)) && wl1.defer_ok) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl1))
end
| uu____10100 -> begin
(

let uu____10101 = ((not (patterns_only)) && (check_head fvs1 t21))
in (match (uu____10101) with
| true -> begin
((

let uu____10103 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10103) with
| true -> begin
(

let uu____10104 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____10105 = (names_to_string fvs1)
in (

let uu____10106 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" uu____10104 uu____10105 uu____10106))))
end
| uu____10107 -> begin
()
end));
(

let uu____10108 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____10108 (~- ((Prims.parse_int "1")))));
)
end
| uu____10120 -> begin
(giveup env "free-variable check failed on a non-redex" orig)
end))
end)
end))
end)
end))))))
end
| FStar_Pervasives_Native.None when patterns_only -> begin
(giveup env "not a pattern" orig)
end
| FStar_Pervasives_Native.None -> begin
(match (wl1.defer_ok) with
| true -> begin
(solve env (defer "not a pattern" orig wl1))
end
| uu____10121 -> begin
(

let uu____10122 = (

let uu____10123 = (FStar_Syntax_Free.names t1)
in (check_head uu____10123 t2))
in (match (uu____10122) with
| true -> begin
(

let im_ok = (imitate_ok t2)
in ((

let uu____10127 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10127) with
| true -> begin
(

let uu____10128 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" uu____10128 (match ((im_ok < (Prims.parse_int "0"))) with
| true -> begin
"imitating"
end
| uu____10129 -> begin
"projecting"
end)))
end
| uu____10130 -> begin
()
end));
(

let uu____10131 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____10131 im_ok));
))
end
| uu____10143 -> begin
(giveup env "head-symbol is free" orig)
end))
end)
end)))))
end)))
in (

let flex_flex1 = (fun orig lhs rhs -> (match ((wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex-flex deferred" orig wl))
end
| uu____10154 -> begin
(

let force_quasi_pattern = (fun xs_opt uu____10176 -> (match (uu____10176) with
| (t, u, k, args) -> begin
(

let k1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let uu____10207 = (FStar_Syntax_Util.arrow_formals k1)
in (match (uu____10207) with
| (all_formals, uu____10218) -> begin
(

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args1 -> (match (((formals), (args1))) with
| ([], []) -> begin
(

let pat_args1 = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun uu____10313 -> (match (uu____10313) with
| (x, imp) -> begin
(

let uu____10320 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____10320), (imp)))
end))))
in (

let pattern_vars1 = (FStar_List.rev pattern_vars)
in (

let kk = (

let uu____10328 = (FStar_Syntax_Util.type_u ())
in (match (uu____10328) with
| (t1, uu____10332) -> begin
(

let uu____10333 = (new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1 t1)
in (FStar_Pervasives_Native.fst uu____10333))
end))
in (

let uu____10336 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk)
in (match (uu____10336) with
| (t', tm_u1) -> begin
(

let uu____10343 = (destruct_flex_t t')
in (match (uu____10343) with
| (uu____10365, u1, k11, uu____10368) -> begin
(

let sol = (

let uu____10400 = (

let uu____10405 = (u_abs k1 all_formals t')
in ((((u), (k1))), (uu____10405)))
in TERM (uu____10400))
in (

let t_app = (FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in ((sol), (((t_app), (u1), (k11), (pat_args1))))))
end))
end)))))
end
| ((formal)::formals1, (hd1)::tl1) -> begin
(

let uu____10467 = (pat_var_opt env pat_args hd1)
in (match (uu____10467) with
| FStar_Pervasives_Native.None -> begin
(aux pat_args pattern_vars pattern_var_set formals1 tl1)
end
| FStar_Pervasives_Native.Some (y) -> begin
(

let maybe_pat = (match (xs_opt) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun uu____10499 -> (match (uu____10499) with
| (x, uu____10503) -> begin
(FStar_Syntax_Syntax.bv_eq x (FStar_Pervasives_Native.fst y))
end))))
end)
in (match ((not (maybe_pat))) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals1 tl1)
end
| uu____10506 -> begin
(

let fvs = (FStar_Syntax_Free.names (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____10509 = (

let uu____10510 = (FStar_Util.set_is_subset_of fvs pattern_var_set)
in (not (uu____10510)))
in (match (uu____10509) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals1 tl1)
end
| uu____10513 -> begin
(

let uu____10514 = (FStar_Util.set_add (FStar_Pervasives_Native.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) uu____10514 formals1 tl1))
end)))
end))
end))
end
| uu____10520 -> begin
(failwith "Impossible")
end))
in (

let uu____10531 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] uu____10531 all_formals args)))
end)))
end))
in (

let solve_both_pats = (fun wl1 uu____10571 uu____10572 r -> (match (((uu____10571), (uu____10572))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
(

let uu____10686 = ((FStar_Syntax_Unionfind.equiv u1 u2) && (binders_eq xs ys))
in (match (uu____10686) with
| true -> begin
(

let uu____10687 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____10687))
end
| uu____10688 -> begin
(

let xs1 = (sn_binders env xs)
in (

let ys1 = (sn_binders env ys)
in (

let zs = (intersect_vars xs1 ys1)
in ((

let uu____10702 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10702) with
| true -> begin
(

let uu____10703 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____10704 = (FStar_Syntax_Print.binders_to_string ", " ys1)
in (

let uu____10705 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (

let uu____10706 = (FStar_Syntax_Print.term_to_string k1)
in (

let uu____10707 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" uu____10703 uu____10704 uu____10705 uu____10706 uu____10707))))))
end
| uu____10708 -> begin
()
end));
(

let subst_k = (fun k xs2 args -> (

let xs_len = (FStar_List.length xs2)
in (

let args_len = (FStar_List.length args)
in (match ((xs_len = args_len)) with
| true -> begin
(

let uu____10755 = (FStar_Syntax_Util.subst_of_list xs2 args)
in (FStar_Syntax_Subst.subst uu____10755 k))
end
| uu____10757 -> begin
(match ((args_len < xs_len)) with
| true -> begin
(

let uu____10768 = (FStar_Util.first_N args_len xs2)
in (match (uu____10768) with
| (xs3, xs_rest) -> begin
(

let k3 = (

let uu____10800 = (FStar_Syntax_Syntax.mk_GTotal k)
in (FStar_Syntax_Util.arrow xs_rest uu____10800))
in (

let uu____10803 = (FStar_Syntax_Util.subst_of_list xs3 args)
in (FStar_Syntax_Subst.subst uu____10803 k3)))
end))
end
| uu____10805 -> begin
(

let uu____10806 = (

let uu____10807 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____10808 = (FStar_Syntax_Print.binders_to_string ", " xs2)
in (

let uu____10809 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" uu____10807 uu____10808 uu____10809))))
in (failwith uu____10806))
end)
end))))
in (

let uu____10810 = (

let uu____10816 = (

let uu____10824 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals uu____10824))
in (match (uu____10816) with
| (bs, k1') -> begin
(

let uu____10842 = (

let uu____10850 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals uu____10850))
in (match (uu____10842) with
| (cs, k2') -> begin
(

let k1'_xs = (subst_k k1' bs args1)
in (

let k2'_ys = (subst_k k2' cs args2)
in (

let sub_prob = (

let uu____10871 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys FStar_Pervasives_Native.None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_63 -> FStar_TypeChecker_Common.TProb (_0_63)) uu____10871))
in (

let uu____10876 = (

let uu____10879 = (

let uu____10880 = (FStar_Syntax_Subst.compress k1')
in uu____10880.FStar_Syntax_Syntax.n)
in (

let uu____10883 = (

let uu____10884 = (FStar_Syntax_Subst.compress k2')
in uu____10884.FStar_Syntax_Syntax.n)
in ((uu____10879), (uu____10883))))
in (match (uu____10876) with
| (FStar_Syntax_Syntax.Tm_type (uu____10892), uu____10893) -> begin
((k1'), ((sub_prob)::[]))
end
| (uu____10897, FStar_Syntax_Syntax.Tm_type (uu____10898)) -> begin
((k2'), ((sub_prob)::[]))
end
| uu____10902 -> begin
(

let uu____10905 = (FStar_Syntax_Util.type_u ())
in (match (uu____10905) with
| (t, uu____10914) -> begin
(

let uu____10915 = (new_uvar r zs t)
in (match (uu____10915) with
| (k_zs, uu____10924) -> begin
(

let kprob = (

let uu____10926 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k_zs FStar_Pervasives_Native.None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_64 -> FStar_TypeChecker_Common.TProb (_0_64)) uu____10926))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end)))))
end))
end))
in (match (uu____10810) with
| (k_u', sub_probs) -> begin
(

let uu____10940 = (

let uu____10948 = (

let uu____10949 = (new_uvar r zs k_u')
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10949))
in (

let uu____10954 = (

let uu____10957 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs1 uu____10957))
in (

let uu____10960 = (

let uu____10963 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys1 uu____10963))
in ((uu____10948), (uu____10954), (uu____10960)))))
in (match (uu____10940) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs1 u_zs)
in (

let uu____10982 = (occurs_check env wl1 ((u1), (k1)) sub1)
in (match (uu____10982) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occcurs check")
end
| uu____10990 -> begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in (

let uu____10994 = (FStar_Syntax_Unionfind.equiv u1 u2)
in (match (uu____10994) with
| true -> begin
(

let wl2 = (solve_prob orig FStar_Pervasives_Native.None ((sol1)::[]) wl1)
in (solve env wl2))
end
| uu____10996 -> begin
(

let sub2 = (u_abs knew2 ys1 u_zs)
in (

let uu____10998 = (occurs_check env wl1 ((u2), (k2)) sub2)
in (match (uu____10998) with
| (occurs_ok1, msg1) -> begin
(match ((not (occurs_ok1))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occurs check")
end
| uu____11006 -> begin
(

let sol2 = TERM (((((u2), (k2))), (sub2)))
in (

let wl2 = (solve_prob orig FStar_Pervasives_Native.None ((sol1)::(sol2)::[]) wl1)
in (solve env (attempt sub_probs wl2))))
end)
end)))
end)))
end)
end)))
end))
end)));
))))
end))
end))
in (

let solve_one_pat = (fun uu____11030 uu____11031 -> (match (((uu____11030), (uu____11031))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
((

let uu____11095 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11095) with
| true -> begin
(

let uu____11096 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____11097 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" uu____11096 uu____11097)))
end
| uu____11098 -> begin
()
end));
(

let uu____11099 = (FStar_Syntax_Unionfind.equiv u1 u2)
in (match (uu____11099) with
| true -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____11113 uu____11114 -> (match (((uu____11113), (uu____11114))) with
| ((a, uu____11124), (t21, uu____11126)) -> begin
(

let uu____11131 = (

let uu____11134 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig uu____11134 FStar_TypeChecker_Common.EQ t21 FStar_Pervasives_Native.None "flex-flex index"))
in (FStar_All.pipe_right uu____11131 (fun _0_65 -> FStar_TypeChecker_Common.TProb (_0_65))))
end)) xs args2)
in (

let guard = (

let uu____11138 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) FStar_Pervasives_Native.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____11138))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))))
end
| uu____11145 -> begin
(

let t21 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t21)
in (

let uu____11149 = (occurs_check env wl ((u1), (k1)) t21)
in (match (uu____11149) with
| (occurs_ok, uu____11154) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in (

let uu____11159 = (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars))
in (match (uu____11159) with
| true -> begin
(

let sol = (

let uu____11161 = (

let uu____11166 = (u_abs k1 xs t21)
in ((((u1), (k1))), (uu____11166)))
in TERM (uu____11161))
in (

let wl1 = (solve_prob orig FStar_Pervasives_Native.None ((sol)::[]) wl)
in (solve env wl1)))
end
| uu____11170 -> begin
(

let uu____11171 = (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok))
in (match (uu____11171) with
| true -> begin
(

let uu____11172 = (force_quasi_pattern (FStar_Pervasives_Native.Some (xs)) ((t21), (u2), (k2), (args2)))
in (match (uu____11172) with
| (sol, (uu____11182, u21, k21, ys)) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____11192 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____11192) with
| true -> begin
(

let uu____11193 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" uu____11193))
end
| uu____11194 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____11198 -> begin
(giveup env "impossible" orig)
end);
))
end))
end
| uu____11199 -> begin
(giveup_or_defer1 orig "flex-flex constraint")
end))
end)))
end))))
end));
)
end))
in (

let uu____11200 = lhs
in (match (uu____11200) with
| (t1, u1, k1, args1) -> begin
(

let uu____11205 = rhs
in (match (uu____11205) with
| (t2, u2, k2, args2) -> begin
(

let maybe_pat_vars1 = (pat_vars env [] args1)
in (

let maybe_pat_vars2 = (pat_vars env [] args2)
in (

let r = t2.FStar_Syntax_Syntax.pos
in (match (((maybe_pat_vars1), (maybe_pat_vars2))) with
| (FStar_Pervasives_Native.Some (xs), FStar_Pervasives_Native.Some (ys)) -> begin
(solve_both_pats wl ((u1), (k1), (xs), (args1)) ((u2), (k2), (ys), (args2)) t2.FStar_Syntax_Syntax.pos)
end
| (FStar_Pervasives_Native.Some (xs), FStar_Pervasives_Native.None) -> begin
(solve_one_pat ((t1), (u1), (k1), (xs)) rhs)
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (ys)) -> begin
(solve_one_pat ((t2), (u2), (k2), (ys)) lhs)
end
| uu____11231 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: neither side is a pattern")
end
| uu____11236 -> begin
(

let uu____11237 = (force_quasi_pattern FStar_Pervasives_Native.None ((t1), (u1), (k1), (args1)))
in (match (uu____11237) with
| (sol, uu____11244) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____11247 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____11247) with
| true -> begin
(

let uu____11248 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" uu____11248))
end
| uu____11249 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____11253 -> begin
(giveup env "impossible" orig)
end);
))
end))
end)
end))))
end))
end)))))
end))
in (

let orig = FStar_TypeChecker_Common.TProb (problem)
in (

let uu____11255 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____11255) with
| true -> begin
(

let uu____11256 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____11256))
end
| uu____11257 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in (

let uu____11260 = (FStar_Util.physical_equality t1 t2)
in (match (uu____11260) with
| true -> begin
(

let uu____11261 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____11261))
end
| uu____11262 -> begin
((

let uu____11264 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____11264) with
| true -> begin
(

let uu____11265 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" uu____11265))
end
| uu____11266 -> begin
()
end));
(

let r = (FStar_TypeChecker_Env.get_range env)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_bvar (uu____11268), uu____11269) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (uu____11270, FStar_Syntax_Syntax.Tm_bvar (uu____11271)) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (FStar_Syntax_Syntax.Tm_type (u1), FStar_Syntax_Syntax.Tm_type (u2)) -> begin
(solve_one_universe_eq env orig u1 u2 wl)
end
| (FStar_Syntax_Syntax.Tm_arrow (bs1, c1), FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) -> begin
(

let mk_c = (fun c uu___132_11311 -> (match (uu___132_11311) with
| [] -> begin
c
end
| bs -> begin
(

let uu____11325 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____11325))
end))
in (

let uu____11335 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____11335) with
| ((bs11, c11), (bs21, c21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let c12 = (FStar_Syntax_Subst.subst_comp subst1 c11)
in (

let c22 = (FStar_Syntax_Subst.subst_comp subst1 c21)
in (

let rel = (

let uu____11428 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____11428) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____11429 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (

let uu____11430 = (mk_problem scope orig c12 rel c22 FStar_Pervasives_Native.None "function co-domain")
in (FStar_All.pipe_left (fun _0_66 -> FStar_TypeChecker_Common.CProb (_0_66)) uu____11430)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___133_11482 -> (match (uu___133_11482) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____11507 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____11507) with
| ((bs11, tbody11), (bs21, tbody21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let uu____11594 = (

let uu____11597 = (FStar_Syntax_Subst.subst subst1 tbody11)
in (

let uu____11598 = (FStar_Syntax_Subst.subst subst1 tbody21)
in (mk_problem scope orig uu____11597 problem.FStar_TypeChecker_Common.relation uu____11598 FStar_Pervasives_Native.None "lambda co-domain")))
in (FStar_All.pipe_left (fun _0_67 -> FStar_TypeChecker_Common.TProb (_0_67)) uu____11594))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (uu____11601), uu____11602) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____11620) -> begin
true
end
| uu____11630 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____11649 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____11655 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let uu____11658 = (

let uu____11669 = (maybe_eta t1)
in (

let uu____11674 = (maybe_eta t2)
in ((uu____11669), (uu____11674))))
in (match (uu____11658) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___166_11706 = problem
in {FStar_TypeChecker_Common.pid = uu___166_11706.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___166_11706.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___166_11706.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_11706.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___166_11706.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___166_11706.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_11706.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_11706.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____11725 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____11725) with
| true -> begin
(

let uu____11726 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____11726 t_abs wl))
end
| uu____11730 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____11747 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____11747) with
| true -> begin
(

let uu____11748 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____11748 t_abs wl))
end
| uu____11752 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| uu____11753 -> begin
(failwith "Impossible: at least one side is an abstraction")
end))))
end
| (uu____11764, FStar_Syntax_Syntax.Tm_abs (uu____11765)) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____11783) -> begin
true
end
| uu____11793 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____11812 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____11818 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let uu____11821 = (

let uu____11832 = (maybe_eta t1)
in (

let uu____11837 = (maybe_eta t2)
in ((uu____11832), (uu____11837))))
in (match (uu____11821) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___166_11869 = problem
in {FStar_TypeChecker_Common.pid = uu___166_11869.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___166_11869.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___166_11869.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_11869.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___166_11869.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___166_11869.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_11869.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_11869.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____11888 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____11888) with
| true -> begin
(

let uu____11889 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____11889 t_abs wl))
end
| uu____11893 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____11910 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____11910) with
| true -> begin
(

let uu____11911 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____11911 t_abs wl))
end
| uu____11915 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| uu____11916 -> begin
(failwith "Impossible: at least one side is an abstraction")
end))))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____11927), FStar_Syntax_Syntax.Tm_refine (uu____11928)) -> begin
(

let uu____11937 = (as_refinement env wl t1)
in (match (uu____11937) with
| (x1, phi1) -> begin
(

let uu____11942 = (as_refinement env wl t2)
in (match (uu____11942) with
| (x2, phi2) -> begin
(

let base_prob = (

let uu____11948 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _0_68 -> FStar_TypeChecker_Common.TProb (_0_68)) uu____11948))
in (

let x11 = (FStar_Syntax_Syntax.freshen_bv x1)
in (

let subst1 = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x11))))::[]
in (

let phi11 = (FStar_Syntax_Subst.subst subst1 phi1)
in (

let phi21 = (FStar_Syntax_Subst.subst subst1 phi2)
in (

let env1 = (FStar_TypeChecker_Env.push_bv env x11)
in (

let mk_imp1 = (fun imp phi12 phi22 -> (

let uu____11981 = (imp phi12 phi22)
in (FStar_All.pipe_right uu____11981 (guard_on_element wl problem x11))))
in (

let fallback = (fun uu____11985 -> (

let impl = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp1 FStar_Syntax_Util.mk_iff phi11 phi21)
end
| uu____11987 -> begin
(mk_imp1 FStar_Syntax_Util.mk_imp phi11 phi21)
end)
in (

let guard = (

let uu____11991 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____11991 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env1 (attempt ((base_prob)::[]) wl1))))))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let ref_prob = (

let uu____11998 = (

let uu____12001 = (

let uu____12002 = (FStar_Syntax_Syntax.mk_binder x11)
in (uu____12002)::(p_scope orig))
in (mk_problem uu____12001 orig phi11 FStar_TypeChecker_Common.EQ phi21 FStar_Pervasives_Native.None "refinement formula"))
in (FStar_All.pipe_left (fun _0_69 -> FStar_TypeChecker_Common.TProb (_0_69)) uu____11998))
in (

let uu____12005 = (solve env1 (

let uu___167_12007 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___167_12007.ctr; defer_ok = false; smt_ok = uu___167_12007.smt_ok; tcenv = uu___167_12007.tcenv}))
in (match (uu____12005) with
| Failed (uu____12011) -> begin
(fallback ())
end
| Success (uu____12014) -> begin
(

let guard = (

let uu____12018 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (

let uu____12021 = (

let uu____12022 = (FStar_All.pipe_right (p_guard ref_prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____12022 (guard_on_element wl problem x11)))
in (FStar_Syntax_Util.mk_conj uu____12018 uu____12021)))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (

let wl2 = (

let uu___168_12029 = wl1
in {attempting = uu___168_12029.attempting; wl_deferred = uu___168_12029.wl_deferred; ctr = (wl1.ctr + (Prims.parse_int "1")); defer_ok = uu___168_12029.defer_ok; smt_ok = uu___168_12029.smt_ok; tcenv = uu___168_12029.tcenv})
in (solve env1 (attempt ((base_prob)::[]) wl2)))))
end)))
end
| uu____12030 -> begin
(fallback ())
end)))))))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____12031), FStar_Syntax_Syntax.Tm_uvar (uu____12032)) -> begin
(

let uu____12053 = (destruct_flex_t t1)
in (

let uu____12054 = (destruct_flex_t t2)
in (flex_flex1 orig uu____12053 uu____12054)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12055); FStar_Syntax_Syntax.tk = uu____12056; FStar_Syntax_Syntax.pos = uu____12057; FStar_Syntax_Syntax.vars = uu____12058}, uu____12059), FStar_Syntax_Syntax.Tm_uvar (uu____12060)) -> begin
(

let uu____12095 = (destruct_flex_t t1)
in (

let uu____12096 = (destruct_flex_t t2)
in (flex_flex1 orig uu____12095 uu____12096)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____12097), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12098); FStar_Syntax_Syntax.tk = uu____12099; FStar_Syntax_Syntax.pos = uu____12100; FStar_Syntax_Syntax.vars = uu____12101}, uu____12102)) -> begin
(

let uu____12137 = (destruct_flex_t t1)
in (

let uu____12138 = (destruct_flex_t t2)
in (flex_flex1 orig uu____12137 uu____12138)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12139); FStar_Syntax_Syntax.tk = uu____12140; FStar_Syntax_Syntax.pos = uu____12141; FStar_Syntax_Syntax.vars = uu____12142}, uu____12143), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12144); FStar_Syntax_Syntax.tk = uu____12145; FStar_Syntax_Syntax.pos = uu____12146; FStar_Syntax_Syntax.vars = uu____12147}, uu____12148)) -> begin
(

let uu____12197 = (destruct_flex_t t1)
in (

let uu____12198 = (destruct_flex_t t2)
in (flex_flex1 orig uu____12197 uu____12198)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____12199), uu____12200) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(

let uu____12211 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____12211 t2 wl))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12215); FStar_Syntax_Syntax.tk = uu____12216; FStar_Syntax_Syntax.pos = uu____12217; FStar_Syntax_Syntax.vars = uu____12218}, uu____12219), uu____12220) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(

let uu____12245 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____12245 t2 wl))
end
| (uu____12249, FStar_Syntax_Syntax.Tm_uvar (uu____12250)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (uu____12261, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12262); FStar_Syntax_Syntax.tk = uu____12263; FStar_Syntax_Syntax.pos = uu____12264; FStar_Syntax_Syntax.vars = uu____12265}, uu____12266)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____12291), FStar_Syntax_Syntax.Tm_type (uu____12292)) -> begin
(solve_t' env (

let uu___169_12304 = problem
in {FStar_TypeChecker_Common.pid = uu___169_12304.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___169_12304.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___169_12304.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___169_12304.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___169_12304.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___169_12304.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___169_12304.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___169_12304.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___169_12304.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12305); FStar_Syntax_Syntax.tk = uu____12306; FStar_Syntax_Syntax.pos = uu____12307; FStar_Syntax_Syntax.vars = uu____12308}, uu____12309), FStar_Syntax_Syntax.Tm_type (uu____12310)) -> begin
(solve_t' env (

let uu___169_12336 = problem
in {FStar_TypeChecker_Common.pid = uu___169_12336.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___169_12336.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___169_12336.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___169_12336.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___169_12336.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___169_12336.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___169_12336.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___169_12336.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___169_12336.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____12337), FStar_Syntax_Syntax.Tm_arrow (uu____12338)) -> begin
(solve_t' env (

let uu___169_12357 = problem
in {FStar_TypeChecker_Common.pid = uu___169_12357.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___169_12357.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___169_12357.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___169_12357.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___169_12357.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___169_12357.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___169_12357.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___169_12357.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___169_12357.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12358); FStar_Syntax_Syntax.tk = uu____12359; FStar_Syntax_Syntax.pos = uu____12360; FStar_Syntax_Syntax.vars = uu____12361}, uu____12362), FStar_Syntax_Syntax.Tm_arrow (uu____12363)) -> begin
(solve_t' env (

let uu___169_12396 = problem
in {FStar_TypeChecker_Common.pid = uu___169_12396.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___169_12396.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___169_12396.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___169_12396.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___169_12396.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___169_12396.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___169_12396.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___169_12396.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___169_12396.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____12397), uu____12398) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____12409 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____12411 = (

let uu____12412 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____12412))
in (match (uu____12411) with
| true -> begin
(

let uu____12413 = (FStar_All.pipe_left (fun _0_70 -> FStar_TypeChecker_Common.TProb (_0_70)) (

let uu___170_12417 = problem
in {FStar_TypeChecker_Common.pid = uu___170_12417.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___170_12417.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___170_12417.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___170_12417.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___170_12417.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___170_12417.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___170_12417.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___170_12417.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___170_12417.FStar_TypeChecker_Common.rank}))
in (

let uu____12418 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____12413 uu____12418 t2 wl)))
end
| uu____12422 -> begin
(

let uu____12423 = (base_and_refinement env wl t2)
in (match (uu____12423) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12453 = (FStar_All.pipe_left (fun _0_71 -> FStar_TypeChecker_Common.TProb (_0_71)) (

let uu___171_12457 = problem
in {FStar_TypeChecker_Common.pid = uu___171_12457.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___171_12457.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___171_12457.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___171_12457.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___171_12457.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___171_12457.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___171_12457.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___171_12457.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___171_12457.FStar_TypeChecker_Common.rank}))
in (

let uu____12458 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____12453 uu____12458 t_base wl)))
end
| FStar_Pervasives_Native.Some (y, phi) -> begin
(

let y' = (

let uu___172_12473 = y
in {FStar_Syntax_Syntax.ppname = uu___172_12473.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___172_12473.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let base_prob = (

let uu____12476 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_72 -> FStar_TypeChecker_Common.TProb (_0_72)) uu____12476))
in (

let guard = (

let uu____12484 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____12484 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl1)))))))
end)
end))
end)))
end)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12490); FStar_Syntax_Syntax.tk = uu____12491; FStar_Syntax_Syntax.pos = uu____12492; FStar_Syntax_Syntax.vars = uu____12493}, uu____12494), uu____12495) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____12520 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____12522 = (

let uu____12523 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____12523))
in (match (uu____12522) with
| true -> begin
(

let uu____12524 = (FStar_All.pipe_left (fun _0_73 -> FStar_TypeChecker_Common.TProb (_0_73)) (

let uu___170_12528 = problem
in {FStar_TypeChecker_Common.pid = uu___170_12528.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___170_12528.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___170_12528.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___170_12528.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___170_12528.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___170_12528.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___170_12528.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___170_12528.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___170_12528.FStar_TypeChecker_Common.rank}))
in (

let uu____12529 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____12524 uu____12529 t2 wl)))
end
| uu____12533 -> begin
(

let uu____12534 = (base_and_refinement env wl t2)
in (match (uu____12534) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12564 = (FStar_All.pipe_left (fun _0_74 -> FStar_TypeChecker_Common.TProb (_0_74)) (

let uu___171_12568 = problem
in {FStar_TypeChecker_Common.pid = uu___171_12568.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___171_12568.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___171_12568.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___171_12568.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___171_12568.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___171_12568.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___171_12568.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___171_12568.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___171_12568.FStar_TypeChecker_Common.rank}))
in (

let uu____12569 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____12564 uu____12569 t_base wl)))
end
| FStar_Pervasives_Native.Some (y, phi) -> begin
(

let y' = (

let uu___172_12584 = y
in {FStar_Syntax_Syntax.ppname = uu___172_12584.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___172_12584.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let base_prob = (

let uu____12587 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_75 -> FStar_TypeChecker_Common.TProb (_0_75)) uu____12587))
in (

let guard = (

let uu____12595 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____12595 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl1)))))))
end)
end))
end)))
end)
end
| (uu____12601, FStar_Syntax_Syntax.Tm_uvar (uu____12602)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| uu____12613 -> begin
(

let uu____12614 = (base_and_refinement env wl t1)
in (match (uu____12614) with
| (t_base, uu____12625) -> begin
(solve_t env (

let uu___173_12641 = problem
in {FStar_TypeChecker_Common.pid = uu___173_12641.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___173_12641.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___173_12641.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___173_12641.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___173_12641.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___173_12641.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___173_12641.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___173_12641.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (uu____12644, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12645); FStar_Syntax_Syntax.tk = uu____12646; FStar_Syntax_Syntax.pos = uu____12647; FStar_Syntax_Syntax.vars = uu____12648}, uu____12649)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| uu____12674 -> begin
(

let uu____12675 = (base_and_refinement env wl t1)
in (match (uu____12675) with
| (t_base, uu____12686) -> begin
(solve_t env (

let uu___173_12702 = problem
in {FStar_TypeChecker_Common.pid = uu___173_12702.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___173_12702.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___173_12702.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___173_12702.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___173_12702.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___173_12702.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___173_12702.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___173_12702.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (FStar_Syntax_Syntax.Tm_refine (uu____12705), uu____12706) -> begin
(

let t21 = (

let uu____12714 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement uu____12714))
in (solve_t env (

let uu___174_12728 = problem
in {FStar_TypeChecker_Common.pid = uu___174_12728.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___174_12728.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___174_12728.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___174_12728.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___174_12728.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___174_12728.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___174_12728.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___174_12728.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___174_12728.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____12729, FStar_Syntax_Syntax.Tm_refine (uu____12730)) -> begin
(

let t11 = (

let uu____12738 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement uu____12738))
in (solve_t env (

let uu___175_12752 = problem
in {FStar_TypeChecker_Common.pid = uu___175_12752.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___175_12752.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___175_12752.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___175_12752.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___175_12752.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___175_12752.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___175_12752.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___175_12752.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___175_12752.FStar_TypeChecker_Common.rank}) wl))
end
| (FStar_Syntax_Syntax.Tm_match (uu____12755), uu____12756) -> begin
(

let head1 = (

let uu____12774 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____12774 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____12805 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____12805 FStar_Pervasives_Native.fst))
in (

let uu____12833 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____12833) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____12842 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____12842) with
| true -> begin
(

let guard = (

let uu____12849 = (

let uu____12850 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____12850 = FStar_Syntax_Util.Equal))
in (match (uu____12849) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____12852 -> begin
(

let uu____12853 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_76 -> FStar_Pervasives_Native.Some (_0_76)) uu____12853))
end))
in (

let uu____12855 = (solve_prob orig guard [] wl)
in (solve env uu____12855)))
end
| uu____12856 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____12857 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____12858), uu____12859) -> begin
(

let head1 = (

let uu____12867 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____12867 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____12898 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____12898 FStar_Pervasives_Native.fst))
in (

let uu____12926 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____12926) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____12935 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____12935) with
| true -> begin
(

let guard = (

let uu____12942 = (

let uu____12943 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____12943 = FStar_Syntax_Util.Equal))
in (match (uu____12942) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____12945 -> begin
(

let uu____12946 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_77 -> FStar_Pervasives_Native.Some (_0_77)) uu____12946))
end))
in (

let uu____12948 = (solve_prob orig guard [] wl)
in (solve env uu____12948)))
end
| uu____12949 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____12950 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_name (uu____12951), uu____12952) -> begin
(

let head1 = (

let uu____12956 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____12956 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____12987 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____12987 FStar_Pervasives_Native.fst))
in (

let uu____13015 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13015) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13024 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13024) with
| true -> begin
(

let guard = (

let uu____13031 = (

let uu____13032 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13032 = FStar_Syntax_Util.Equal))
in (match (uu____13031) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13034 -> begin
(

let uu____13035 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_78 -> FStar_Pervasives_Native.Some (_0_78)) uu____13035))
end))
in (

let uu____13037 = (solve_prob orig guard [] wl)
in (solve env uu____13037)))
end
| uu____13038 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13039 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_constant (uu____13040), uu____13041) -> begin
(

let head1 = (

let uu____13045 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13045 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13076 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13076 FStar_Pervasives_Native.fst))
in (

let uu____13104 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13104) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13113 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13113) with
| true -> begin
(

let guard = (

let uu____13120 = (

let uu____13121 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13121 = FStar_Syntax_Util.Equal))
in (match (uu____13120) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13123 -> begin
(

let uu____13124 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_79 -> FStar_Pervasives_Native.Some (_0_79)) uu____13124))
end))
in (

let uu____13126 = (solve_prob orig guard [] wl)
in (solve env uu____13126)))
end
| uu____13127 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13128 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____13129), uu____13130) -> begin
(

let head1 = (

let uu____13134 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13134 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13165 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13165 FStar_Pervasives_Native.fst))
in (

let uu____13193 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13193) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13202 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13202) with
| true -> begin
(

let guard = (

let uu____13209 = (

let uu____13210 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13210 = FStar_Syntax_Util.Equal))
in (match (uu____13209) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13212 -> begin
(

let uu____13213 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_80 -> FStar_Pervasives_Native.Some (_0_80)) uu____13213))
end))
in (

let uu____13215 = (solve_prob orig guard [] wl)
in (solve env uu____13215)))
end
| uu____13216 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13217 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____13218), uu____13219) -> begin
(

let head1 = (

let uu____13232 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13232 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13263 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13263 FStar_Pervasives_Native.fst))
in (

let uu____13291 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13291) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13300 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13300) with
| true -> begin
(

let guard = (

let uu____13307 = (

let uu____13308 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13308 = FStar_Syntax_Util.Equal))
in (match (uu____13307) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13310 -> begin
(

let uu____13311 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_81 -> FStar_Pervasives_Native.Some (_0_81)) uu____13311))
end))
in (

let uu____13313 = (solve_prob orig guard [] wl)
in (solve env uu____13313)))
end
| uu____13314 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13315 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____13316, FStar_Syntax_Syntax.Tm_match (uu____13317)) -> begin
(

let head1 = (

let uu____13335 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13335 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13366 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13366 FStar_Pervasives_Native.fst))
in (

let uu____13394 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13394) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13403 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13403) with
| true -> begin
(

let guard = (

let uu____13410 = (

let uu____13411 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13411 = FStar_Syntax_Util.Equal))
in (match (uu____13410) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13413 -> begin
(

let uu____13414 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_82 -> FStar_Pervasives_Native.Some (_0_82)) uu____13414))
end))
in (

let uu____13416 = (solve_prob orig guard [] wl)
in (solve env uu____13416)))
end
| uu____13417 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13418 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____13419, FStar_Syntax_Syntax.Tm_uinst (uu____13420)) -> begin
(

let head1 = (

let uu____13428 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13428 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13459 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13459 FStar_Pervasives_Native.fst))
in (

let uu____13487 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13487) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13496 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13496) with
| true -> begin
(

let guard = (

let uu____13503 = (

let uu____13504 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13504 = FStar_Syntax_Util.Equal))
in (match (uu____13503) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13506 -> begin
(

let uu____13507 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_83 -> FStar_Pervasives_Native.Some (_0_83)) uu____13507))
end))
in (

let uu____13509 = (solve_prob orig guard [] wl)
in (solve env uu____13509)))
end
| uu____13510 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13511 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____13512, FStar_Syntax_Syntax.Tm_name (uu____13513)) -> begin
(

let head1 = (

let uu____13517 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13517 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13548 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13548 FStar_Pervasives_Native.fst))
in (

let uu____13576 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13576) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13585 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13585) with
| true -> begin
(

let guard = (

let uu____13592 = (

let uu____13593 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13593 = FStar_Syntax_Util.Equal))
in (match (uu____13592) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13595 -> begin
(

let uu____13596 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_84 -> FStar_Pervasives_Native.Some (_0_84)) uu____13596))
end))
in (

let uu____13598 = (solve_prob orig guard [] wl)
in (solve env uu____13598)))
end
| uu____13599 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13600 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____13601, FStar_Syntax_Syntax.Tm_constant (uu____13602)) -> begin
(

let head1 = (

let uu____13606 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13606 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13637 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13637 FStar_Pervasives_Native.fst))
in (

let uu____13665 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13665) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13674 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13674) with
| true -> begin
(

let guard = (

let uu____13681 = (

let uu____13682 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13682 = FStar_Syntax_Util.Equal))
in (match (uu____13681) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13684 -> begin
(

let uu____13685 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_85 -> FStar_Pervasives_Native.Some (_0_85)) uu____13685))
end))
in (

let uu____13687 = (solve_prob orig guard [] wl)
in (solve env uu____13687)))
end
| uu____13688 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13689 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____13690, FStar_Syntax_Syntax.Tm_fvar (uu____13691)) -> begin
(

let head1 = (

let uu____13695 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13695 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13726 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13726 FStar_Pervasives_Native.fst))
in (

let uu____13754 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13754) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13763 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13763) with
| true -> begin
(

let guard = (

let uu____13770 = (

let uu____13771 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13771 = FStar_Syntax_Util.Equal))
in (match (uu____13770) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13773 -> begin
(

let uu____13774 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_86 -> FStar_Pervasives_Native.Some (_0_86)) uu____13774))
end))
in (

let uu____13776 = (solve_prob orig guard [] wl)
in (solve env uu____13776)))
end
| uu____13777 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13778 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____13779, FStar_Syntax_Syntax.Tm_app (uu____13780)) -> begin
(

let head1 = (

let uu____13793 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13793 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13824 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13824 FStar_Pervasives_Native.fst))
in (

let uu____13852 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13852) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13861 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13861) with
| true -> begin
(

let guard = (

let uu____13868 = (

let uu____13869 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13869 = FStar_Syntax_Util.Equal))
in (match (uu____13868) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13871 -> begin
(

let uu____13872 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_87 -> FStar_Pervasives_Native.Some (_0_87)) uu____13872))
end))
in (

let uu____13874 = (solve_prob orig guard [] wl)
in (solve env uu____13874)))
end
| uu____13875 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13876 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t11, uu____13878, uu____13879), uu____13880) -> begin
(solve_t' env (

let uu___176_13910 = problem
in {FStar_TypeChecker_Common.pid = uu___176_13910.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___176_13910.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___176_13910.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___176_13910.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___176_13910.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___176_13910.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___176_13910.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___176_13910.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___176_13910.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____13913, FStar_Syntax_Syntax.Tm_ascribed (t21, uu____13915, uu____13916)) -> begin
(solve_t' env (

let uu___177_13946 = problem
in {FStar_TypeChecker_Common.pid = uu___177_13946.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___177_13946.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___177_13946.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___177_13946.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___177_13946.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___177_13946.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___177_13946.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___177_13946.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___177_13946.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_let (uu____13947), uu____13948) -> begin
(

let uu____13956 = (

let uu____13957 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____13958 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____13957 uu____13958)))
in (failwith uu____13956))
end
| (FStar_Syntax_Syntax.Tm_meta (uu____13959), uu____13960) -> begin
(

let uu____13965 = (

let uu____13966 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____13967 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____13966 uu____13967)))
in (failwith uu____13965))
end
| (FStar_Syntax_Syntax.Tm_delayed (uu____13968), uu____13969) -> begin
(

let uu____13984 = (

let uu____13985 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____13986 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____13985 uu____13986)))
in (failwith uu____13984))
end
| (uu____13987, FStar_Syntax_Syntax.Tm_meta (uu____13988)) -> begin
(

let uu____13993 = (

let uu____13994 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____13995 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____13994 uu____13995)))
in (failwith uu____13993))
end
| (uu____13996, FStar_Syntax_Syntax.Tm_delayed (uu____13997)) -> begin
(

let uu____14012 = (

let uu____14013 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____14014 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____14013 uu____14014)))
in (failwith uu____14012))
end
| (uu____14015, FStar_Syntax_Syntax.Tm_let (uu____14016)) -> begin
(

let uu____14024 = (

let uu____14025 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____14026 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____14025 uu____14026)))
in (failwith uu____14024))
end
| uu____14027 -> begin
(giveup env "head tag mismatch" orig)
end));
)
end))))
end)))))))))))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (

let c1 = problem.FStar_TypeChecker_Common.lhs
in (

let c2 = problem.FStar_TypeChecker_Common.rhs
in (

let orig = FStar_TypeChecker_Common.CProb (problem)
in (

let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 FStar_Pervasives_Native.None reason))
in (

let solve_eq = (fun c1_comp c2_comp -> ((

let uu____14059 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____14059) with
| true -> begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end
| uu____14060 -> begin
()
end));
(

let sub_probs = (FStar_List.map2 (fun uu____14074 uu____14075 -> (match (((uu____14074), (uu____14075))) with
| ((a1, uu____14085), (a2, uu____14087)) -> begin
(

let uu____14092 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _0_88 -> FStar_TypeChecker_Common.TProb (_0_88)) uu____14092))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (

let uu____14098 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) FStar_Pervasives_Native.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____14098))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))));
))
in (

let solve_sub = (fun c11 edge c21 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let lift_c1 = (fun uu____14119 -> (

let wp = (match (c11.FStar_Syntax_Syntax.effect_args) with
| ((wp1, uu____14126))::[] -> begin
wp1
end
| uu____14139 -> begin
(

let uu____14145 = (

let uu____14146 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c11.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" uu____14146))
in (failwith uu____14145))
end)
in (

let uu____14149 = (

let uu____14155 = (

let uu____14156 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c11.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____14156))
in (uu____14155)::[])
in {FStar_Syntax_Syntax.comp_univs = c11.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c21.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c11.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____14149; FStar_Syntax_Syntax.flags = c11.FStar_Syntax_Syntax.flags})))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____14157 = (lift_c1 ())
in (solve_eq uu____14157 c21))
end
| uu____14158 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___134_14162 -> (match (uu___134_14162) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| uu____14163 -> begin
false
end))))
in (

let uu____14164 = (match (((c11.FStar_Syntax_Syntax.effect_args), (c21.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____14188))::uu____14189, ((wp2, uu____14191))::uu____14192) -> begin
((wp1), (wp2))
end
| uu____14233 -> begin
(

let uu____14246 = (

let uu____14247 = (

let uu____14250 = (

let uu____14251 = (FStar_Syntax_Print.lid_to_string c11.FStar_Syntax_Syntax.effect_name)
in (

let uu____14252 = (FStar_Syntax_Print.lid_to_string c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____14251 uu____14252)))
in ((uu____14250), (env.FStar_TypeChecker_Env.range)))
in FStar_Errors.Error (uu____14247))
in (FStar_Pervasives.raise uu____14246))
end)
in (match (uu____14164) with
| (wpc1, wpc2) -> begin
(

let uu____14269 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____14269) with
| true -> begin
(

let uu____14272 = (problem_using_guard orig c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ FStar_Pervasives_Native.None "result type")
in (solve_t env uu____14272 wl))
end
| uu____14275 -> begin
(

let uu____14276 = (

let uu____14280 = (FStar_TypeChecker_Env.effect_decl_opt env c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.must uu____14280))
in (match (uu____14276) with
| (c2_decl, qualifiers) -> begin
(

let uu____14292 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____14292) with
| true -> begin
(

let c1_repr = (

let uu____14295 = (

let uu____14296 = (

let uu____14297 = (lift_c1 ())
in (FStar_Syntax_Syntax.mk_Comp uu____14297))
in (

let uu____14298 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____14296 uu____14298)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____14295))
in (

let c2_repr = (

let uu____14300 = (

let uu____14301 = (FStar_Syntax_Syntax.mk_Comp c21)
in (

let uu____14302 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____14301 uu____14302)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____14300))
in (

let prob = (

let uu____14304 = (

let uu____14307 = (

let uu____14308 = (FStar_Syntax_Print.term_to_string c1_repr)
in (

let uu____14309 = (FStar_Syntax_Print.term_to_string c2_repr)
in (FStar_Util.format2 "sub effect repr: %s <: %s" uu____14308 uu____14309)))
in (sub_prob c1_repr problem.FStar_TypeChecker_Common.relation c2_repr uu____14307))
in FStar_TypeChecker_Common.TProb (uu____14304))
in (

let wl1 = (

let uu____14311 = (

let uu____14313 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in FStar_Pervasives_Native.Some (uu____14313))
in (solve_prob orig uu____14311 [] wl))
in (solve env (attempt ((prob)::[]) wl1))))))
end
| uu____14316 -> begin
(

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____14318 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____14320 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14320) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____14321 -> begin
()
end));
(

let uu____14322 = (

let uu____14325 = (

let uu____14326 = (

let uu____14336 = (

let uu____14337 = (

let uu____14338 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (uu____14338)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____14337 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (

let uu____14339 = (

let uu____14341 = (FStar_Syntax_Syntax.as_arg c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____14342 = (

let uu____14344 = (

let uu____14345 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____14345))
in (uu____14344)::[])
in (uu____14341)::uu____14342))
in ((uu____14336), (uu____14339))))
in FStar_Syntax_Syntax.Tm_app (uu____14326))
in (FStar_Syntax_Syntax.mk uu____14325))
in (uu____14322 (FStar_Pervasives_Native.Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r));
)
end
| uu____14355 -> begin
(

let uu____14356 = (

let uu____14359 = (

let uu____14360 = (

let uu____14370 = (

let uu____14371 = (

let uu____14372 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (uu____14372)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____14371 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (

let uu____14373 = (

let uu____14375 = (FStar_Syntax_Syntax.as_arg c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____14376 = (

let uu____14378 = (FStar_Syntax_Syntax.as_arg wpc2)
in (

let uu____14379 = (

let uu____14381 = (

let uu____14382 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____14382))
in (uu____14381)::[])
in (uu____14378)::uu____14379))
in (uu____14375)::uu____14376))
in ((uu____14370), (uu____14373))))
in FStar_Syntax_Syntax.Tm_app (uu____14360))
in (FStar_Syntax_Syntax.mk uu____14359))
in (uu____14356 (FStar_Pervasives_Native.Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r))
end)
end)
in (

let base_prob = (

let uu____14393 = (sub_prob c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _0_89 -> FStar_TypeChecker_Common.TProb (_0_89)) uu____14393))
in (

let wl1 = (

let uu____14399 = (

let uu____14401 = (

let uu____14404 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____14404 g))
in (FStar_All.pipe_left (fun _0_90 -> FStar_Pervasives_Native.Some (_0_90)) uu____14401))
in (solve_prob orig uu____14399 [] wl))
in (solve env (attempt ((base_prob)::[]) wl1)))))
end))
end))
end))
end)))
end))))
in (

let uu____14414 = (FStar_Util.physical_equality c1 c2)
in (match (uu____14414) with
| true -> begin
(

let uu____14415 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____14415))
end
| uu____14416 -> begin
((

let uu____14418 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14418) with
| true -> begin
(

let uu____14419 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____14420 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____14419 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____14420)))
end
| uu____14421 -> begin
()
end));
(

let uu____14422 = (

let uu____14425 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____14426 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____14425), (uu____14426))))
in (match (uu____14422) with
| (c11, c21) -> begin
(match (((c11.FStar_Syntax_Syntax.n), (c21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____14430), FStar_Syntax_Syntax.Total (t2, uu____14432)) when (FStar_Syntax_Util.non_informative t2) -> begin
(

let uu____14445 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____14445 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____14448), FStar_Syntax_Syntax.Total (uu____14449)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| (FStar_Syntax_Syntax.Total (t1, uu____14461), FStar_Syntax_Syntax.Total (t2, uu____14463)) -> begin
(

let uu____14476 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____14476 wl))
end
| (FStar_Syntax_Syntax.GTotal (t1, uu____14480), FStar_Syntax_Syntax.GTotal (t2, uu____14482)) -> begin
(

let uu____14495 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____14495 wl))
end
| (FStar_Syntax_Syntax.Total (t1, uu____14499), FStar_Syntax_Syntax.GTotal (t2, uu____14501)) -> begin
(

let uu____14514 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____14514 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____14517), FStar_Syntax_Syntax.Comp (uu____14518)) -> begin
(

let uu____14524 = (

let uu___178_14527 = problem
in (

let uu____14530 = (

let uu____14531 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____14531))
in {FStar_TypeChecker_Common.pid = uu___178_14527.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____14530; FStar_TypeChecker_Common.relation = uu___178_14527.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___178_14527.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___178_14527.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___178_14527.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___178_14527.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___178_14527.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___178_14527.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___178_14527.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____14524 wl))
end
| (FStar_Syntax_Syntax.Total (uu____14532), FStar_Syntax_Syntax.Comp (uu____14533)) -> begin
(

let uu____14539 = (

let uu___178_14542 = problem
in (

let uu____14545 = (

let uu____14546 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____14546))
in {FStar_TypeChecker_Common.pid = uu___178_14542.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____14545; FStar_TypeChecker_Common.relation = uu___178_14542.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___178_14542.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___178_14542.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___178_14542.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___178_14542.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___178_14542.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___178_14542.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___178_14542.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____14539 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____14547), FStar_Syntax_Syntax.GTotal (uu____14548)) -> begin
(

let uu____14554 = (

let uu___179_14557 = problem
in (

let uu____14560 = (

let uu____14561 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____14561))
in {FStar_TypeChecker_Common.pid = uu___179_14557.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___179_14557.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___179_14557.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____14560; FStar_TypeChecker_Common.element = uu___179_14557.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___179_14557.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___179_14557.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___179_14557.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___179_14557.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___179_14557.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____14554 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____14562), FStar_Syntax_Syntax.Total (uu____14563)) -> begin
(

let uu____14569 = (

let uu___179_14572 = problem
in (

let uu____14575 = (

let uu____14576 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____14576))
in {FStar_TypeChecker_Common.pid = uu___179_14572.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___179_14572.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___179_14572.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____14575; FStar_TypeChecker_Common.element = uu___179_14572.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___179_14572.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___179_14572.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___179_14572.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___179_14572.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___179_14572.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____14569 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____14577), FStar_Syntax_Syntax.Comp (uu____14578)) -> begin
(

let uu____14579 = (((FStar_Syntax_Util.is_ml_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) || ((FStar_Syntax_Util.is_total_comp c11) && ((FStar_Syntax_Util.is_total_comp c21) || (FStar_Syntax_Util.is_ml_comp c21))))
in (match (uu____14579) with
| true -> begin
(

let uu____14580 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c11) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c21) FStar_Pervasives_Native.None "result type")
in (solve_t env uu____14580 wl))
end
| uu____14583 -> begin
(

let c1_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (

let c2_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (match (((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name))) with
| true -> begin
(solve_eq c1_comp c2_comp)
end
| uu____14586 -> begin
(

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((

let uu____14590 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14590) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c12.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c22.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____14591 -> begin
()
end));
(

let uu____14592 = (FStar_TypeChecker_Env.monad_leq env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____14592) with
| FStar_Pervasives_Native.None -> begin
(

let uu____14594 = (((FStar_Syntax_Util.is_ghost_effect c12.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c22.FStar_Syntax_Syntax.effect_name)) && (

let uu____14596 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c22.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative uu____14596)))
in (match (uu____14594) with
| true -> begin
(

let edge = {FStar_TypeChecker_Env.msource = c12.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c22.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = FStar_TypeChecker_Env.identity_mlift}
in (solve_sub c12 edge c22))
end
| uu____14598 -> begin
(

let uu____14599 = (

let uu____14600 = (FStar_Syntax_Print.lid_to_string c12.FStar_Syntax_Syntax.effect_name)
in (

let uu____14601 = (FStar_Syntax_Print.lid_to_string c22.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____14600 uu____14601)))
in (giveup env uu____14599 orig))
end))
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

let uu____14607 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____14630 -> (match (uu____14630) with
| (uu____14637, uu____14638, u, uu____14640, uu____14641, uu____14642) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____14607 (FStar_String.concat ", "))))


let ineqs_to_string : (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.string = (fun ineqs -> (

let vars = (

let uu____14661 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs) (FStar_List.map FStar_Syntax_Print.univ_to_string))
in (FStar_All.pipe_right uu____14661 (FStar_String.concat ", ")))
in (

let ineqs1 = (

let uu____14671 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs) (FStar_List.map (fun uu____14688 -> (match (uu____14688) with
| (u1, u2) -> begin
(

let uu____14693 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____14694 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "%s < %s" uu____14693 uu____14694)))
end))))
in (FStar_All.pipe_right uu____14671 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred), (g.FStar_TypeChecker_Env.univ_ineqs))) with
| (FStar_TypeChecker_Common.Trivial, [], (uu____14708, [])) -> begin
"{}"
end
| uu____14721 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____14731 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____14731) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____14732 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____14734 = (FStar_List.map (fun uu____14741 -> (match (uu____14741) with
| (uu____14744, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right uu____14734 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (

let uu____14748 = (ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs)
in (FStar_Util.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n" form carry uu____14748 imps)))))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = (

let uu____14793 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____14793) with
| true -> begin
(

let uu____14794 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____14795 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14794 (rel_to_string rel) uu____14795)))
end
| uu____14796 -> begin
"TOP"
end))
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (

let uu____14819 = (

let uu____14821 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_91 -> FStar_Pervasives_Native.Some (_0_91)) uu____14821))
in (FStar_Syntax_Syntax.new_bv uu____14819 t1))
in (

let env1 = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (

let uu____14827 = (

let uu____14829 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _0_92 -> FStar_Pervasives_Native.Some (_0_92)) uu____14829))
in (

let uu____14831 = (FStar_TypeChecker_Env.get_range env1)
in (new_t_problem env1 t1 rel t2 uu____14827 uu____14831)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option = (fun env probs err1 -> (

let probs1 = (

let uu____14857 = (FStar_Options.eager_inference ())
in (match (uu____14857) with
| true -> begin
(

let uu___180_14858 = probs
in {attempting = uu___180_14858.attempting; wl_deferred = uu___180_14858.wl_deferred; ctr = uu___180_14858.ctr; defer_ok = false; smt_ok = uu___180_14858.smt_ok; tcenv = uu___180_14858.tcenv})
end
| uu____14859 -> begin
probs
end))
in (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let sol = (solve env probs1)
in (match (sol) with
| Success (deferred) -> begin
((FStar_Syntax_Unionfind.commit tx);
FStar_Pervasives_Native.Some (deferred);
)
end
| Failed (d, s) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(

let uu____14869 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____14869) with
| true -> begin
(

let uu____14870 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____14870))
end
| uu____14871 -> begin
()
end));
(err1 ((d), (s)));
)
end)))))


let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
((

let uu____14882 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____14882) with
| true -> begin
(

let uu____14883 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____14883))
end
| uu____14884 -> begin
()
end));
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env f)
in ((

let uu____14887 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____14887) with
| true -> begin
(

let uu____14888 = (FStar_Syntax_Print.term_to_string f1)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____14888))
end
| uu____14889 -> begin
()
end));
(

let f2 = (

let uu____14891 = (

let uu____14892 = (FStar_Syntax_Util.unmeta f1)
in uu____14892.FStar_Syntax_Syntax.n)
in (match (uu____14891) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____14896 -> begin
FStar_TypeChecker_Common.NonTrivial (f1)
end))
in (

let uu___181_14897 = g
in {FStar_TypeChecker_Env.guard_f = f2; FStar_TypeChecker_Env.deferred = uu___181_14897.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___181_14897.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___181_14897.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____14915 = (

let uu____14916 = (

let uu____14917 = (

let uu____14918 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____14918 (fun _0_93 -> FStar_TypeChecker_Common.NonTrivial (_0_93))))
in {FStar_TypeChecker_Env.guard_f = uu____14917; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env uu____14916))
in (FStar_All.pipe_left (fun _0_94 -> FStar_Pervasives_Native.Some (_0_94)) uu____14915))
end))


let with_guard_no_simp = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____14955 = (

let uu____14956 = (

let uu____14957 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____14957 (fun _0_95 -> FStar_TypeChecker_Common.NonTrivial (_0_95))))
in {FStar_TypeChecker_Env.guard_f = uu____14956; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in FStar_Pervasives_Native.Some (uu____14955))
end))


let try_teq : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun smt_ok env t1 t2 -> ((

let uu____14987 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14987) with
| true -> begin
(

let uu____14988 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____14989 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" uu____14988 uu____14989)))
end
| uu____14990 -> begin
()
end));
(

let prob = (

let uu____14992 = (

let uu____14995 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None uu____14995))
in (FStar_All.pipe_left (fun _0_96 -> FStar_TypeChecker_Common.TProb (_0_96)) uu____14992))
in (

let g = (

let uu____15000 = (

let uu____15002 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____15002 (fun uu____15004 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____15000))
in g));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____15021 = (try_teq true env t1 t2)
in (match (uu____15021) with
| FStar_Pervasives_Native.None -> begin
(

let uu____15023 = (

let uu____15024 = (

let uu____15027 = (FStar_TypeChecker_Err.basic_type_error env FStar_Pervasives_Native.None t2 t1)
in (

let uu____15028 = (FStar_TypeChecker_Env.get_range env)
in ((uu____15027), (uu____15028))))
in FStar_Errors.Error (uu____15024))
in (FStar_Pervasives.raise uu____15023))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____15031 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____15031) with
| true -> begin
(

let uu____15032 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____15033 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____15034 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____15032 uu____15033 uu____15034))))
end
| uu____15035 -> begin
()
end));
g;
)
end)))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 smt_ok -> ((

let uu____15054 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____15054) with
| true -> begin
(

let uu____15055 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____15056 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" uu____15055 uu____15056)))
end
| uu____15057 -> begin
()
end));
(

let uu____15058 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____15058) with
| (prob, x) -> begin
(

let g = (

let uu____15066 = (

let uu____15068 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____15068 (fun uu____15070 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____15066))
in ((

let uu____15076 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____15076) with
| true -> begin
(

let uu____15077 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____15078 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____15079 = (

let uu____15080 = (FStar_Util.must g)
in (guard_to_string env uu____15080))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" uu____15077 uu____15078 uu____15079))))
end
| uu____15081 -> begin
()
end));
(abstract_guard x g);
))
end));
))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env e t1 t2 -> (

let uu____15111 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____15112 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t2 t1)
in (FStar_Errors.err uu____15111 uu____15112))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env c1 c2 -> ((

let uu____15127 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____15127) with
| true -> begin
(

let uu____15128 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____15129 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" uu____15128 uu____15129)))
end
| uu____15130 -> begin
()
end));
(

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____15132 -> begin
FStar_TypeChecker_Common.SUB
end)
in (

let prob = (

let uu____15134 = (

let uu____15137 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 FStar_Pervasives_Native.None uu____15137 "sub_comp"))
in (FStar_All.pipe_left (fun _0_97 -> FStar_TypeChecker_Common.CProb (_0_97)) uu____15134))
in (

let uu____15140 = (

let uu____15142 = (singleton env prob)
in (solve_and_commit env uu____15142 (fun uu____15144 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____15140))));
))


let solve_universe_inequalities' : FStar_Syntax_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun tx env uu____15166 -> (match (uu____15166) with
| (variables, ineqs) -> begin
(

let fail = (fun u1 u2 -> ((FStar_Syntax_Unionfind.rollback tx);
(

let uu____15191 = (

let uu____15192 = (

let uu____15195 = (

let uu____15196 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____15197 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Universe %s and %s are incompatible" uu____15196 uu____15197)))
in (

let uu____15198 = (FStar_TypeChecker_Env.get_range env)
in ((uu____15195), (uu____15198))))
in FStar_Errors.Error (uu____15192))
in (FStar_Pervasives.raise uu____15191));
))
in (

let equiv1 = (fun v1 v' -> (

let uu____15206 = (

let uu____15209 = (FStar_Syntax_Subst.compress_univ v1)
in (

let uu____15210 = (FStar_Syntax_Subst.compress_univ v')
in ((uu____15209), (uu____15210))))
in (match (uu____15206) with
| (FStar_Syntax_Syntax.U_unif (v0), FStar_Syntax_Syntax.U_unif (v0')) -> begin
(FStar_Syntax_Unionfind.univ_equiv v0 v0')
end
| uu____15221 -> begin
false
end)))
in (

let sols = (FStar_All.pipe_right variables (FStar_List.collect (fun v1 -> (

let uu____15240 = (FStar_Syntax_Subst.compress_univ v1)
in (match (uu____15240) with
| FStar_Syntax_Syntax.U_unif (uu____15244) -> begin
(

let lower_bounds_of_v = (FStar_All.pipe_right ineqs (FStar_List.collect (fun uu____15262 -> (match (uu____15262) with
| (u, v') -> begin
(

let uu____15268 = (equiv1 v1 v')
in (match (uu____15268) with
| true -> begin
(

let uu____15270 = (FStar_All.pipe_right variables (FStar_Util.for_some (equiv1 u)))
in (match (uu____15270) with
| true -> begin
[]
end
| uu____15273 -> begin
(u)::[]
end))
end
| uu____15274 -> begin
[]
end))
end))))
in (

let lb = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max (lower_bounds_of_v)))
in (((lb), (v1)))::[]))
end
| uu____15280 -> begin
[]
end)))))
in (

let uu____15283 = (

let wl = (

let uu___182_15286 = (empty_worklist env)
in {attempting = uu___182_15286.attempting; wl_deferred = uu___182_15286.wl_deferred; ctr = uu___182_15286.ctr; defer_ok = false; smt_ok = uu___182_15286.smt_ok; tcenv = uu___182_15286.tcenv})
in (FStar_All.pipe_right sols (FStar_List.map (fun uu____15298 -> (match (uu____15298) with
| (lb, v1) -> begin
(

let uu____15303 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl lb v1)
in (match (uu____15303) with
| USolved (wl1) -> begin
()
end
| uu____15305 -> begin
(fail lb v1)
end))
end)))))
in (

let rec check_ineq = (fun uu____15311 -> (match (uu____15311) with
| (u, v1) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u)
in (

let v2 = (FStar_TypeChecker_Normalize.normalize_universe env v1)
in (match (((u1), (v2))) with
| (FStar_Syntax_Syntax.U_zero, uu____15318) -> begin
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
| (FStar_Syntax_Syntax.U_name (uu____15333), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_unif (uu____15335), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_max (us), uu____15342) -> begin
(FStar_All.pipe_right us (FStar_Util.for_all (fun u2 -> (check_ineq ((u2), (v2))))))
end
| (uu____15347, FStar_Syntax_Syntax.U_max (vs)) -> begin
(FStar_All.pipe_right vs (FStar_Util.for_some (fun v3 -> (check_ineq ((u1), (v3))))))
end
| uu____15353 -> begin
false
end)))
end))
in (

let uu____15356 = (FStar_All.pipe_right ineqs (FStar_Util.for_all (fun uu____15366 -> (match (uu____15366) with
| (u, v1) -> begin
(

let uu____15371 = (check_ineq ((u), (v1)))
in (match (uu____15371) with
| true -> begin
true
end
| uu____15372 -> begin
((

let uu____15374 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____15374) with
| true -> begin
(

let uu____15375 = (FStar_Syntax_Print.univ_to_string u)
in (

let uu____15376 = (FStar_Syntax_Print.univ_to_string v1)
in (FStar_Util.print2 "%s </= %s" uu____15375 uu____15376)))
end
| uu____15377 -> begin
()
end));
false;
)
end))
end))))
in (match (uu____15356) with
| true -> begin
()
end
| uu____15378 -> begin
((

let uu____15380 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____15380) with
| true -> begin
((

let uu____15382 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Partially solved inequality constraints are: %s\n" uu____15382));
(FStar_Syntax_Unionfind.rollback tx);
(

let uu____15388 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Original solved inequality constraints are: %s\n" uu____15388));
)
end
| uu____15393 -> begin
()
end));
(

let uu____15394 = (

let uu____15395 = (

let uu____15398 = (FStar_TypeChecker_Env.get_range env)
in (("Failed to solve universe inequalities for inductives"), (uu____15398)))
in FStar_Errors.Error (uu____15395))
in (FStar_Pervasives.raise uu____15394));
)
end)))))))
end))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun env ineqs -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Syntax_Unionfind.commit tx);
)))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail = (fun uu____15435 -> (match (uu____15435) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (FStar_Pervasives.raise (FStar_Errors.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in ((

let uu____15445 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____15445) with
| true -> begin
(

let uu____15446 = (wl_to_string wl)
in (

let uu____15447 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" uu____15446 uu____15447)))
end
| uu____15460 -> begin
()
end));
(

let g1 = (

let uu____15462 = (solve_and_commit env wl fail)
in (match (uu____15462) with
| FStar_Pervasives_Native.Some ([]) -> begin
(

let uu___183_15469 = g
in {FStar_TypeChecker_Env.guard_f = uu___183_15469.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu___183_15469.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___183_15469.FStar_TypeChecker_Env.implicits})
end
| uu____15472 -> begin
(failwith "impossible: Unexpected deferred constraints remain")
end))
in ((solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___184_15475 = g1
in {FStar_TypeChecker_Env.guard_f = uu___184_15475.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___184_15475.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = uu___184_15475.FStar_TypeChecker_Env.implicits});
));
))))


let last_proof_ns : FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let maybe_update_proof_ns : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (

let pns = env.FStar_TypeChecker_Env.proof_ns
in (

let uu____15488 = (FStar_ST.read last_proof_ns)
in (match (uu____15488) with
| FStar_Pervasives_Native.None -> begin
(FStar_ST.write last_proof_ns (FStar_Pervasives_Native.Some (pns)))
end
| FStar_Pervasives_Native.Some (old) -> begin
(match ((old = pns)) with
| true -> begin
()
end
| uu____15497 -> begin
((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(FStar_ST.write last_proof_ns (FStar_Pervasives_Native.Some (pns)));
)
end)
end))))


let discharge_guard' : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun use_env_range_msg env g use_smt -> (

let g1 = (solve_deferred_constraints env g)
in (

let ret_g = (

let uu___185_15529 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___185_15529.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___185_15529.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___185_15529.FStar_TypeChecker_Env.implicits})
in (

let uu____15530 = (

let uu____15531 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____15531)))
in (match (uu____15530) with
| true -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| uu____15533 -> begin
(match (g1.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((

let uu____15537 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Norm"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____15537) with
| true -> begin
(

let uu____15538 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____15539 = (

let uu____15540 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____15540))
in (FStar_Errors.diag uu____15538 uu____15539)))
end
| uu____15541 -> begin
()
end));
(

let vc1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env vc)
in (

let uu____15543 = (check_trivial vc1)
in (match (uu____15543) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc2) -> begin
(match ((not (use_smt))) with
| true -> begin
((

let uu____15548 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____15548) with
| true -> begin
(

let uu____15549 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____15550 = (

let uu____15551 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Cannot solve without SMT : %s\n" uu____15551))
in (FStar_Errors.diag uu____15549 uu____15550)))
end
| uu____15552 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| uu____15553 -> begin
((

let uu____15556 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____15556) with
| true -> begin
(

let uu____15557 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____15558 = (

let uu____15559 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____15559))
in (FStar_Errors.diag uu____15557 uu____15558)))
end
| uu____15560 -> begin
()
end));
(

let vcs = (

let uu____15566 = (FStar_Options.use_tactics ())
in (match (uu____15566) with
| true -> begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.preprocess env vc2)
end
| uu____15571 -> begin
(

let uu____15572 = (

let uu____15576 = (FStar_Options.peek ())
in ((env), (vc2), (uu____15576)))
in (uu____15572)::[])
end))
in (FStar_All.pipe_right vcs (FStar_List.iter (fun uu____15597 -> (match (uu____15597) with
| (env1, goal, opts) -> begin
(

let goal1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env1 goal)
in (

let uu____15605 = (check_trivial goal1)
in (match (uu____15605) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let uu____15607 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Tac"))))
in (match (uu____15607) with
| true -> begin
(FStar_Util.print_string "Goal completely solved by tactic\n")
end
| uu____15608 -> begin
()
end))
end
| FStar_TypeChecker_Common.NonTrivial (goal2) -> begin
((FStar_Options.push ());
(FStar_Options.set opts);
(maybe_update_proof_ns env1);
(

let uu____15614 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____15614) with
| true -> begin
(

let uu____15615 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____15616 = (

let uu____15617 = (FStar_Syntax_Print.term_to_string goal2)
in (

let uu____15618 = (FStar_TypeChecker_Env.string_of_proof_ns env1)
in (FStar_Util.format2 "Trying to solve:\n> %s\nWith proof_ns:\n %s\n" uu____15617 uu____15618)))
in (FStar_Errors.diag uu____15615 uu____15616)))
end
| uu____15619 -> begin
()
end));
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env1 goal2);
(FStar_Options.pop ());
)
end)))
end)))));
FStar_Pervasives_Native.Some (ret_g);
)
end)
end)));
)
end)
end)))))


let discharge_guard_no_smt : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let uu____15630 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____15630) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____15635 = (

let uu____15636 = (

let uu____15639 = (FStar_TypeChecker_Env.get_range env)
in (("Expected a trivial pre-condition"), (uu____15639)))
in FStar_Errors.Error (uu____15636))
in (FStar_Pervasives.raise uu____15635))
end)))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let uu____15648 = (discharge_guard' FStar_Pervasives_Native.None env g true)
in (match (uu____15648) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end)))


let resolve_implicits' : Prims.bool  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun forcelax g -> (

let unresolved = (fun u -> (

let uu____15665 = (FStar_Syntax_Unionfind.find u)
in (match (uu____15665) with
| FStar_Pervasives_Native.None -> begin
true
end
| uu____15667 -> begin
false
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____15680 = acc
in (match (uu____15680) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____15691 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd1)::tl1 -> begin
(

let uu____15726 = hd1
in (match (uu____15726) with
| (uu____15733, env, u, tm, k, r) -> begin
(

let uu____15739 = (unresolved u)
in (match (uu____15739) with
| true -> begin
(until_fixpoint (((hd1)::out), (changed)) tl1)
end
| uu____15753 -> begin
(

let env1 = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 tm)
in ((

let uu____15757 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("RelCheck")))
in (match (uu____15757) with
| true -> begin
(

let uu____15758 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____15759 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____15760 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" uu____15758 uu____15759 uu____15760))))
end
| uu____15761 -> begin
()
end));
(

let env2 = (match (forcelax) with
| true -> begin
(

let uu___186_15763 = env1
in {FStar_TypeChecker_Env.solver = uu___186_15763.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___186_15763.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___186_15763.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___186_15763.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___186_15763.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___186_15763.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___186_15763.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___186_15763.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___186_15763.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___186_15763.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___186_15763.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___186_15763.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___186_15763.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___186_15763.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___186_15763.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___186_15763.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___186_15763.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___186_15763.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___186_15763.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___186_15763.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___186_15763.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___186_15763.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___186_15763.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___186_15763.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___186_15763.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___186_15763.FStar_TypeChecker_Env.is_native_tactic})
end
| uu____15764 -> begin
env1
end)
in (

let uu____15765 = (env2.FStar_TypeChecker_Env.type_of (

let uu___187_15770 = env2
in {FStar_TypeChecker_Env.solver = uu___187_15770.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___187_15770.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___187_15770.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___187_15770.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___187_15770.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___187_15770.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___187_15770.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___187_15770.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___187_15770.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___187_15770.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___187_15770.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___187_15770.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___187_15770.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___187_15770.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___187_15770.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___187_15770.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___187_15770.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___187_15770.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___187_15770.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___187_15770.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___187_15770.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___187_15770.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___187_15770.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___187_15770.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___187_15770.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___187_15770.FStar_TypeChecker_Env.is_native_tactic}) tm1)
in (match (uu____15765) with
| (uu____15771, uu____15772, g1) -> begin
(

let g2 = (match (env2.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___188_15775 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___188_15775.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___188_15775.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___188_15775.FStar_TypeChecker_Env.implicits})
end
| uu____15776 -> begin
g1
end)
in (

let g' = (

let uu____15778 = (discharge_guard' (FStar_Pervasives_Native.Some ((fun uu____15783 -> (FStar_Syntax_Print.term_to_string tm1)))) env2 g2 true)
in (match (uu____15778) with
| FStar_Pervasives_Native.Some (g3) -> begin
g3
end
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end))
in (until_fixpoint (((FStar_List.append g'.FStar_TypeChecker_Env.implicits out)), (true)) tl1)))
end)));
)))
end))
end))
end)
end)))
in (

let uu___189_15798 = g
in (

let uu____15799 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___189_15798.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___189_15798.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___189_15798.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____15799})))))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (resolve_implicits' false g))


let resolve_implicits_lax : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (resolve_implicits' true g))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g1 = (

let uu____15837 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____15837 resolve_implicits))
in (match (g1.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(

let uu____15844 = (discharge_guard env g1)
in (FStar_All.pipe_left FStar_Pervasives.ignore uu____15844))
end
| ((reason, uu____15846, uu____15847, e, t, r))::uu____15851 -> begin
(

let uu____15865 = (

let uu____15866 = (

let uu____15869 = (

let uu____15870 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____15871 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Failed to resolve implicit argument of type \'%s\' introduced in %s" uu____15870 uu____15871)))
in ((uu____15869), (r)))
in FStar_Errors.Error (uu____15866))
in (FStar_Pervasives.raise uu____15865))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___190_15880 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___190_15880.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___190_15880.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ((((u1), (u2)))::[])); FStar_TypeChecker_Env.implicits = uu___190_15880.FStar_TypeChecker_Env.implicits}))


let teq_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____15901 = (try_teq false env t1 t2)
in (match (uu____15901) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g) -> begin
(

let uu____15904 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____15904) with
| FStar_Pervasives_Native.Some (uu____15908) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end))
end)))





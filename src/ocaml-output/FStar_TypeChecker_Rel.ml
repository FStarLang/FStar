
open Prims
open FStar_Pervasives

let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu____30; FStar_TypeChecker_Env.implicits = uu____31} -> begin
true
end
| uu____58 -> begin
false
end))


let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []}


let abstract_guard_n : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun bs g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let f' = (FStar_Syntax_Util.abs bs f (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in (

let uu___119_91 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.NonTrivial (f'); FStar_TypeChecker_Env.deferred = uu___119_91.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___119_91.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___119_91.FStar_TypeChecker_Env.implicits}))
end))


let abstract_guard : FStar_Syntax_Syntax.binder  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun b g -> (abstract_guard_n ((b)::[]) g))


let def_check_vars_in_set : FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun rng msg vset t -> (

let uu____114 = (FStar_Options.defensive ())
in (match (uu____114) with
| true -> begin
(

let s = (FStar_Syntax_Free.names t)
in (

let uu____118 = (

let uu____119 = (

let uu____120 = (FStar_Util.set_difference s vset)
in (FStar_All.pipe_left FStar_Util.set_is_empty uu____120))
in (not (uu____119)))
in (match (uu____118) with
| true -> begin
(

let uu____125 = (

let uu____130 = (

let uu____131 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____132 = (

let uu____133 = (FStar_Util.set_elements s)
in (FStar_All.pipe_right uu____133 (FStar_Syntax_Print.bvs_to_string ",\n\t")))
in (FStar_Util.format3 "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n" msg uu____131 uu____132)))
in ((FStar_Errors.Warning_Defensive), (uu____130)))
in (FStar_Errors.log_issue rng uu____125))
end
| uu____138 -> begin
()
end)))
end
| uu____139 -> begin
()
end)))


let def_check_closed : FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun rng msg t -> (

let uu____149 = (

let uu____150 = (FStar_Options.defensive ())
in (not (uu____150)))
in (match (uu____149) with
| true -> begin
()
end
| uu____151 -> begin
(def_check_vars_in_set rng msg FStar_Syntax_Free.empty t)
end)))


let def_check_closed_in : FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun rng msg l t -> (

let uu____168 = (

let uu____169 = (FStar_Options.defensive ())
in (not (uu____169)))
in (match (uu____168) with
| true -> begin
()
end
| uu____170 -> begin
(

let uu____171 = (FStar_Util.as_set l FStar_Syntax_Syntax.order_bv)
in (def_check_vars_in_set rng msg uu____171 t))
end)))


let def_check_closed_in_env : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun rng msg e t -> (

let uu____186 = (

let uu____187 = (FStar_Options.defensive ())
in (not (uu____187)))
in (match (uu____186) with
| true -> begin
()
end
| uu____188 -> begin
(

let uu____189 = (FStar_TypeChecker_Env.bound_vars e)
in (def_check_closed_in rng msg uu____189 t))
end)))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___120_199 = g
in (

let uu____200 = (

let uu____201 = (

let uu____202 = (

let uu____205 = (

let uu____206 = (

let uu____221 = (

let uu____224 = (FStar_Syntax_Syntax.as_arg e)
in (uu____224)::[])
in ((f), (uu____221)))
in FStar_Syntax_Syntax.Tm_app (uu____206))
in (FStar_Syntax_Syntax.mk uu____205))
in (uu____202 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _0_40 -> FStar_TypeChecker_Common.NonTrivial (_0_40)) uu____201))
in {FStar_TypeChecker_Env.guard_f = uu____200; FStar_TypeChecker_Env.deferred = uu___120_199.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___120_199.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___120_199.FStar_TypeChecker_Env.implicits}))
end))


let map_guard : FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  FStar_TypeChecker_Env.guard_t = (fun g map1 -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___121_242 = g
in (

let uu____243 = (

let uu____244 = (map1 f)
in FStar_TypeChecker_Common.NonTrivial (uu____244))
in {FStar_TypeChecker_Env.guard_f = uu____243; FStar_TypeChecker_Env.deferred = uu___121_242.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___121_242.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___121_242.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____248) -> begin
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

let uu____259 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (uu____259))
end))


let check_trivial : FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (

let uu____263 = (

let uu____264 = (FStar_Syntax_Util.unmeta t)
in uu____264.FStar_Syntax_Syntax.n)
in (match (uu____263) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____268 -> begin
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

let uu____299 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = uu____299; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (((FStar_List.append (FStar_Pervasives_Native.fst g1.FStar_TypeChecker_Env.univ_ineqs) (FStar_Pervasives_Native.fst g2.FStar_TypeChecker_Env.univ_ineqs))), ((FStar_List.append (FStar_Pervasives_Native.snd g1.FStar_TypeChecker_Env.univ_ineqs) (FStar_Pervasives_Native.snd g2.FStar_TypeChecker_Env.univ_ineqs)))); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard_univs : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun us bs g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let f1 = (FStar_List.fold_right2 (fun u b f1 -> (

let uu____366 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____366) with
| true -> begin
f1
end
| uu____367 -> begin
(FStar_Syntax_Util.mk_forall u (FStar_Pervasives_Native.fst b) f1)
end))) us bs f)
in (

let uu___122_368 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.NonTrivial (f1); FStar_TypeChecker_Env.deferred = uu___122_368.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___122_368.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___122_368.FStar_TypeChecker_Env.implicits}))
end))


let close_forall : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____387 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____387) with
| true -> begin
f1
end
| uu____388 -> begin
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

let uu___123_400 = g
in (

let uu____401 = (

let uu____402 = (close_forall env binders f)
in FStar_TypeChecker_Common.NonTrivial (uu____402))
in {FStar_TypeChecker_Env.guard_f = uu____401; FStar_TypeChecker_Env.deferred = uu___123_400.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___123_400.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___123_400.FStar_TypeChecker_Env.implicits}))
end))


let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (

let uv = (FStar_Syntax_Unionfind.fresh ())
in (match (binders) with
| [] -> begin
(

let uv1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k)))) FStar_Pervasives_Native.None r)
in ((uv1), (uv1)))
end
| uu____432 -> begin
(

let args = (FStar_All.pipe_right binders (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder))
in (

let k' = (

let uu____457 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders uu____457))
in (

let uv1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k')))) FStar_Pervasives_Native.None r)
in (

let uu____465 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((uv1), (args)))) FStar_Pervasives_Native.None r)
in ((uu____465), (uv1))))))
end)))

type uvi =
| TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)


let uu___is_TERM : uvi  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TERM (_0) -> begin
true
end
| uu____512 -> begin
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
| uu____552 -> begin
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
| uu____738 -> begin
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
| uu____754 -> begin
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
| uu____777 -> begin
false
end))


let uu___is_CONTRAVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CONTRAVARIANT -> begin
true
end
| uu____781 -> begin
false
end))


let uu___is_INVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| INVARIANT -> begin
true
end
| uu____785 -> begin
false
end))


type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem


type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem


type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun uu___89_808 -> (match (uu___89_808) with
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

let compact = (FStar_Syntax_Print.term_to_string t)
in (

let detail = (

let uu____814 = (

let uu____815 = (FStar_Syntax_Subst.compress t)
in uu____815.FStar_Syntax_Syntax.n)
in (match (uu____814) with
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let uu____844 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____845 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "%s : %s" uu____844 uu____845)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty); FStar_Syntax_Syntax.pos = uu____848; FStar_Syntax_Syntax.vars = uu____849}, args) -> begin
(

let uu____895 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____896 = (FStar_Syntax_Print.term_to_string ty)
in (

let uu____897 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "(%s : %s) %s" uu____895 uu____896 uu____897))))
end
| uu____898 -> begin
"--"
end))
in (

let uu____899 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format3 "%s (%s)\t%s" compact uu____899 detail)))))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env uu___90_905 -> (match (uu___90_905) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____911 = (

let uu____914 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____915 = (

let uu____918 = (term_to_string p.FStar_TypeChecker_Common.lhs)
in (

let uu____919 = (

let uu____922 = (

let uu____925 = (term_to_string p.FStar_TypeChecker_Common.rhs)
in (uu____925)::[])
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::uu____922)
in (uu____918)::uu____919))
in (uu____914)::uu____915))
in (FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____911))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____931 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____932 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____933 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____931 uu____932 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____933))))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env uu___91_939 -> (match (uu___91_939) with
| UNIV (u, t) -> begin
(

let x = (

let uu____943 = (FStar_Options.hide_uvar_nums ())
in (match (uu____943) with
| true -> begin
"?"
end
| uu____944 -> begin
(

let uu____945 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____945 FStar_Util.string_of_int))
end))
in (

let uu____946 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x uu____946)))
end
| TERM ((u, uu____948), t) -> begin
(

let x = (

let uu____955 = (FStar_Options.hide_uvar_nums ())
in (match (uu____955) with
| true -> begin
"?"
end
| uu____956 -> begin
(

let uu____957 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____957 FStar_Util.string_of_int))
end))
in (

let uu____958 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x uu____958)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (

let uu____969 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right uu____969 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (

let uu____981 = (

let uu____984 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right uu____984 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right uu____981 (FStar_String.concat ", "))))


let args_to_string : 'Auu____995 . (FStar_Syntax_Syntax.term * 'Auu____995) Prims.list  ->  Prims.string = (fun args -> (

let uu____1012 = (FStar_All.pipe_right args (FStar_List.map (fun uu____1030 -> (match (uu____1030) with
| (x, uu____1036) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____1012 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> (

let uu____1042 = (

let uu____1043 = (FStar_Options.eager_inference ())
in (not (uu____1043)))
in {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = uu____1042; smt_ok = true; tcenv = env}))


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let uu___124_1059 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = uu___124_1059.wl_deferred; ctr = uu___124_1059.ctr; defer_ok = uu___124_1059.defer_ok; smt_ok = smt_ok; tcenv = uu___124_1059.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard : 'Auu____1069 . FStar_TypeChecker_Env.env  ->  ('Auu____1069 * FStar_TypeChecker_Common.prob) Prims.list  ->  worklist = (fun env g -> (

let uu___125_1090 = (empty_worklist env)
in (

let uu____1091 = (FStar_List.map FStar_Pervasives_Native.snd g)
in {attempting = uu____1091; wl_deferred = uu___125_1090.wl_deferred; ctr = uu___125_1090.ctr; defer_ok = false; smt_ok = uu___125_1090.smt_ok; tcenv = uu___125_1090.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu___126_1105 = wl
in {attempting = uu___126_1105.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = uu___126_1105.ctr; defer_ok = uu___126_1105.defer_ok; smt_ok = uu___126_1105.smt_ok; tcenv = uu___126_1105.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let uu___127_1122 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = uu___127_1122.wl_deferred; ctr = uu___127_1122.ctr; defer_ok = uu___127_1122.defer_ok; smt_ok = uu___127_1122.smt_ok; tcenv = uu___127_1122.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> ((

let uu____1133 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____1133) with
| true -> begin
(

let uu____1134 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1134))
end
| uu____1135 -> begin
()
end));
Failed (((prob), (reason)));
))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun uu___92_1138 -> (match (uu___92_1138) with
| FStar_TypeChecker_Common.EQ -> begin
FStar_TypeChecker_Common.EQ
end
| FStar_TypeChecker_Common.SUB -> begin
FStar_TypeChecker_Common.SUBINV
end
| FStar_TypeChecker_Common.SUBINV -> begin
FStar_TypeChecker_Common.SUB
end))


let invert : 'Auu____1142 'Auu____1143 . ('Auu____1142, 'Auu____1143) FStar_TypeChecker_Common.problem  ->  ('Auu____1142, 'Auu____1143) FStar_TypeChecker_Common.problem = (fun p -> (

let uu___128_1160 = p
in {FStar_TypeChecker_Common.pid = uu___128_1160.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = uu___128_1160.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___128_1160.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___128_1160.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___128_1160.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___128_1160.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___128_1160.FStar_TypeChecker_Common.rank}))


let maybe_invert : 'Auu____1168 'Auu____1169 . ('Auu____1168, 'Auu____1169) FStar_TypeChecker_Common.problem  ->  ('Auu____1168, 'Auu____1169) FStar_TypeChecker_Common.problem = (fun p -> (match ((Prims.op_Equality p.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUBINV)) with
| true -> begin
(invert p)
end
| uu____1186 -> begin
p
end))


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___93_1189 -> (match (uu___93_1189) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_41 -> FStar_TypeChecker_Common.TProb (_0_41)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_42 -> FStar_TypeChecker_Common.CProb (_0_42)))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel uu___94_1213 -> (match (uu___94_1213) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun uu___95_1216 -> (match (uu___95_1216) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun uu___96_1229 -> (match (uu___96_1229) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun uu___97_1244 -> (match (uu___97_1244) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun uu___98_1259 -> (match (uu___98_1259) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun uu___99_1276 -> (match (uu___99_1276) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let def_scope_wf : 'Auu____1295 . Prims.string  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.bv * 'Auu____1295) Prims.list  ->  Prims.unit = (fun msg rng r -> (

let uu____1320 = (

let uu____1321 = (FStar_Options.defensive ())
in (not (uu____1321)))
in (match (uu____1320) with
| true -> begin
()
end
| uu____1322 -> begin
(

let rec aux = (fun prev next -> (match (next) with
| [] -> begin
()
end
| ((bv, uu____1351))::bs -> begin
((def_check_closed_in rng msg prev bv.FStar_Syntax_Syntax.sort);
(aux (FStar_List.append prev ((bv)::[])) bs);
)
end))
in (aux [] r))
end)))


let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun prob -> (

let r = (match (prob) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end)
in ((def_scope_wf "p_scope" (p_loc prob) r);
r;
)))


let def_check_scoped : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun msg prob phi -> (

let uu____1388 = (

let uu____1389 = (FStar_Options.defensive ())
in (not (uu____1389)))
in (match (uu____1388) with
| true -> begin
()
end
| uu____1390 -> begin
(

let uu____1391 = (

let uu____1394 = (p_scope prob)
in (FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst) uu____1394))
in (def_check_closed_in (p_loc prob) msg uu____1391 phi))
end)))


let def_check_prob : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  Prims.unit = (fun msg prob -> ((

let uu____1420 = (

let uu____1421 = (FStar_Options.defensive ())
in (not (uu____1421)))
in (match (uu____1420) with
| true -> begin
()
end
| uu____1422 -> begin
(

let uu____1423 = (p_scope prob)
in (def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1423))
end));
(

let uu____1431 = (FStar_All.pipe_left FStar_Pervasives_Native.fst (p_guard prob))
in (def_check_scoped (Prims.strcat msg ".guard") prob uu____1431));
(

let uu____1437 = (FStar_All.pipe_left FStar_Pervasives_Native.snd (p_guard prob))
in (def_check_scoped (Prims.strcat msg ".guard_type") prob uu____1437));
(match (prob) with
| FStar_TypeChecker_Common.TProb (p) -> begin
((def_check_scoped (Prims.strcat msg ".lhs") prob p.FStar_TypeChecker_Common.lhs);
(def_check_scoped (Prims.strcat msg ".rhs") prob p.FStar_TypeChecker_Common.rhs);
)
end
| uu____1448 -> begin
()
end);
))


let mk_eq2 : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun prob t1 t2 -> (

let uu____1463 = (FStar_Syntax_Util.type_u ())
in (match (uu____1463) with
| (t_type, u) -> begin
(

let uu____1470 = (

let uu____1475 = (p_scope prob)
in (new_uvar t1.FStar_Syntax_Syntax.pos uu____1475 t_type))
in (match (uu____1470) with
| (tt, uu____1477) -> begin
(FStar_Syntax_Util.mk_eq2 u tt t1 t2)
end))
end)))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___100_1480 -> (match (uu___100_1480) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _0_43 -> FStar_TypeChecker_Common.TProb (_0_43)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _0_44 -> FStar_TypeChecker_Common.CProb (_0_44)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> (

let uu____1502 = (FStar_All.pipe_right (p_reason p) FStar_List.length)
in (Prims.op_Equality uu____1502 (Prims.parse_int "1"))))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____1514 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
)))


let mk_problem : 'Auu____1725 'Auu____1726 . FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  'Auu____1725  ->  FStar_TypeChecker_Common.rel  ->  'Auu____1725  ->  'Auu____1726 FStar_Pervasives_Native.option  ->  Prims.string  ->  ('Auu____1725, 'Auu____1726) FStar_TypeChecker_Common.problem = (fun scope orig lhs rel rhs elt reason -> (

let uu____1763 = (next_pid ())
in (

let uu____1764 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____1763; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____1764; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})))


let new_problem : 'Auu____1778 'Auu____1779 . FStar_TypeChecker_Env.env  ->  'Auu____1778  ->  FStar_TypeChecker_Common.rel  ->  'Auu____1778  ->  'Auu____1779 FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  Prims.string  ->  ('Auu____1778, 'Auu____1779) FStar_TypeChecker_Common.problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (

let uu____1817 = (next_pid ())
in (

let uu____1818 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____1817; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____1818; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None}))))


let problem_using_guard : 'Auu____1831 'Auu____1832 . FStar_TypeChecker_Common.prob  ->  'Auu____1831  ->  FStar_TypeChecker_Common.rel  ->  'Auu____1831  ->  'Auu____1832 FStar_Pervasives_Native.option  ->  Prims.string  ->  ('Auu____1831, 'Auu____1832) FStar_TypeChecker_Common.problem = (fun orig lhs rel rhs elt reason -> (

let uu____1865 = (next_pid ())
in (

let uu____1866 = (p_scope orig)
in {FStar_TypeChecker_Common.pid = uu____1865; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = uu____1866; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})))


let guard_on_element : 'Auu____1872 . worklist  ->  ('Auu____1872, FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_TypeChecker_Common.problem  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun wl problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| FStar_Pervasives_Native.None -> begin
(

let u = (wl.tcenv.FStar_TypeChecker_Env.universe_of wl.tcenv x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Util.mk_forall u x phi))
end
| FStar_Pervasives_Native.Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (

let uu____1922 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____1922) with
| true -> begin
(

let uu____1923 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (

let uu____1924 = (prob_to_string env d)
in (

let uu____1925 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" uu____1923 uu____1924 uu____1925 s))))
end
| uu____1928 -> begin
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
| uu____1931 -> begin
(failwith "impossible")
end)
in (

let uu____1932 = (match (d1) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____1946 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (

let uu____1947 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((uu____1946), (uu____1947))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____1953 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (

let uu____1954 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((uu____1953), (uu____1954))))
end)
in (match (uu____1932) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___101_1970 -> (match (uu___101_1970) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Syntax_Unionfind.univ_union u u')
end
| uu____1982 -> begin
(FStar_Syntax_Unionfind.univ_change u t)
end)
end
| TERM ((u, uu____1984), t) -> begin
((def_check_closed t.FStar_Syntax_Syntax.pos "commit" t);
(FStar_Syntax_Util.set_uvar u t);
)
end)))))


let find_term_uvar : FStar_Syntax_Syntax.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun uv s -> (FStar_Util.find_map s (fun uu___102_2005 -> (match (uu___102_2005) with
| UNIV (uu____2008) -> begin
FStar_Pervasives_Native.None
end
| TERM ((u, uu____2014), t) -> begin
(

let uu____2020 = (FStar_Syntax_Unionfind.equiv uv u)
in (match (uu____2020) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____2023 -> begin
FStar_Pervasives_Native.None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe_uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun u s -> (FStar_Util.find_map s (fun uu___103_2040 -> (match (uu___103_2040) with
| UNIV (u', t) -> begin
(

let uu____2045 = (FStar_Syntax_Unionfind.univ_equiv u u')
in (match (uu____2045) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____2048 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____2049 -> begin
FStar_Pervasives_Native.None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____2056 = (

let uu____2057 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env uu____2057))
in (FStar_Syntax_Subst.compress uu____2056)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____2064 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress uu____2064)))


let norm_arg : 'Auu____2068 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * 'Auu____2068)  ->  (FStar_Syntax_Syntax.term * 'Auu____2068) = (fun env t -> (

let uu____2089 = (sn env (FStar_Pervasives_Native.fst t))
in ((uu____2089), ((FStar_Pervasives_Native.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____2120 -> (match (uu____2120) with
| (x, imp) -> begin
(

let uu____2131 = (

let uu___129_2132 = x
in (

let uu____2133 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___129_2132.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___129_2132.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2133}))
in ((uu____2131), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____2148 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____2148))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____2152 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____2152))
end
| uu____2155 -> begin
u2
end)))
in (

let uu____2156 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2156))))


let base_and_refinement_maybe_delta : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option) = (fun should_delta env t1 -> (

let norm_refinement = (fun env1 t -> (

let steps = (match (should_delta) with
| true -> begin
(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]
end
| uu____2192 -> begin
(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]
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
| uu____2267 -> begin
(

let uu____2268 = (norm_refinement env t12)
in (match (uu____2268) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x1, phi1); FStar_Syntax_Syntax.pos = uu____2285; FStar_Syntax_Syntax.vars = uu____2286} -> begin
((x1.FStar_Syntax_Syntax.sort), (FStar_Pervasives_Native.Some (((x1), (phi1)))))
end
| tt -> begin
(

let uu____2312 = (

let uu____2313 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____2314 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" uu____2313 uu____2314)))
in (failwith uu____2312))
end))
end)
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____2330 = (FStar_Syntax_Util.unfold_lazy i)
in (aux norm1 uu____2330))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____2331) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____2366 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____2368 = (

let uu____2369 = (FStar_Syntax_Subst.compress t1')
in uu____2369.FStar_Syntax_Syntax.n)
in (match (uu____2368) with
| FStar_Syntax_Syntax.Tm_refine (uu____2386) -> begin
(aux true t1')
end
| uu____2393 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2408) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____2437 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____2439 = (

let uu____2440 = (FStar_Syntax_Subst.compress t1')
in uu____2440.FStar_Syntax_Syntax.n)
in (match (uu____2439) with
| FStar_Syntax_Syntax.Tm_refine (uu____2457) -> begin
(aux true t1')
end
| uu____2464 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_app (uu____2479) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____2522 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____2524 = (

let uu____2525 = (FStar_Syntax_Subst.compress t1')
in uu____2525.FStar_Syntax_Syntax.n)
in (match (uu____2524) with
| FStar_Syntax_Syntax.Tm_refine (uu____2542) -> begin
(aux true t1')
end
| uu____2549 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_type (uu____2564) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_constant (uu____2579) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_name (uu____2594) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2609) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____2624) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_abs (uu____2651) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_quoted (uu____2682) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2703) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_let (uu____2734) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_match (uu____2761) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_meta (uu____2798) -> begin
(

let uu____2805 = (

let uu____2806 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____2807 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2806 uu____2807)))
in (failwith uu____2805))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____2822) -> begin
(

let uu____2849 = (

let uu____2850 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____2851 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2850 uu____2851)))
in (failwith uu____2849))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____2866) -> begin
(

let uu____2891 = (

let uu____2892 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____2893 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2892 uu____2893)))
in (failwith uu____2891))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____2908 = (

let uu____2909 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____2910 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2909 uu____2910)))
in (failwith uu____2908))
end)))
in (

let uu____2925 = (whnf env t1)
in (aux false uu____2925)))))


let base_and_refinement : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option) = (fun env t -> (base_and_refinement_maybe_delta false env t))


let normalize_refinement : 'Auu____2947 . FStar_TypeChecker_Normalize.steps  ->  FStar_TypeChecker_Env.env  ->  'Auu____2947  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____2970 = (base_and_refinement env t)
in (FStar_All.pipe_right uu____2970 FStar_Pervasives_Native.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (

let uu____3004 = (FStar_Syntax_Syntax.null_bv t)
in ((uu____3004), (FStar_Syntax_Util.t_true))))


let as_refinement : 'Auu____3010 . Prims.bool  ->  FStar_TypeChecker_Env.env  ->  'Auu____3010  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun delta1 env wl t -> (

let uu____3031 = (base_and_refinement_maybe_delta delta1 env t)
in (match (uu____3031) with
| (t_base, refinement) -> begin
(match (refinement) with
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end
| FStar_Pervasives_Native.Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement : (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun uu____3110 -> (match (uu____3110) with
| (t_base, refopt) -> begin
(

let uu____3137 = (match (refopt) with
| FStar_Pervasives_Native.Some (y, phi) -> begin
((y), (phi))
end
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end)
in (match (uu____3137) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl prob -> (prob_to_string wl.tcenv prob))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (

let uu____3169 = (

let uu____3172 = (

let uu____3175 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____3198 -> (match (uu____3198) with
| (uu____3205, uu____3206, x) -> begin
x
end))))
in (FStar_List.append wl.attempting uu____3175))
in (FStar_List.map (wl_prob_to_string wl) uu____3172))
in (FStar_All.pipe_right uu____3169 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____3219 = (

let uu____3232 = (

let uu____3233 = (FStar_Syntax_Subst.compress k)
in uu____3233.FStar_Syntax_Syntax.n)
in (match (uu____3232) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((Prims.op_Equality (FStar_List.length bs) (FStar_List.length ys))) with
| true -> begin
(

let uu____3286 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (uu____3286)))
end
| uu____3299 -> begin
(

let uu____3300 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____3300) with
| (ys', t1, uu____3323) -> begin
(

let uu____3328 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t1))), (uu____3328)))
end))
end)
end
| uu____3369 -> begin
(

let uu____3370 = (

let uu____3381 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____3381)))
in ((((ys), (t))), (uu____3370)))
end))
in (match (uu____3219) with
| ((ys1, t1), (xs, c)) -> begin
(match ((Prims.op_disEquality (FStar_List.length xs) (FStar_List.length ys1))) with
| true -> begin
(FStar_Syntax_Util.abs ys1 t1 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None []))))
end
| uu____3428 -> begin
(

let c1 = (

let uu____3430 = (FStar_Syntax_Util.rename_binders xs ys1)
in (FStar_Syntax_Subst.subst_comp uu____3430 c))
in (FStar_Syntax_Util.abs ys1 t1 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c1)))))
end)
end)))


let solve_prob' : Prims.bool  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun resolve_ok prob logical_guard uvis wl -> ((def_check_prob "solve_prob\'" prob);
(

let phi = (match (logical_guard) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Util.t_true
end
| FStar_Pervasives_Native.Some (phi) -> begin
phi
end)
in (

let uu____3459 = (p_guard prob)
in (match (uu____3459) with
| (uu____3464, uv) -> begin
((

let uu____3467 = (

let uu____3468 = (FStar_Syntax_Subst.compress uv)
in uu____3468.FStar_Syntax_Syntax.n)
in (match (uu____3467) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi1 = (u_abs k bs phi)
in ((

let uu____3500 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____3500) with
| true -> begin
(

let uu____3501 = (FStar_Util.string_of_int (p_pid prob))
in (

let uu____3502 = (FStar_Syntax_Print.term_to_string uv)
in (

let uu____3503 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" uu____3501 uu____3502 uu____3503))))
end
| uu____3504 -> begin
()
end));
(def_check_closed (p_loc prob) "solve_prob\'" phi1);
(FStar_Syntax_Util.set_uvar uvar phi1);
)))
end
| uu____3506 -> begin
(match ((not (resolve_ok))) with
| true -> begin
(failwith "Impossible: this instance has already been assigned a solution")
end
| uu____3507 -> begin
()
end)
end));
(commit uvis);
(

let uu___130_3509 = wl
in {attempting = uu___130_3509.attempting; wl_deferred = uu___130_3509.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___130_3509.defer_ok; smt_ok = uu___130_3509.smt_ok; tcenv = uu___130_3509.tcenv});
)
end)));
))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____3524 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____3524) with
| true -> begin
(

let uu____3525 = (FStar_Util.string_of_int pid)
in (

let uu____3526 = (

let uu____3527 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right uu____3527 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____3525 uu____3526)))
end
| uu____3532 -> begin
()
end));
(commit sol);
(

let uu___131_3534 = wl
in {attempting = uu___131_3534.attempting; wl_deferred = uu___131_3534.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___131_3534.defer_ok; smt_ok = uu___131_3534.smt_ok; tcenv = uu___131_3534.tcenv});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> ((def_check_prob "solve_prob.prob" prob);
(FStar_Util.iter_opt logical_guard (def_check_scoped "solve_prob.guard" prob));
(

let conj_guard1 = (fun t g -> (match (((t), (g))) with
| (uu____3574, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (FStar_Pervasives_Native.None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
FStar_Pervasives_Native.Some (f)
end
| (FStar_Pervasives_Native.Some (t1), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(

let uu____3586 = (FStar_Syntax_Util.mk_conj t1 f)
in FStar_Pervasives_Native.Some (uu____3586))
end))
in ((

let uu____3592 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____3592) with
| true -> begin
(

let uu____3593 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (

let uu____3594 = (

let uu____3595 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right uu____3595 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____3593 uu____3594)))
end
| uu____3600 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
));
))


let rec occurs : 'b . worklist  ->  (FStar_Syntax_Syntax.uvar * 'b)  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun wl uk t -> (

let uu____3627 = (

let uu____3634 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right uu____3634 FStar_Util.set_elements))
in (FStar_All.pipe_right uu____3627 (FStar_Util.for_some (fun uu____3670 -> (match (uu____3670) with
| (uv, uu____3676) -> begin
(FStar_Syntax_Unionfind.equiv uv (FStar_Pervasives_Native.fst uk))
end))))))


let occurs_check : 'Auu____3683 'Auu____3684 . 'Auu____3683  ->  worklist  ->  (FStar_Syntax_Syntax.uvar * 'Auu____3684)  ->  FStar_Syntax_Syntax.typ  ->  (Prims.bool * Prims.string FStar_Pervasives_Native.option) = (fun env wl uk t -> (

let occurs_ok = (

let uu____3716 = (occurs wl uk t)
in (not (uu____3716)))
in (

let msg = (match (occurs_ok) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3722 -> begin
(

let uu____3723 = (

let uu____3724 = (FStar_Syntax_Print.uvar_to_string (FStar_Pervasives_Native.fst uk))
in (

let uu____3725 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" uu____3724 uu____3725)))
in FStar_Pervasives_Native.Some (uu____3723))
end)
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check : 'Auu____3735 'Auu____3736 . 'Auu____3735  ->  worklist  ->  (FStar_Syntax_Syntax.uvar * 'Auu____3736)  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.term  ->  (Prims.bool * Prims.bool * (Prims.string FStar_Pervasives_Native.option * FStar_Syntax_Syntax.bv FStar_Util.set * FStar_Syntax_Syntax.bv FStar_Util.set)) = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let uu____3790 = (occurs_check env wl uk t)
in (match (uu____3790) with
| (occurs_ok, msg) -> begin
(

let uu____3821 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (uu____3821), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars : 'Auu____3844 'Auu____3845 . (FStar_Syntax_Syntax.bv * 'Auu____3844) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____3845) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____3845) Prims.list = (fun v1 v2 -> (

let as_set1 = (fun v3 -> (FStar_All.pipe_right v3 (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set1 v1)
in (

let uu____3929 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____3983 uu____3984 -> (match (((uu____3983), (uu____3984))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____4065 = (

let uu____4066 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation uu____4066))
in (match (uu____4065) with
| true -> begin
((isect), (isect_set))
end
| uu____4087 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____4091 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____4091) with
| true -> begin
(

let uu____4104 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (uu____4104)))
end
| uu____4119 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (uu____3929) with
| (isect, uu____4145) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq : 'Auu____4170 'Auu____4171 . (FStar_Syntax_Syntax.bv * 'Auu____4170) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____4171) Prims.list  ->  Prims.bool = (fun v1 v2 -> ((Prims.op_Equality (FStar_List.length v1) (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____4226 uu____4227 -> (match (((uu____4226), (uu____4227))) with
| ((a, uu____4245), (b, uu____4247)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt : 'Auu____4261 'Auu____4262 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____4261) Prims.list  ->  (FStar_Syntax_Syntax.term * 'Auu____4262)  ->  (FStar_Syntax_Syntax.bv * 'Auu____4262) FStar_Pervasives_Native.option = (fun env seen arg -> (

let hd1 = (norm_arg env arg)
in (match ((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(

let uu____4313 = (FStar_All.pipe_right seen (FStar_Util.for_some (fun uu____4327 -> (match (uu____4327) with
| (b, uu____4333) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end))))
in (match (uu____4313) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4344 -> begin
FStar_Pervasives_Native.Some (((a), ((FStar_Pervasives_Native.snd hd1))))
end))
end
| uu____4349 -> begin
FStar_Pervasives_Native.None
end)))


let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option = (fun env seen args -> (match (args) with
| [] -> begin
FStar_Pervasives_Native.Some ((FStar_List.rev seen))
end
| (hd1)::rest -> begin
(

let uu____4422 = (pat_var_opt env seen hd1)
in (match (uu____4422) with
| FStar_Pervasives_Native.None -> begin
((

let uu____4436 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____4436) with
| true -> begin
(

let uu____4437 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (FStar_Pervasives_Native.fst hd1))
in (FStar_Util.print1 "Not a pattern: %s\n" uu____4437))
end
| uu____4438 -> begin
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

let uu____4455 = (

let uu____4456 = (FStar_Syntax_Subst.compress t)
in uu____4456.FStar_Syntax_Syntax.n)
in (match (uu____4455) with
| FStar_Syntax_Syntax.Tm_uvar (uu____4459) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____4476); FStar_Syntax_Syntax.pos = uu____4477; FStar_Syntax_Syntax.vars = uu____4478}, uu____4479) -> begin
true
end
| uu____4516 -> begin
false
end)))


let destruct_flex_t : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.pos = uu____4640; FStar_Syntax_Syntax.vars = uu____4641}, args) -> begin
((t), (uv), (k), (args))
end
| uu____4709 -> begin
(failwith "Not a flex-uvar")
end))


let destruct_flex_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) * FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option) = (fun env t -> (

let uu____4786 = (destruct_flex_t t)
in (match (uu____4786) with
| (t1, uv, k, args) -> begin
(

let uu____4901 = (pat_vars env [] args)
in (match (uu____4901) with
| FStar_Pervasives_Native.Some (vars) -> begin
((((t1), (uv), (k), (args))), (FStar_Pervasives_Native.Some (vars)))
end
| uu____4999 -> begin
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
| uu____5080 -> begin
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
| uu____5115 -> begin
false
end))


let uu___is_FullMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullMatch -> begin
true
end
| uu____5119 -> begin
false
end))


let string_of_option : 'Auu____5123 . ('Auu____5123  ->  Prims.string)  ->  'Auu____5123 FStar_Pervasives_Native.option  ->  Prims.string = (fun f uu___104_5136 -> (match (uu___104_5136) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____5142 = (f x)
in (Prims.strcat "Some " uu____5142))
end))


let string_of_match_result : match_result  ->  Prims.string = (fun uu___105_5145 -> (match (uu___105_5145) with
| MisMatch (d1, d2) -> begin
(

let uu____5156 = (

let uu____5157 = (string_of_option FStar_Syntax_Print.delta_depth_to_string d1)
in (

let uu____5158 = (

let uu____5159 = (

let uu____5160 = (string_of_option FStar_Syntax_Print.delta_depth_to_string d2)
in (Prims.strcat uu____5160 ")"))
in (Prims.strcat ") (" uu____5159))
in (Prims.strcat uu____5157 uu____5158)))
in (Prims.strcat "MisMatch (" uu____5156))
end
| HeadMatch -> begin
"HeadMatch"
end
| FullMatch -> begin
"FullMatch"
end))


let head_match : match_result  ->  match_result = (fun uu___106_5163 -> (match (uu___106_5163) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____5178 -> begin
HeadMatch
end))


let and_match : match_result  ->  (Prims.unit  ->  match_result)  ->  match_result = (fun m1 m2 -> (match (m1) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| HeadMatch -> begin
(

let uu____5204 = (m2 ())
in (match (uu____5204) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____5219 -> begin
HeadMatch
end))
end
| FullMatch -> begin
(m2 ())
end))


let fv_delta_depth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.delta_depth = (fun env fv -> (match (fv.FStar_Syntax_Syntax.fv_delta) with
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(match (((Prims.op_Equality env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr) && (not (env.FStar_TypeChecker_Env.is_iface)))) with
| true -> begin
d
end
| uu____5227 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
end
| FStar_Syntax_Syntax.Delta_defined_at_level (uu____5228) -> begin
(

let uu____5229 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5229) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Syntax.Delta_constant
end
| uu____5240 -> begin
fv.FStar_Syntax_Syntax.fv_delta
end))
end
| d -> begin
d
end))


let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____5259) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____5268) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____5296 = (FStar_Syntax_Util.unfold_lazy i)
in (delta_depth_of_term env uu____5296))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_bvar (uu____5297) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_name (uu____5298) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uvar (uu____5299) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_let (uu____5316) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_match (uu____5329) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____5353) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____5359, uu____5360) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____5402) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____5423; FStar_Syntax_Syntax.index = uu____5424; FStar_Syntax_Syntax.sort = t2}, uu____5426) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_constant (uu____5433) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_type (uu____5434) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____5435) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____5448) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_abs (uu____5455) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5473 = (fv_delta_depth env fv)
in FStar_Pervasives_Native.Some (uu____5473))
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
| uu____5487 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____5494 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____5494) with
| true -> begin
FullMatch
end
| uu____5495 -> begin
(

let uu____5496 = (

let uu____5505 = (

let uu____5508 = (fv_delta_depth env f)
in FStar_Pervasives_Native.Some (uu____5508))
in (

let uu____5509 = (

let uu____5512 = (fv_delta_depth env g)
in FStar_Pervasives_Native.Some (uu____5512))
in ((uu____5505), (uu____5509))))
in MisMatch (uu____5496))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____5518), FStar_Syntax_Syntax.Tm_uinst (g, uu____5520)) -> begin
(

let uu____5529 = (head_matches env f g)
in (FStar_All.pipe_right uu____5529 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____5532 = (FStar_Const.eq_const c d)
in (match (uu____5532) with
| true -> begin
FullMatch
end
| uu____5533 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, uu____5539), FStar_Syntax_Syntax.Tm_uvar (uv', uu____5541)) -> begin
(

let uu____5590 = (FStar_Syntax_Unionfind.equiv uv uv')
in (match (uu____5590) with
| true -> begin
FullMatch
end
| uu____5591 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____5597), FStar_Syntax_Syntax.Tm_refine (y, uu____5599)) -> begin
(

let uu____5608 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____5608 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____5610), uu____5611) -> begin
(

let uu____5616 = (head_matches env x.FStar_Syntax_Syntax.sort t21)
in (FStar_All.pipe_right uu____5616 head_match))
end
| (uu____5617, FStar_Syntax_Syntax.Tm_refine (x, uu____5619)) -> begin
(

let uu____5624 = (head_matches env t11 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____5624 head_match))
end
| (FStar_Syntax_Syntax.Tm_type (uu____5625), FStar_Syntax_Syntax.Tm_type (uu____5626)) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_arrow (uu____5627), FStar_Syntax_Syntax.Tm_arrow (uu____5628)) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_match (uu____5653), FStar_Syntax_Syntax.Tm_match (uu____5654)) -> begin
((

let uu____5700 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelDelta")))
in (match (uu____5700) with
| true -> begin
(FStar_ST.op_Colon_Equals FStar_Syntax_Util.debug_term_eq true)
end
| uu____5726 -> begin
()
end));
(

let uu____5727 = (FStar_Syntax_Util.term_eq t11 t21)
in (match (uu____5727) with
| true -> begin
FullMatch
end
| uu____5728 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end));
)
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____5734), FStar_Syntax_Syntax.Tm_app (head', uu____5736)) -> begin
(

let uu____5777 = (head_matches env head1 head')
in (FStar_All.pipe_right uu____5777 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____5779), uu____5780) -> begin
(

let uu____5801 = (head_matches env head1 t21)
in (FStar_All.pipe_right uu____5801 head_match))
end
| (uu____5802, FStar_Syntax_Syntax.Tm_app (head1, uu____5804)) -> begin
(

let uu____5825 = (head_matches env t11 head1)
in (FStar_All.pipe_right uu____5825 head_match))
end
| uu____5826 -> begin
(

let uu____5831 = (

let uu____5840 = (delta_depth_of_term env t11)
in (

let uu____5843 = (delta_depth_of_term env t21)
in ((uu____5840), (uu____5843))))
in MisMatch (uu____5831))
end))))


let head_matches_delta : 'Auu____5855 . FStar_TypeChecker_Env.env  ->  'Auu____5855  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (match_result * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) FStar_Pervasives_Native.option) = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let uu____5888 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____5888) with
| (head1, uu____5906) -> begin
(

let uu____5927 = (

let uu____5928 = (FStar_Syntax_Util.un_uinst head1)
in uu____5928.FStar_Syntax_Syntax.n)
in (match (uu____5927) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5934 = (

let uu____5935 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____5935 FStar_Option.isSome))
in (match (uu____5934) with
| true -> begin
(

let uu____5954 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right uu____5954 (fun _0_45 -> FStar_Pervasives_Native.Some (_0_45))))
end
| uu____5957 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____5958 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (

let success = (fun d r t11 t21 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (((t11), (t21)))
end
| uu____5998 -> begin
FStar_Pervasives_Native.None
end))))
in (

let fail1 = (fun r -> ((r), (FStar_Pervasives_Native.None)))
in (

let rec aux = (fun retry n_delta t11 t21 -> (

let r = (head_matches env t11 t21)
in (match (r) with
| MisMatch (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational), uu____6061) -> begin
(match ((not (retry))) with
| true -> begin
(fail1 r)
end
| uu____6078 -> begin
(

let uu____6079 = (

let uu____6088 = (maybe_inline t11)
in (

let uu____6091 = (maybe_inline t21)
in ((uu____6088), (uu____6091))))
in (match (uu____6079) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(fail1 r)
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
| MisMatch (uu____6128, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational)) -> begin
(match ((not (retry))) with
| true -> begin
(fail1 r)
end
| uu____6145 -> begin
(

let uu____6146 = (

let uu____6155 = (maybe_inline t11)
in (

let uu____6158 = (maybe_inline t21)
in ((uu____6155), (uu____6158))))
in (match (uu____6146) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(fail1 r)
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
(

let uu____6201 = (FStar_TypeChecker_Common.decr_delta_depth d1)
in (match (uu____6201) with
| FStar_Pervasives_Native.None -> begin
(fail1 r)
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let t12 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env wl t11)
in (

let t22 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env wl t21)
in (aux retry (n_delta + (Prims.parse_int "1")) t12 t22)))
end))
end
| MisMatch (FStar_Pervasives_Native.Some (d1), FStar_Pervasives_Native.Some (d2)) -> begin
(

let d1_greater_than_d2 = (FStar_TypeChecker_Common.delta_depth_greater_than d1 d2)
in (

let uu____6224 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env wl t11)
in ((t1'), (t21)))
end
| uu____6234 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env wl t21)
in ((t11), (t2')))
end)
in (match (uu____6224) with
| (t12, t22) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
end)))
end
| MisMatch (uu____6248) -> begin
(fail1 r)
end
| uu____6257 -> begin
(success n_delta r t11 t21)
end)))
in (

let r = (aux true (Prims.parse_int "0") t1 t2)
in ((

let uu____6270 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelDelta")))
in (match (uu____6270) with
| true -> begin
(

let uu____6271 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6272 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____6273 = (string_of_match_result (FStar_Pervasives_Native.fst r))
in (FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6271 uu____6272 uu____6273))))
end
| uu____6280 -> begin
()
end));
r;
)))))))

type tc =
| T of (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term))
| C of FStar_Syntax_Syntax.comp


let uu___is_T : tc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| T (_0) -> begin
true
end
| uu____6313 -> begin
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
| uu____6349 -> begin
false
end))


let __proj__C__item___0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_0) -> begin
_0
end))


type tcs =
tc Prims.list


let tc_to_string : tc  ->  Prims.string = (fun uu___107_6361 -> (match (uu___107_6361) with
| T (t, uu____6363) -> begin
(term_to_string t)
end
| C (c) -> begin
(FStar_Syntax_Print.comp_to_string c)
end))


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____6379 = (FStar_Syntax_Util.type_u ())
in (match (uu____6379) with
| (t, uu____6385) -> begin
(

let uu____6386 = (new_uvar r binders t)
in (FStar_Pervasives_Native.fst uu____6386))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____6397 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____6397 FStar_Pervasives_Native.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * variance * tc) Prims.list) = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (

let uu____6461 = (head_matches env t1 t')
in (match (uu____6461) with
| MisMatch (uu____6462) -> begin
false
end
| uu____6471 -> begin
true
end)))
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let rebuild = (fun args' -> (

let args1 = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((uu____6567, imp), T (t2, uu____6570)) -> begin
((t2), (imp))
end
| uu____6589 -> begin
(failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd1), (args1)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun uu____6656 -> (match (uu____6656) with
| (t2, uu____6670) -> begin
((FStar_Pervasives_Native.None), (INVARIANT), (T (((t2), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____6713 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6713) with
| (bs1, c1) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs2 tcs1 -> (match (((bs2), (tcs1))) with
| (((x, imp))::bs3, (T (t2, uu____6788))::tcs2) -> begin
(aux (((((

let uu___132_6823 = x
in {FStar_Syntax_Syntax.ppname = uu___132_6823.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___132_6823.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (imp)))::out) bs3 tcs2)
end
| ([], (C (c2))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c2)
end
| uu____6841 -> begin
(failwith "Bad reconstruction")
end))
in (aux [] bs1 tcs)))
in (

let rec decompose1 = (fun out uu___108_6894 -> (match (uu___108_6894) with
| [] -> begin
(FStar_List.rev ((((FStar_Pervasives_Native.None), (COVARIANT), (C (c1))))::out))
end
| (hd1)::rest -> begin
(decompose1 ((((FStar_Pervasives_Native.Some (hd1)), (CONTRAVARIANT), (T ((((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (

let uu____7011 = (decompose1 [] bs1)
in ((rebuild), (matches), (uu____7011)))))
end))
end
| uu____7060 -> begin
(

let rebuild = (fun uu___109_7066 -> (match (uu___109_7066) with
| [] -> begin
t1
end
| uu____7069 -> begin
(failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t2 -> (FStar_Util.return_all true))), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun uu___110_7100 -> (match (uu___110_7100) with
| T (t, uu____7102) -> begin
t
end
| uu____7111 -> begin
(failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun uu___111_7114 -> (match (uu___111_7114) with
| T (t, uu____7116) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| uu____7125 -> begin
(failwith "Impossible")
end))


let imitation_sub_probs : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * variance * tc) Prims.list  ->  (FStar_TypeChecker_Common.prob Prims.list * tc Prims.list * FStar_Syntax_Syntax.formula) = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope1 args q -> (match (q) with
| (uu____7241, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope1 r)
in (

let uu____7266 = (new_uvar r scope1 k)
in (match (uu____7266) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| uu____7284 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) FStar_Pervasives_Native.None r)
end)
in (

let uu____7301 = (

let uu____7302 = (mk_problem scope1 orig gi_ps (vary_rel rel variance) ti FStar_Pervasives_Native.None "type subterm")
in (FStar_All.pipe_left (fun _0_46 -> FStar_TypeChecker_Common.TProb (_0_46)) uu____7302))
in ((T (((gi_xs), (mk_kind)))), (uu____7301))))
end)))
end
| (uu____7315, uu____7316, C (uu____7317)) -> begin
(failwith "impos")
end))
in (

let rec aux = (fun scope1 args qs1 -> (match (qs1) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs2 -> begin
(

let uu____7464 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.pos = uu____7481; FStar_Syntax_Syntax.vars = uu____7482})) -> begin
(

let uu____7505 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____7505) with
| (T (gi_xs, uu____7529), prob) -> begin
(

let uu____7539 = (

let uu____7540 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_47 -> C (_0_47)) uu____7540))
in ((uu____7539), ((prob)::[])))
end
| uu____7543 -> begin
(failwith "impossible")
end))
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.pos = uu____7558; FStar_Syntax_Syntax.vars = uu____7559})) -> begin
(

let uu____7582 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____7582) with
| (T (gi_xs, uu____7606), prob) -> begin
(

let uu____7616 = (

let uu____7617 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_48 -> C (_0_48)) uu____7617))
in ((uu____7616), ((prob)::[])))
end
| uu____7620 -> begin
(failwith "impossible")
end))
end
| (uu____7631, uu____7632, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.pos = uu____7634; FStar_Syntax_Syntax.vars = uu____7635})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((FStar_Pervasives_Native.None), (INVARIANT), (T ((((FStar_Pervasives_Native.fst t)), (generic_kind))))))))
in (

let components1 = (((FStar_Pervasives_Native.None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let uu____7766 = (

let uu____7775 = (FStar_List.map (sub_prob scope1 args) components1)
in (FStar_All.pipe_right uu____7775 FStar_List.unzip))
in (match (uu____7766) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (

let uu____7829 = (

let uu____7830 = (

let uu____7833 = (FStar_List.hd tcs)
in (FStar_All.pipe_right uu____7833 un_T))
in (

let uu____7834 = (

let uu____7843 = (FStar_List.tl tcs)
in (FStar_All.pipe_right uu____7843 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____7830; FStar_Syntax_Syntax.effect_args = uu____7834; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____7829))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| uu____7852 -> begin
(

let uu____7865 = (sub_prob scope1 args q)
in (match (uu____7865) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (uu____7464) with
| (tc, probs) -> begin
(

let uu____7896 = (match (((q), (tc))) with
| ((FStar_Pervasives_Native.Some (b, imp), uu____7959, uu____7960), T (t, uu____7962)) -> begin
(

let b1 = (((

let uu___133_7999 = b
in {FStar_Syntax_Syntax.ppname = uu___133_7999.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___133_7999.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let uu____8000 = (

let uu____8007 = (FStar_Syntax_Util.arg_of_non_null_binder b1)
in (uu____8007)::args)
in ((FStar_Pervasives_Native.Some (b1)), ((b1)::scope1), (uu____8000))))
end
| uu____8042 -> begin
((FStar_Pervasives_Native.None), (scope1), (args))
end)
in (match (uu____7896) with
| (bopt, scope2, args1) -> begin
(

let uu____8126 = (aux scope2 args1 qs2)
in (match (uu____8126) with
| (sub_probs, tcs, f) -> begin
(

let f1 = (match (bopt) with
| FStar_Pervasives_Native.None -> begin
(

let f1 = (

let uu____8164 = (

let uu____8167 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst))))
in (f)::uu____8167)
in (FStar_Syntax_Util.mk_conj_l uu____8164))
in ((def_check_closed (p_loc orig) "imitation_sub_probs (1)" f1);
f1;
))
end
| FStar_Pervasives_Native.Some (b) -> begin
(

let u_b = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (

let f1 = (

let uu____8192 = (

let uu____8195 = (FStar_Syntax_Util.mk_forall u_b (FStar_Pervasives_Native.fst b) f)
in (

let uu____8196 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst))))
in (uu____8195)::uu____8196))
in (FStar_Syntax_Util.mk_conj_l uu____8192))
in ((def_check_closed (p_loc orig) "imitation_sub_probs (2)" f1);
f1;
)))
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


let compress_tprob : 'Auu____8265 . worklist  ->  (FStar_Syntax_Syntax.term, 'Auu____8265) FStar_TypeChecker_Common.problem  ->  (FStar_Syntax_Syntax.term, 'Auu____8265) FStar_TypeChecker_Common.problem = (fun wl p -> (

let uu___134_8286 = p
in (

let uu____8291 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____8292 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___134_8286.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____8291; FStar_TypeChecker_Common.relation = uu___134_8286.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____8292; FStar_TypeChecker_Common.element = uu___134_8286.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___134_8286.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___134_8286.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___134_8286.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___134_8286.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___134_8286.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p1) -> begin
(

let uu____8304 = (compress_tprob wl p1)
in (FStar_All.pipe_right uu____8304 (fun _0_49 -> FStar_TypeChecker_Common.TProb (_0_49))))
end
| FStar_TypeChecker_Common.CProb (uu____8313) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (

let uu____8333 = (compress_prob wl pr)
in (FStar_All.pipe_right uu____8333 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____8343 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____8343) with
| (lh, uu____8363) -> begin
(

let uu____8384 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____8384) with
| (rh, uu____8404) -> begin
(

let uu____8425 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____8442), FStar_Syntax_Syntax.Tm_uvar (uu____8443)) -> begin
((flex_flex), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____8480), uu____8481) when ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (uu____8502, FStar_Syntax_Syntax.Tm_uvar (uu____8503)) when ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____8524), uu____8525) -> begin
(

let uu____8542 = (base_and_refinement wl.tcenv tp.FStar_TypeChecker_Common.rhs)
in (match (uu____8542) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
((flex_rigid), (tp))
end
| uu____8591 -> begin
(

let rank = (

let uu____8599 = (is_top_level_prob prob)
in (match (uu____8599) with
| true -> begin
flex_refine
end
| uu____8600 -> begin
flex_refine_inner
end))
in (

let uu____8601 = (

let uu___135_8606 = tp
in (

let uu____8611 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___135_8606.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___135_8606.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___135_8606.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____8611; FStar_TypeChecker_Common.element = uu___135_8606.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___135_8606.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___135_8606.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___135_8606.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___135_8606.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___135_8606.FStar_TypeChecker_Common.rank}))
in ((rank), (uu____8601))))
end)
end))
end
| (uu____8622, FStar_Syntax_Syntax.Tm_uvar (uu____8623)) -> begin
(

let uu____8640 = (base_and_refinement wl.tcenv tp.FStar_TypeChecker_Common.lhs)
in (match (uu____8640) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
((rigid_flex), (tp))
end
| uu____8689 -> begin
(

let uu____8696 = (

let uu___136_8703 = tp
in (

let uu____8708 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___136_8703.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____8708; FStar_TypeChecker_Common.relation = uu___136_8703.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___136_8703.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___136_8703.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___136_8703.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___136_8703.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___136_8703.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___136_8703.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___136_8703.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (uu____8696)))
end)
end))
end
| (uu____8725, uu____8726) -> begin
((rigid_rigid), (tp))
end)
in (match (uu____8425) with
| (rank, tp1) -> begin
(

let uu____8745 = (FStar_All.pipe_right (

let uu___137_8751 = tp1
in {FStar_TypeChecker_Common.pid = uu___137_8751.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___137_8751.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___137_8751.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___137_8751.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___137_8751.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___137_8751.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___137_8751.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___137_8751.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___137_8751.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rank)}) (fun _0_50 -> FStar_TypeChecker_Common.TProb (_0_50)))
in ((rank), (uu____8745)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____8761 = (FStar_All.pipe_right (

let uu___138_8767 = cp
in {FStar_TypeChecker_Common.pid = uu___138_8767.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___138_8767.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___138_8767.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___138_8767.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___138_8767.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___138_8767.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___138_8767.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___138_8767.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___138_8767.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rigid_rigid)}) (fun _0_51 -> FStar_TypeChecker_Common.CProb (_0_51)))
in ((rigid_rigid), (uu____8761)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun uu____8822 probs -> (match (uu____8822) with
| (min_rank, min1, out) -> begin
(match (probs) with
| [] -> begin
((min1), (out), (min_rank))
end
| (hd1)::tl1 -> begin
(

let uu____8875 = (rank wl hd1)
in (match (uu____8875) with
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
| uu____8921 -> begin
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
| uu____8951 -> begin
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
| uu____8982 -> begin
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
| uu____8994 -> begin
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
| uu____9006 -> begin
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

let uu____9046 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____9046) with
| (k, uu____9052) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Syntax_Unionfind.univ_equiv v1 v2)
end
| uu____9062 -> begin
false
end)
end)))))
end
| uu____9063 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (

let rec filter_out_common_univs = (fun u12 u22 -> (

let common_elts = (FStar_All.pipe_right u12 (FStar_List.fold_left (fun uvs uv1 -> (

let uu____9111 = (FStar_All.pipe_right u22 (FStar_List.existsML (fun uv2 -> (

let uu____9117 = (FStar_Syntax_Util.compare_univs uv1 uv2)
in (Prims.op_Equality uu____9117 (Prims.parse_int "0"))))))
in (match (uu____9111) with
| true -> begin
(uv1)::uvs
end
| uu____9120 -> begin
uvs
end))) []))
in (

let filter1 = (FStar_List.filter (fun u -> (

let uu____9131 = (FStar_All.pipe_right common_elts (FStar_List.existsML (fun u' -> (

let uu____9137 = (FStar_Syntax_Util.compare_univs u u')
in (Prims.op_Equality uu____9137 (Prims.parse_int "0"))))))
in (not (uu____9131)))))
in (

let uu____9138 = (filter1 u12)
in (

let uu____9141 = (filter1 u22)
in ((uu____9138), (uu____9141)))))))
in (

let try_umax_components = (fun u12 u22 msg -> (match (((u12), (u22))) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(

let uu____9164 = (filter_out_common_univs us1 us2)
in (match (uu____9164) with
| (us11, us21) -> begin
(match ((Prims.op_Equality (FStar_List.length us11) (FStar_List.length us21))) with
| true -> begin
(

let rec aux = (fun wl1 us12 us22 -> (match (((us12), (us22))) with
| ((u13)::us13, (u23)::us23) -> begin
(

let uu____9217 = (really_solve_universe_eq pid_orig wl1 u13 u23)
in (match (uu____9217) with
| USolved (wl2) -> begin
(aux wl2 us13 us23)
end
| failed -> begin
failed
end))
end
| uu____9220 -> begin
USolved (wl1)
end))
in (aux wl us11 us21))
end
| uu____9229 -> begin
(

let uu____9230 = (

let uu____9231 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____9232 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" uu____9231 uu____9232)))
in UFailed (uu____9230))
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

let uu____9252 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____9252) with
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

let uu____9274 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____9274) with
| USolved (wl2) -> begin
(aux wl2 us2)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____9277 -> begin
(

let uu____9282 = (

let uu____9283 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____9284 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" uu____9283 uu____9284 msg)))
in UFailed (uu____9282))
end))
in (match (((u11), (u21))) with
| (FStar_Syntax_Syntax.U_bvar (uu____9285), uu____9286) -> begin
(

let uu____9287 = (

let uu____9288 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____9289 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____9288 uu____9289)))
in (failwith uu____9287))
end
| (FStar_Syntax_Syntax.U_unknown, uu____9290) -> begin
(

let uu____9291 = (

let uu____9292 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____9293 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____9292 uu____9293)))
in (failwith uu____9291))
end
| (uu____9294, FStar_Syntax_Syntax.U_bvar (uu____9295)) -> begin
(

let uu____9296 = (

let uu____9297 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____9298 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____9297 uu____9298)))
in (failwith uu____9296))
end
| (uu____9299, FStar_Syntax_Syntax.U_unknown) -> begin
(

let uu____9300 = (

let uu____9301 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____9302 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____9301 uu____9302)))
in (failwith uu____9300))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____9305 -> begin
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

let uu____9326 = (FStar_Syntax_Unionfind.univ_equiv v1 v2)
in (match (uu____9326) with
| true -> begin
USolved (wl)
end
| uu____9327 -> begin
(

let wl1 = (extend_solution pid_orig ((UNIV (((v1), (u21))))::[]) wl)
in USolved (wl1))
end))
end
| (FStar_Syntax_Syntax.U_unif (v1), u) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____9348 = (occurs_univ v1 u3)
in (match (uu____9348) with
| true -> begin
(

let uu____9349 = (

let uu____9350 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____9351 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____9350 uu____9351)))
in (try_umax_components u11 u21 uu____9349))
end
| uu____9352 -> begin
(

let uu____9353 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____9353))
end)))
end
| (u, FStar_Syntax_Syntax.U_unif (v1)) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____9373 = (occurs_univ v1 u3)
in (match (uu____9373) with
| true -> begin
(

let uu____9374 = (

let uu____9375 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____9376 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____9375 uu____9376)))
in (try_umax_components u11 u21 uu____9374))
end
| uu____9377 -> begin
(

let uu____9378 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____9378))
end)))
end
| (FStar_Syntax_Syntax.U_max (uu____9387), uu____9388) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____9391 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____9394 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____9394) with
| true -> begin
USolved (wl)
end
| uu____9395 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (uu____9396, FStar_Syntax_Syntax.U_max (uu____9397)) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____9400 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____9403 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____9403) with
| true -> begin
USolved (wl)
end
| uu____9404 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (FStar_Syntax_Syntax.U_succ (uu____9405), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_succ (uu____9406), FStar_Syntax_Syntax.U_name (uu____9407)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ (uu____9408)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name (uu____9409)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____9410), FStar_Syntax_Syntax.U_succ (uu____9411)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____9412), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end)))))))


let solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (match (wl.tcenv.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
USolved (wl)
end
| uu____9425 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders : 'a 'b . ('a Prims.list * ('a Prims.list  ->  'b))  ->  ('a Prims.list * ('a Prims.list  ->  'b))  ->  (('a Prims.list * 'b) * ('a Prims.list * 'b)) = (fun bc1 bc2 -> (

let uu____9498 = bc1
in (match (uu____9498) with
| (bs1, mk_cod1) -> begin
(

let uu____9539 = bc2
in (match (uu____9539) with
| (bs2, mk_cod2) -> begin
(

let rec aux = (fun bs11 bs21 -> (match (((bs11), (bs21))) with
| ((x)::xs, (y)::ys) -> begin
(

let uu____9643 = (aux xs ys)
in (match (uu____9643) with
| ((xs1, xr), (ys1, yr)) -> begin
(((((x)::xs1), (xr))), ((((y)::ys1), (yr))))
end))
end
| (xs, ys) -> begin
(

let uu____9726 = (

let uu____9733 = (mk_cod1 xs)
in (([]), (uu____9733)))
in (

let uu____9736 = (

let uu____9743 = (mk_cod2 ys)
in (([]), (uu____9743)))
in ((uu____9726), (uu____9736))))
end))
in (aux bs1 bs2))
end))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____9854 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____9854) with
| true -> begin
(

let uu____9855 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" uu____9855))
end
| uu____9856 -> begin
()
end));
(

let uu____9857 = (next_prob probs)
in (match (uu____9857) with
| (FStar_Pervasives_Native.Some (hd1), tl1, rank1) -> begin
(

let probs1 = (

let uu___139_9878 = probs
in {attempting = tl1; wl_deferred = uu___139_9878.wl_deferred; ctr = uu___139_9878.ctr; defer_ok = uu___139_9878.defer_ok; smt_ok = uu___139_9878.smt_ok; tcenv = uu___139_9878.tcenv})
in (match (hd1) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs1)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match ((((not (probs1.defer_ok)) && (flex_refine_inner <= rank1)) && (rank1 <= flex_rigid))) with
| true -> begin
(

let uu____9889 = (solve_flex_rigid_join env tp probs1)
in (match (uu____9889) with
| FStar_Pervasives_Native.None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| FStar_Pervasives_Native.Some (wl) -> begin
(solve env wl)
end))
end
| uu____9893 -> begin
(match ((((not (probs1.defer_ok)) && (rigid_flex <= rank1)) && (rank1 <= refine_flex))) with
| true -> begin
(

let uu____9894 = (solve_rigid_flex_meet env tp probs1)
in (match (uu____9894) with
| FStar_Pervasives_Native.None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| FStar_Pervasives_Native.Some (wl) -> begin
(solve env wl)
end))
end
| uu____9898 -> begin
(solve_t' env (maybe_invert tp) probs1)
end)
end)
end))
end
| (FStar_Pervasives_Native.None, uu____9899, uu____9900) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| uu____9917 -> begin
(

let uu____9926 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____9985 -> (match (uu____9985) with
| (c, uu____9993, uu____9994) -> begin
(c < probs.ctr)
end))))
in (match (uu____9926) with
| (attempt1, rest) -> begin
(match (attempt1) with
| [] -> begin
(

let uu____10035 = (FStar_List.map (fun uu____10050 -> (match (uu____10050) with
| (uu____10061, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (uu____10035))
end
| uu____10064 -> begin
(

let uu____10073 = (

let uu___140_10074 = probs
in (

let uu____10075 = (FStar_All.pipe_right attempt1 (FStar_List.map (fun uu____10096 -> (match (uu____10096) with
| (uu____10103, uu____10104, y) -> begin
y
end))))
in {attempting = uu____10075; wl_deferred = rest; ctr = uu___140_10074.ctr; defer_ok = uu___140_10074.defer_ok; smt_ok = uu___140_10074.smt_ok; tcenv = uu___140_10074.tcenv}))
in (solve env uu____10073))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____10111 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____10111) with
| USolved (wl1) -> begin
(

let uu____10113 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____10113))
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

let uu____10159 = (solve_universe_eq (p_pid orig) wl1 u1 u2)
in (match (uu____10159) with
| USolved (wl2) -> begin
(aux wl2 us11 us21)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____10162 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t11 = (whnf env t1)
in (

let t21 = (whnf env t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.pos = uu____10174; FStar_Syntax_Syntax.vars = uu____10175}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.pos = uu____10178; FStar_Syntax_Syntax.vars = uu____10179}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____10199), uu____10200) -> begin
(failwith "Impossible: expect head symbols to match")
end
| (uu____10207, FStar_Syntax_Syntax.Tm_uinst (uu____10208)) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____10215 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____10225 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10225) with
| true -> begin
(

let uu____10226 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" uu____10226 msg))
end
| uu____10227 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____10228 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist FStar_Pervasives_Native.option = (fun env tp wl -> ((

let uu____10235 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____10235) with
| true -> begin
(

let uu____10236 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" uu____10236))
end
| uu____10237 -> begin
()
end));
(

let uu____10238 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____10238) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let uu____10300 = (head_matches_delta env () t1 t2)
in (match (uu____10300) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (uu____10341) -> begin
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

let uu____10390 = (match (ts) with
| FStar_Pervasives_Native.Some (t11, t21) -> begin
(

let uu____10405 = (FStar_Syntax_Subst.compress t11)
in (

let uu____10406 = (FStar_Syntax_Subst.compress t21)
in ((uu____10405), (uu____10406))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____10411 = (FStar_Syntax_Subst.compress t1)
in (

let uu____10412 = (FStar_Syntax_Subst.compress t2)
in ((uu____10411), (uu____10412))))
end)
in (match (uu____10390) with
| (t11, t21) -> begin
(

let eq_prob = (fun t12 t22 -> (

let uu____10438 = (new_problem env t12 FStar_TypeChecker_Common.EQ t22 FStar_Pervasives_Native.None t12.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _0_52 -> FStar_TypeChecker_Common.TProb (_0_52)) uu____10438)))
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(

let uu____10469 = (

let uu____10478 = (

let uu____10481 = (

let uu____10484 = (

let uu____10485 = (

let uu____10492 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (uu____10492)))
in FStar_Syntax_Syntax.Tm_refine (uu____10485))
in (FStar_Syntax_Syntax.mk uu____10484))
in (uu____10481 FStar_Pervasives_Native.None t11.FStar_Syntax_Syntax.pos))
in (

let uu____10500 = (

let uu____10503 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (uu____10503)::[])
in ((uu____10478), (uu____10500))))
in FStar_Pervasives_Native.Some (uu____10469))
end
| (uu____10516, FStar_Syntax_Syntax.Tm_refine (x, uu____10518)) -> begin
(

let uu____10523 = (

let uu____10530 = (

let uu____10533 = (eq_prob x.FStar_Syntax_Syntax.sort t11)
in (uu____10533)::[])
in ((t11), (uu____10530)))
in FStar_Pervasives_Native.Some (uu____10523))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____10543), uu____10544) -> begin
(

let uu____10549 = (

let uu____10556 = (

let uu____10559 = (eq_prob x.FStar_Syntax_Syntax.sort t21)
in (uu____10559)::[])
in ((t21), (uu____10556)))
in FStar_Pervasives_Native.Some (uu____10549))
end
| uu____10568 -> begin
(

let uu____10573 = (FStar_Syntax_Util.head_and_args t11)
in (match (uu____10573) with
| (head1, uu____10597) -> begin
(

let uu____10618 = (

let uu____10619 = (FStar_Syntax_Util.un_uinst head1)
in uu____10619.FStar_Syntax_Syntax.n)
in (match (uu____10618) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____10630; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (i); FStar_Syntax_Syntax.fv_qual = uu____10632}) -> begin
(

let prev = (match ((i > (Prims.parse_int "1"))) with
| true -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i - (Prims.parse_int "1")))
end
| uu____10636 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
in (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t21)
in (disjoin t12 t22))))
end
| uu____10639 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____10652) -> begin
(

let uu____10677 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___112_10703 -> (match (uu___112_10703) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| FStar_Pervasives_Native.Some (rank1) when (is_rigid_flex rank1) -> begin
(

let uu____10710 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.rhs)
in (match (uu____10710) with
| (u', uu____10726) -> begin
(

let uu____10747 = (

let uu____10748 = (whnf env u')
in uu____10748.FStar_Syntax_Syntax.n)
in (match (uu____10747) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____10752) -> begin
(FStar_Syntax_Unionfind.equiv uv uv')
end
| uu____10777 -> begin
false
end))
end))
end
| uu____10778 -> begin
false
end)
end
| uu____10781 -> begin
false
end))))
in (match (uu____10677) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun uu____10815 tps -> (match (uu____10815) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
FStar_Pervasives_Native.Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____10863 = (

let uu____10872 = (whnf env hd1.FStar_TypeChecker_Common.lhs)
in (disjoin bound uu____10872))
in (match (uu____10863) with
| FStar_Pervasives_Native.Some (bound1, sub1) -> begin
(make_lower_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____10907 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let uu____10916 = (

let uu____10925 = (

let uu____10932 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((uu____10932), ([])))
in (make_lower_bound uu____10925 lower_bounds))
in (match (uu____10916) with
| FStar_Pervasives_Native.None -> begin
((

let uu____10944 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____10944) with
| true -> begin
(FStar_Util.print_string "No lower bounds\n")
end
| uu____10945 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (lhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in ((

let uu____10964 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____10964) with
| true -> begin
(

let wl' = (

let uu___141_10966 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___141_10966.wl_deferred; ctr = uu___141_10966.ctr; defer_ok = uu___141_10966.defer_ok; smt_ok = uu___141_10966.smt_ok; tcenv = uu___141_10966.tcenv})
in (

let uu____10967 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" uu____10967)))
end
| uu____10968 -> begin
()
end));
(

let uu____10969 = (solve_t env eq_prob (

let uu___142_10971 = wl
in {attempting = sub_probs; wl_deferred = uu___142_10971.wl_deferred; ctr = uu___142_10971.ctr; defer_ok = uu___142_10971.defer_ok; smt_ok = uu___142_10971.smt_ok; tcenv = uu___142_10971.tcenv}))
in (match (uu____10969) with
| Success (uu____10974) -> begin
(

let wl1 = (

let uu___143_10976 = wl
in {attempting = rest; wl_deferred = uu___143_10976.wl_deferred; ctr = uu___143_10976.ctr; defer_ok = uu___143_10976.defer_ok; smt_ok = uu___143_10976.smt_ok; tcenv = uu___143_10976.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) FStar_Pervasives_Native.None [] wl1)
in (

let uu____10978 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p FStar_Pervasives_Native.None [] wl3)) wl2 lower_bounds)
in FStar_Pervasives_Native.Some (wl2))))
end
| uu____10983 -> begin
FStar_Pervasives_Native.None
end));
))
end)))
end))
end
| uu____10984 -> begin
(failwith "Impossible: Not a rigid-flex")
end)))
end));
))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist FStar_Pervasives_Native.option = (fun env tp wl -> ((

let uu____10993 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____10993) with
| true -> begin
(

let uu____10994 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" uu____10994))
end
| uu____10995 -> begin
()
end));
(

let uu____10996 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____10996) with
| (u, args) -> begin
(

let uu____11035 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (uu____11035) with
| (ok, head_match1, partial_match, fallback, failed_match) -> begin
(

let max1 = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____11060 -> begin
i
end))
in (

let base_types_match = (fun t1 t2 -> (

let uu____11076 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____11076) with
| (h1, args1) -> begin
(

let uu____11117 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____11117) with
| (h2, uu____11137) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
(

let uu____11164 = (FStar_Syntax_Syntax.fv_eq tc1 tc2)
in (match (uu____11164) with
| true -> begin
(match ((Prims.op_Equality (FStar_List.length args1) (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____11181 -> begin
(

let uu____11182 = (

let uu____11185 = (

let uu____11186 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_53 -> FStar_TypeChecker_Common.TProb (_0_53)) uu____11186))
in (uu____11185)::[])
in FStar_Pervasives_Native.Some (uu____11182))
end)
end
| uu____11197 -> begin
FStar_Pervasives_Native.None
end))
end
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(match ((FStar_Syntax_Syntax.bv_eq a b)) with
| true -> begin
(match ((Prims.op_Equality (FStar_List.length args1) (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____11218 -> begin
(

let uu____11219 = (

let uu____11222 = (

let uu____11223 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_54 -> FStar_TypeChecker_Common.TProb (_0_54)) uu____11223))
in (uu____11222)::[])
in FStar_Pervasives_Native.Some (uu____11219))
end)
end
| uu____11234 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____11237 -> begin
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

let uu____11327 = (

let uu____11336 = (

let uu____11339 = (FStar_Syntax_Util.mk_conj phi11 phi21)
in (FStar_Syntax_Util.refine x1 uu____11339))
in ((uu____11336), (m1)))
in FStar_Pervasives_Native.Some (uu____11327))))))
end))
end
| (uu____11352, FStar_Syntax_Syntax.Tm_refine (y, uu____11354)) -> begin
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
| (FStar_Syntax_Syntax.Tm_refine (x, uu____11402), uu____11403) -> begin
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
| uu____11450 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____11503) -> begin
(

let uu____11528 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___113_11554 -> (match (uu___113_11554) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| FStar_Pervasives_Native.Some (rank1) when (is_flex_rigid rank1) -> begin
(

let uu____11561 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.lhs)
in (match (uu____11561) with
| (u', uu____11577) -> begin
(

let uu____11598 = (

let uu____11599 = (whnf env u')
in uu____11599.FStar_Syntax_Syntax.n)
in (match (uu____11598) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____11603) -> begin
(FStar_Syntax_Unionfind.equiv uv uv')
end
| uu____11628 -> begin
false
end))
end))
end
| uu____11629 -> begin
false
end)
end
| uu____11632 -> begin
false
end))))
in (match (uu____11528) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun uu____11670 tps -> (match (uu____11670) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
FStar_Pervasives_Native.Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____11732 = (

let uu____11743 = (whnf env hd1.FStar_TypeChecker_Common.rhs)
in (conjoin bound uu____11743))
in (match (uu____11732) with
| FStar_Pervasives_Native.Some (bound1, sub1) -> begin
(make_upper_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____11794 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let uu____11805 = (

let uu____11816 = (

let uu____11825 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((uu____11825), ([])))
in (make_upper_bound uu____11816 upper_bounds))
in (match (uu____11805) with
| FStar_Pervasives_Native.None -> begin
((

let uu____11839 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11839) with
| true -> begin
(FStar_Util.print_string "No upper bounds\n")
end
| uu____11840 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "joining refinements")
in ((

let uu____11865 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11865) with
| true -> begin
(

let wl' = (

let uu___144_11867 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___144_11867.wl_deferred; ctr = uu___144_11867.ctr; defer_ok = uu___144_11867.defer_ok; smt_ok = uu___144_11867.smt_ok; tcenv = uu___144_11867.tcenv})
in (

let uu____11868 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" uu____11868)))
end
| uu____11869 -> begin
()
end));
(

let uu____11870 = (solve_t env eq_prob (

let uu___145_11872 = wl
in {attempting = sub_probs; wl_deferred = uu___145_11872.wl_deferred; ctr = uu___145_11872.ctr; defer_ok = uu___145_11872.defer_ok; smt_ok = uu___145_11872.smt_ok; tcenv = uu___145_11872.tcenv}))
in (match (uu____11870) with
| Success (uu____11875) -> begin
(

let wl1 = (

let uu___146_11877 = wl
in {attempting = rest; wl_deferred = uu___146_11877.wl_deferred; ctr = uu___146_11877.ctr; defer_ok = uu___146_11877.defer_ok; smt_ok = uu___146_11877.smt_ok; tcenv = uu___146_11877.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) FStar_Pervasives_Native.None [] wl1)
in (

let uu____11879 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p FStar_Pervasives_Native.None [] wl3)) wl2 upper_bounds)
in FStar_Pervasives_Native.Some (wl2))))
end
| uu____11884 -> begin
FStar_Pervasives_Native.None
end));
))
end)))
end))
end
| uu____11885 -> begin
(failwith "Impossible: Not a flex-rigid")
end)))))
end))
end));
))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (

let rec aux = (fun scope env1 subst1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
(

let rhs_prob = (rhs scope env1 subst1)
in ((

let uu____11960 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____11960) with
| true -> begin
(

let uu____11961 = (prob_to_string env1 rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" uu____11961))
end
| uu____11962 -> begin
()
end));
(

let formula = (FStar_All.pipe_right (p_guard rhs_prob) FStar_Pervasives_Native.fst)
in FStar_Util.Inl ((((rhs_prob)::[]), (formula))));
))
end
| (((hd1, imp))::xs1, ((hd2, imp'))::ys1) when (Prims.op_Equality imp imp') -> begin
(

let hd11 = (

let uu___147_12015 = hd1
in (

let uu____12016 = (FStar_Syntax_Subst.subst subst1 hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___147_12015.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___147_12015.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____12016}))
in (

let hd21 = (

let uu___148_12020 = hd2
in (

let uu____12021 = (FStar_Syntax_Subst.subst subst1 hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___148_12020.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___148_12020.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____12021}))
in (

let prob = (

let uu____12025 = (

let uu____12030 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd11.FStar_Syntax_Syntax.sort uu____12030 hd21.FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None "Formal parameter"))
in (FStar_All.pipe_left (fun _0_55 -> FStar_TypeChecker_Common.TProb (_0_55)) uu____12025))
in (

let hd12 = (FStar_Syntax_Syntax.freshen_bv hd11)
in (

let subst2 = (

let uu____12041 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd12))))::uu____12041)
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 hd12)
in (

let uu____12045 = (aux (FStar_List.append scope ((((hd12), (imp)))::[])) env2 subst2 xs1 ys1)
in (match (uu____12045) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi1 = (

let uu____12083 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (

let uu____12088 = (close_forall env2 ((((hd12), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj uu____12083 uu____12088)))
in ((

let uu____12098 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____12098) with
| true -> begin
(

let uu____12099 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____12100 = (FStar_Syntax_Print.bv_to_string hd12)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" uu____12099 uu____12100)))
end
| uu____12101 -> begin
()
end));
FStar_Util.Inl ((((prob)::sub_probs), (phi1)));
))
end
| fail1 -> begin
fail1
end))))))))
end
| uu____12123 -> begin
FStar_Util.Inr ("arity or argument-qualifier mismatch")
end))
in (

let scope = (p_scope orig)
in (

let uu____12133 = (aux scope env [] bs1 bs2)
in (match (uu____12133) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (phi)) [] wl)
in (solve env (attempt sub_probs wl1)))
end)))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> ((def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb (problem)));
(

let uu____12158 = (compress_tprob wl problem)
in (solve_t' env uu____12158 wl));
))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> ((def_check_prob "solve_t\'.1" (FStar_TypeChecker_Common.TProb (problem)));
(

let giveup_or_defer1 = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env1 orig wl1 head1 head2 t1 t2 -> (

let uu____12192 = (head_matches_delta env1 wl1 t1 t2)
in (match (uu____12192) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____12223), uu____12224) -> begin
(

let rec may_relate = (fun head3 -> (

let uu____12249 = (

let uu____12250 = (FStar_Syntax_Subst.compress head3)
in uu____12250.FStar_Syntax_Syntax.n)
in (match (uu____12249) with
| FStar_Syntax_Syntax.Tm_name (uu____12253) -> begin
true
end
| FStar_Syntax_Syntax.Tm_match (uu____12254) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____12277; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational; FStar_Syntax_Syntax.fv_qual = uu____12278}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____12281; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (uu____12282); FStar_Syntax_Syntax.fv_qual = uu____12283}) -> begin
(Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____12287, uu____12288) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____12330) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____12336) -> begin
(may_relate t)
end
| uu____12341 -> begin
false
end)))
in (

let uu____12342 = (((may_relate head1) || (may_relate head2)) && wl1.smt_ok)
in (match (uu____12342) with
| true -> begin
(

let guard = (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_eq2 orig t1 t2)
end
| uu____12344 -> begin
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

let uu____12359 = (

let uu____12360 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t11 uu____12360 t21))
in (FStar_Syntax_Util.mk_forall u_x x uu____12359))))
end))
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB)) with
| true -> begin
(has_type_guard t1 t2)
end
| uu____12361 -> begin
(has_type_guard t2 t1)
end))
end)
in (

let uu____12362 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl1)
in (solve env1 uu____12362)))
end
| uu____12363 -> begin
(

let uu____12364 = (

let uu____12365 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____12366 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.format2 "head mismatch (%s vs %s)" uu____12365 uu____12366)))
in (giveup env1 uu____12364 orig))
end)))
end
| (uu____12367, FStar_Pervasives_Native.Some (t11, t21)) -> begin
(solve_t env1 (

let uu___149_12381 = problem
in {FStar_TypeChecker_Common.pid = uu___149_12381.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___149_12381.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___149_12381.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___149_12381.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___149_12381.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___149_12381.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___149_12381.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___149_12381.FStar_TypeChecker_Common.rank}) wl1)
end
| (uu____12382, FStar_Pervasives_Native.None) -> begin
((

let uu____12394 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____12394) with
| true -> begin
(

let uu____12395 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12396 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____12397 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____12398 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" uu____12395 uu____12396 uu____12397 uu____12398)))))
end
| uu____12399 -> begin
()
end));
(

let uu____12400 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____12400) with
| (head11, args1) -> begin
(

let uu____12437 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____12437) with
| (head21, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((Prims.op_disEquality nargs (FStar_List.length args2))) with
| true -> begin
(

let uu____12491 = (

let uu____12492 = (FStar_Syntax_Print.term_to_string head11)
in (

let uu____12493 = (args_to_string args1)
in (

let uu____12494 = (FStar_Syntax_Print.term_to_string head21)
in (

let uu____12495 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____12492 uu____12493 uu____12494 uu____12495)))))
in (giveup env1 uu____12491 orig))
end
| uu____12496 -> begin
(

let uu____12497 = ((Prims.op_Equality nargs (Prims.parse_int "0")) || (

let uu____12503 = (FStar_Syntax_Util.eq_args args1 args2)
in (Prims.op_Equality uu____12503 FStar_Syntax_Util.Equal)))
in (match (uu____12497) with
| true -> begin
(

let uu____12504 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____12504) with
| USolved (wl2) -> begin
(

let uu____12506 = (solve_prob orig FStar_Pervasives_Native.None [] wl2)
in (solve env1 uu____12506))
end
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end))
end
| uu____12509 -> begin
(

let uu____12510 = (base_and_refinement env1 t1)
in (match (uu____12510) with
| (base1, refinement1) -> begin
(

let uu____12535 = (base_and_refinement env1 t2)
in (match (uu____12535) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(

let uu____12592 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____12592) with
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end
| USolved (wl2) -> begin
(

let subprobs = (FStar_List.map2 (fun uu____12614 uu____12615 -> (match (((uu____12614), (uu____12615))) with
| ((a, uu____12633), (a', uu____12635)) -> begin
(

let uu____12644 = (

let uu____12649 = (p_scope orig)
in (mk_problem uu____12649 orig a FStar_TypeChecker_Common.EQ a' FStar_Pervasives_Native.None "index"))
in (FStar_All.pipe_left (fun _0_56 -> FStar_TypeChecker_Common.TProb (_0_56)) uu____12644))
end)) args1 args2)
in (

let formula = (

let uu____12655 = (FStar_List.map (fun p -> (FStar_Pervasives_Native.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____12655))
in (

let wl3 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) [] wl2)
in (solve env1 (attempt subprobs wl3)))))
end))
end
| uu____12661 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env1 (

let uu___150_12697 = problem
in {FStar_TypeChecker_Common.pid = uu___150_12697.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___150_12697.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___150_12697.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___150_12697.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___150_12697.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___150_12697.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___150_12697.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___150_12697.FStar_TypeChecker_Common.rank}) wl1)))
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

let force_quasi_pattern = (fun xs_opt uu____12730 -> (match (uu____12730) with
| (t, u, k, args) -> begin
(

let debug1 = (fun f -> (

let uu____12772 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12772) with
| true -> begin
(f ())
end
| uu____12773 -> begin
()
end)))
in (

let rec aux = (fun pat_args pat_args_set pattern_vars pattern_var_set seen_formals formals res_t args1 -> ((debug1 (fun uu____12868 -> (

let uu____12869 = (FStar_Syntax_Print.binders_to_string ", " pat_args)
in (FStar_Util.print1 "pat_args so far: {%s}\n" uu____12869))));
(match (((formals), (args1))) with
| ([], []) -> begin
(

let pat_args1 = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun uu____12937 -> (match (uu____12937) with
| (x, imp) -> begin
(

let uu____12948 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____12948), (imp)))
end))))
in (

let pattern_vars1 = (FStar_List.rev pattern_vars)
in (

let kk = (

let uu____12961 = (FStar_Syntax_Util.type_u ())
in (match (uu____12961) with
| (t1, uu____12967) -> begin
(

let uu____12968 = (new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1 t1)
in (FStar_Pervasives_Native.fst uu____12968))
end))
in (

let uu____12973 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk)
in (match (uu____12973) with
| (t', tm_u1) -> begin
(

let uu____12986 = (destruct_flex_t t')
in (match (uu____12986) with
| (uu____13023, u1, k1, uu____13026) -> begin
(

let all_formals = (FStar_List.rev seen_formals)
in (

let k2 = (

let uu____13085 = (FStar_Syntax_Syntax.mk_Total res_t)
in (FStar_Syntax_Util.arrow all_formals uu____13085))
in (

let sol = (

let uu____13089 = (

let uu____13098 = (u_abs k2 all_formals t')
in ((((u), (k2))), (uu____13098)))
in TERM (uu____13089))
in (

let t_app = (FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (((sol), (((t_app), (u1), (k1), (pat_args1)))))))))
end))
end)))))
end
| ((formal)::formals1, (hd1)::tl1) -> begin
((debug1 (fun uu____13233 -> (

let uu____13234 = (FStar_Syntax_Print.binder_to_string formal)
in (

let uu____13235 = (FStar_Syntax_Print.args_to_string ((hd1)::[]))
in (FStar_Util.print2 "force_quasi_pattern (case 2): formal=%s, hd=%s\n" uu____13234 uu____13235)))));
(

let uu____13248 = (pat_var_opt env pat_args hd1)
in (match (uu____13248) with
| FStar_Pervasives_Native.None -> begin
((debug1 (fun uu____13268 -> (FStar_Util.print_string "not a pattern var\n")));
(aux pat_args pat_args_set pattern_vars pattern_var_set ((formal)::seen_formals) formals1 res_t tl1);
)
end
| FStar_Pervasives_Native.Some (y) -> begin
(

let maybe_pat = (match (xs_opt) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun uu____13311 -> (match (uu____13311) with
| (x, uu____13317) -> begin
(FStar_Syntax_Syntax.bv_eq x (FStar_Pervasives_Native.fst y))
end))))
end)
in (match ((not (maybe_pat))) with
| true -> begin
(aux pat_args pat_args_set pattern_vars pattern_var_set ((formal)::seen_formals) formals1 res_t tl1)
end
| uu____13324 -> begin
((debug1 (fun uu____13332 -> (

let uu____13333 = (FStar_Syntax_Print.args_to_string ((hd1)::[]))
in (

let uu____13346 = (FStar_Syntax_Print.binder_to_string y)
in (FStar_Util.print2 "%s (var = %s) maybe pat\n" uu____13333 uu____13346)))));
(

let fvs = (FStar_Syntax_Free.names (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____13350 = (

let uu____13351 = (FStar_Util.set_is_subset_of fvs pat_args_set)
in (not (uu____13351)))
in (match (uu____13350) with
| true -> begin
((debug1 (fun uu____13363 -> (

let uu____13364 = (

let uu____13367 = (FStar_Syntax_Print.args_to_string ((hd1)::[]))
in (

let uu____13380 = (

let uu____13383 = (FStar_Syntax_Print.binder_to_string y)
in (

let uu____13384 = (

let uu____13387 = (FStar_Syntax_Print.term_to_string (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____13388 = (

let uu____13391 = (names_to_string fvs)
in (

let uu____13392 = (

let uu____13395 = (names_to_string pattern_var_set)
in (uu____13395)::[])
in (uu____13391)::uu____13392))
in (uu____13387)::uu____13388))
in (uu____13383)::uu____13384))
in (uu____13367)::uu____13380))
in (FStar_Util.print "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n" uu____13364))));
(aux pat_args pat_args_set pattern_vars pattern_var_set ((formal)::seen_formals) formals1 res_t tl1);
)
end
| uu____13396 -> begin
(

let uu____13397 = (FStar_Util.set_add (FStar_Pervasives_Native.fst y) pat_args_set)
in (

let uu____13400 = (FStar_Util.set_add (FStar_Pervasives_Native.fst formal) pattern_var_set)
in (aux ((y)::pat_args) uu____13397 ((formal)::pattern_vars) uu____13400 ((formal)::seen_formals) formals1 res_t tl1)))
end)));
)
end))
end));
)
end
| ([], (uu____13407)::uu____13408) -> begin
(

let uu____13439 = (

let uu____13452 = (FStar_TypeChecker_Normalize.unfold_whnf env res_t)
in (FStar_Syntax_Util.arrow_formals uu____13452))
in (match (uu____13439) with
| (more_formals, res_t1) -> begin
(match (more_formals) with
| [] -> begin
FStar_Pervasives_Native.None
end
| uu____13491 -> begin
(aux pat_args pat_args_set pattern_vars pattern_var_set seen_formals more_formals res_t1 args1)
end)
end))
end
| ((uu____13498)::uu____13499, []) -> begin
FStar_Pervasives_Native.None
end);
))
in (

let uu____13522 = (

let uu____13535 = (FStar_TypeChecker_Normalize.unfold_whnf env k)
in (FStar_Syntax_Util.arrow_formals uu____13535))
in (match (uu____13522) with
| (all_formals, res_t) -> begin
((debug1 (fun uu____13571 -> (

let uu____13572 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____13573 = (FStar_Syntax_Print.binders_to_string ", " all_formals)
in (

let uu____13574 = (FStar_Syntax_Print.term_to_string res_t)
in (

let uu____13575 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print4 "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n" uu____13572 uu____13573 uu____13574 uu____13575)))))));
(

let uu____13576 = (FStar_Syntax_Syntax.new_bv_set ())
in (

let uu____13579 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] uu____13576 [] uu____13579 [] all_formals res_t args)));
)
end))))
end))
in (

let use_pattern_equality = (fun orig env1 wl1 lhs pat_vars1 rhs -> (

let uu____13613 = lhs
in (match (uu____13613) with
| (t1, uv, k_uv, args_lhs) -> begin
(

let sol = (match (pat_vars1) with
| [] -> begin
rhs
end
| uu____13623 -> begin
(

let uu____13624 = (sn_binders env1 pat_vars1)
in (u_abs k_uv uu____13624 rhs))
end)
in (

let wl2 = (solve_prob orig FStar_Pervasives_Native.None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl1)
in (solve env1 wl2)))
end)))
in (

let imitate = (fun orig env1 wl1 p -> (

let uu____13647 = p
in (match (uu____13647) with
| (((u, k), xs, c), ps, (h, uu____13658, qs)) -> begin
(

let xs1 = (sn_binders env1 xs)
in (

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____13740 = (imitation_sub_probs orig env1 xs1 ps qs)
in (match (uu____13740) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (

let uu____13763 = (h gs_xs)
in (

let uu____13764 = (FStar_All.pipe_right (FStar_Syntax_Util.residual_comp_of_comp c) (fun _0_57 -> FStar_Pervasives_Native.Some (_0_57)))
in (FStar_Syntax_Util.abs xs1 uu____13763 uu____13764)))
in ((

let uu____13770 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____13770) with
| true -> begin
(

let uu____13771 = (

let uu____13774 = (

let uu____13775 = (FStar_List.map tc_to_string gs_xs)
in (FStar_All.pipe_right uu____13775 (FStar_String.concat "\n\t>")))
in (

let uu____13780 = (

let uu____13783 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____13784 = (

let uu____13787 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____13788 = (

let uu____13791 = (FStar_Syntax_Print.term_to_string im)
in (

let uu____13792 = (

let uu____13795 = (FStar_Syntax_Print.tag_of_term im)
in (

let uu____13796 = (

let uu____13799 = (

let uu____13800 = (FStar_List.map (prob_to_string env1) sub_probs)
in (FStar_All.pipe_right uu____13800 (FStar_String.concat ", ")))
in (

let uu____13805 = (

let uu____13808 = (FStar_TypeChecker_Normalize.term_to_string env1 formula)
in (uu____13808)::[])
in (uu____13799)::uu____13805))
in (uu____13795)::uu____13796))
in (uu____13791)::uu____13792))
in (uu____13787)::uu____13788))
in (uu____13783)::uu____13784))
in (uu____13774)::uu____13780))
in (FStar_Util.print "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" uu____13771))
end
| uu____13809 -> begin
()
end));
(def_check_closed (p_loc orig) "imitate" im);
(

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl1)
in (solve env1 (attempt sub_probs wl2)));
))
end))))
end)))
in (

let imitate' = (fun orig env1 wl1 uu___114_13830 -> (match (uu___114_13830) with
| FStar_Pervasives_Native.None -> begin
(giveup env1 "unable to compute subterms" orig)
end
| FStar_Pervasives_Native.Some (p) -> begin
(imitate orig env1 wl1 p)
end))
in (

let project = (fun orig env1 wl1 i p -> (

let uu____13862 = p
in (match (uu____13862) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____13953 = (FStar_List.nth ps i)
in (match (uu____13953) with
| (pi, uu____13957) -> begin
(

let uu____13962 = (FStar_List.nth xs i)
in (match (uu____13962) with
| (xi, uu____13974) -> begin
(

let rec gs = (fun k -> (

let uu____13987 = (

let uu____14000 = (FStar_TypeChecker_Normalize.unfold_whnf env1 k)
in (FStar_Syntax_Util.arrow_formals uu____14000))
in (match (uu____13987) with
| (bs, k1) -> begin
(

let rec aux = (fun subst1 bs1 -> (match (bs1) with
| [] -> begin
(([]), ([]))
end
| ((a, uu____14075))::tl1 -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst1 a.FStar_Syntax_Syntax.sort)
in (

let uu____14088 = (new_uvar r xs k_a)
in (match (uu____14088) with
| (gi_xs, gi) -> begin
(

let gi_xs1 = (FStar_TypeChecker_Normalize.eta_expand env1 gi_xs)
in (

let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps FStar_Pervasives_Native.None r)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((a), (gi_xs1))))::subst1
in (

let uu____14110 = (aux subst2 tl1)
in (match (uu____14110) with
| (gi_xs', gi_ps') -> begin
(

let uu____14137 = (

let uu____14140 = (FStar_Syntax_Syntax.as_arg gi_xs1)
in (uu____14140)::gi_xs')
in (

let uu____14141 = (

let uu____14144 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (uu____14144)::gi_ps')
in ((uu____14137), (uu____14141))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in (

let uu____14149 = (

let uu____14150 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation uu____14150))
in (match (uu____14149) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____14153 -> begin
(

let uu____14154 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (uu____14154) with
| (g_xs, uu____14166) -> begin
(

let xi1 = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (

let uu____14177 = (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs FStar_Pervasives_Native.None r)
in (

let uu____14178 = (FStar_All.pipe_right (FStar_Syntax_Util.residual_comp_of_comp c) (fun _0_58 -> FStar_Pervasives_Native.Some (_0_58)))
in (FStar_Syntax_Util.abs xs uu____14177 uu____14178)))
in (

let sub1 = (

let uu____14184 = (

let uu____14189 = (p_scope orig)
in (

let uu____14190 = (FStar_Syntax_Syntax.mk_Tm_app proj ps FStar_Pervasives_Native.None r)
in (

let uu____14193 = (

let uu____14196 = (FStar_List.map (fun uu____14211 -> (match (uu____14211) with
| (uu____14220, uu____14221, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h uu____14196))
in (mk_problem uu____14189 orig uu____14190 (p_rel orig) uu____14193 FStar_Pervasives_Native.None "projection"))))
in (FStar_All.pipe_left (fun _0_59 -> FStar_TypeChecker_Common.TProb (_0_59)) uu____14184))
in ((

let uu____14236 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____14236) with
| true -> begin
(

let uu____14237 = (FStar_Syntax_Print.term_to_string proj)
in (

let uu____14238 = (prob_to_string env1 sub1)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" uu____14237 uu____14238)))
end
| uu____14239 -> begin
()
end));
(

let wl2 = (

let uu____14241 = (

let uu____14244 = (FStar_All.pipe_left FStar_Pervasives_Native.fst (p_guard sub1))
in FStar_Pervasives_Native.Some (uu____14244))
in (solve_prob orig uu____14241 ((TERM (((u), (proj))))::[]) wl1))
in (

let uu____14253 = (solve env1 (attempt ((sub1)::[]) wl2))
in (FStar_All.pipe_left (fun _0_60 -> FStar_Pervasives_Native.Some (_0_60)) uu____14253)));
))))
end))
end)))
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl1 -> (

let uu____14284 = lhs
in (match (uu____14284) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let uu____14320 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (uu____14320) with
| (xs, c) -> begin
(match ((Prims.op_Equality (FStar_List.length xs) (FStar_List.length ps))) with
| true -> begin
(

let uu____14353 = (

let uu____14400 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____14400)))
in FStar_Pervasives_Native.Some (uu____14353))
end
| uu____14519 -> begin
(

let rec elim = (fun k args -> (

let k1 = (FStar_TypeChecker_Normalize.unfold_whnf env k)
in (

let uu____14544 = (

let uu____14551 = (

let uu____14552 = (FStar_Syntax_Subst.compress k1)
in uu____14552.FStar_Syntax_Syntax.n)
in ((uu____14551), (args)))
in (match (uu____14544) with
| (uu____14563, []) -> begin
(

let uu____14566 = (

let uu____14577 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____14577)))
in FStar_Pervasives_Native.Some (uu____14566))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____14598), uu____14599) -> begin
(

let uu____14620 = (FStar_Syntax_Util.head_and_args k1)
in (match (uu____14620) with
| (uv1, uv_args) -> begin
(

let uu____14663 = (

let uu____14664 = (FStar_Syntax_Subst.compress uv1)
in uu____14664.FStar_Syntax_Syntax.n)
in (match (uu____14663) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____14674) -> begin
(

let uu____14699 = (pat_vars env [] uv_args)
in (match (uu____14699) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (scope) -> begin
(

let xs1 = (FStar_All.pipe_right args (FStar_List.map (fun uu____14726 -> (

let uu____14727 = (

let uu____14728 = (

let uu____14729 = (

let uu____14734 = (

let uu____14735 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____14735 FStar_Pervasives_Native.fst))
in (new_uvar k1.FStar_Syntax_Syntax.pos scope uu____14734))
in (FStar_Pervasives_Native.fst uu____14729))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (k1.FStar_Syntax_Syntax.pos)) uu____14728))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____14727)))))
in (

let c1 = (

let uu____14745 = (

let uu____14746 = (

let uu____14751 = (

let uu____14752 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____14752 FStar_Pervasives_Native.fst))
in (new_uvar k1.FStar_Syntax_Syntax.pos scope uu____14751))
in (FStar_Pervasives_Native.fst uu____14746))
in (FStar_Syntax_Syntax.mk_Total uu____14745))
in (

let k' = (FStar_Syntax_Util.arrow xs1 c1)
in (

let uv_sol = (

let uu____14765 = (

let uu____14768 = (

let uu____14769 = (

let uu____14772 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____14772 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Util.residual_tot uu____14769))
in FStar_Pervasives_Native.Some (uu____14768))
in (FStar_Syntax_Util.abs scope k' uu____14765))
in ((def_check_closed (p_loc orig) "solve_t_flex_rigid.subterms" uv_sol);
(FStar_Syntax_Util.set_uvar uvar uv_sol);
FStar_Pervasives_Native.Some (((xs1), (c1)));
)))))
end))
end
| uu____14791 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_app (uu____14796), uu____14797) -> begin
(

let uu____14816 = (FStar_Syntax_Util.head_and_args k1)
in (match (uu____14816) with
| (uv1, uv_args) -> begin
(

let uu____14859 = (

let uu____14860 = (FStar_Syntax_Subst.compress uv1)
in uu____14860.FStar_Syntax_Syntax.n)
in (match (uu____14859) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____14870) -> begin
(

let uu____14895 = (pat_vars env [] uv_args)
in (match (uu____14895) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (scope) -> begin
(

let xs1 = (FStar_All.pipe_right args (FStar_List.map (fun uu____14922 -> (

let uu____14923 = (

let uu____14924 = (

let uu____14925 = (

let uu____14930 = (

let uu____14931 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____14931 FStar_Pervasives_Native.fst))
in (new_uvar k1.FStar_Syntax_Syntax.pos scope uu____14930))
in (FStar_Pervasives_Native.fst uu____14925))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (k1.FStar_Syntax_Syntax.pos)) uu____14924))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____14923)))))
in (

let c1 = (

let uu____14941 = (

let uu____14942 = (

let uu____14947 = (

let uu____14948 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____14948 FStar_Pervasives_Native.fst))
in (new_uvar k1.FStar_Syntax_Syntax.pos scope uu____14947))
in (FStar_Pervasives_Native.fst uu____14942))
in (FStar_Syntax_Syntax.mk_Total uu____14941))
in (

let k' = (FStar_Syntax_Util.arrow xs1 c1)
in (

let uv_sol = (

let uu____14961 = (

let uu____14964 = (

let uu____14965 = (

let uu____14968 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____14968 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Util.residual_tot uu____14965))
in FStar_Pervasives_Native.Some (uu____14964))
in (FStar_Syntax_Util.abs scope k' uu____14961))
in ((def_check_closed (p_loc orig) "solve_t_flex_rigid.subterms" uv_sol);
(FStar_Syntax_Util.set_uvar uvar uv_sol);
FStar_Pervasives_Native.Some (((xs1), (c1)));
)))))
end))
end
| uu____14987 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs1, c1), uu____14994) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs1)
in (match ((Prims.op_Equality n_xs n_args)) with
| true -> begin
(

let uu____15035 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (FStar_All.pipe_right uu____15035 (fun _0_61 -> FStar_Pervasives_Native.Some (_0_61))))
end
| uu____15054 -> begin
(match ((n_xs < n_args)) with
| true -> begin
(

let uu____15071 = (FStar_Util.first_N n_xs args)
in (match (uu____15071) with
| (args1, rest) -> begin
(

let uu____15100 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (match (uu____15100) with
| (xs2, c2) -> begin
(

let uu____15113 = (elim (FStar_Syntax_Util.comp_result c2) rest)
in (FStar_Util.bind_opt uu____15113 (fun uu____15137 -> (match (uu____15137) with
| (xs', c3) -> begin
FStar_Pervasives_Native.Some ((((FStar_List.append xs2 xs')), (c3)))
end))))
end))
end))
end
| uu____15176 -> begin
(

let uu____15177 = (FStar_Util.first_N n_args xs1)
in (match (uu____15177) with
| (xs2, rest) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c1)))) FStar_Pervasives_Native.None k1.FStar_Syntax_Syntax.pos)
in (

let uu____15245 = (

let uu____15250 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs2 uu____15250))
in (FStar_All.pipe_right uu____15245 (fun _0_62 -> FStar_Pervasives_Native.Some (_0_62)))))
end))
end)
end)))
end
| uu____15265 -> begin
(

let uu____15272 = (

let uu____15277 = (

let uu____15278 = (FStar_Syntax_Print.uvar_to_string uv)
in (

let uu____15279 = (FStar_Syntax_Print.term_to_string k1)
in (

let uu____15280 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" uu____15278 uu____15279 uu____15280))))
in ((FStar_Errors.Fatal_IllTyped), (uu____15277)))
in (FStar_Errors.raise_error uu____15272 t1.FStar_Syntax_Syntax.pos))
end))))
in (

let uu____15287 = (elim k_uv ps)
in (FStar_Util.bind_opt uu____15287 (fun uu____15342 -> (match (uu____15342) with
| (xs1, c1) -> begin
(

let uu____15391 = (

let uu____15432 = (decompose env t2)
in ((((((uv), (k_uv))), (xs1), (c1))), (ps), (uu____15432)))
in FStar_Pervasives_Native.Some (uu____15391))
end)))))
end)
end)))
in (

let imitate_or_project = (fun n1 lhs1 rhs stopt -> (

let fail1 = (fun uu____15553 -> (giveup env "flex-rigid case failed all backtracking attempts" orig))
in (

let rec try_project = (fun st i -> (match ((i >= n1)) with
| true -> begin
(fail1 ())
end
| uu____15565 -> begin
(

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____15567 = (project orig env wl1 i st)
in (match (uu____15567) with
| FStar_Pervasives_Native.None -> begin
((FStar_Syntax_Unionfind.rollback tx);
(try_project st (i + (Prims.parse_int "1")));
)
end
| FStar_Pervasives_Native.Some (Failed (uu____15581)) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(try_project st (i + (Prims.parse_int "1")));
)
end
| FStar_Pervasives_Native.Some (sol) -> begin
sol
end)))
end))
in (match ((FStar_Option.isSome stopt)) with
| true -> begin
(

let st = (FStar_Util.must stopt)
in (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____15596 = (imitate orig env wl1 st)
in (match (uu____15596) with
| Failed (uu____15601) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(try_project st (Prims.parse_int "0"));
)
end
| sol -> begin
sol
end))))
end
| uu____15614 -> begin
(fail1 ())
end))))
in (

let pattern_eq_imitate_or_project = (fun n1 lhs1 rhs stopt -> (

let uu____15632 = (force_quasi_pattern FStar_Pervasives_Native.None lhs1)
in (match (uu____15632) with
| FStar_Pervasives_Native.None -> begin
(imitate_or_project n1 lhs1 rhs stopt)
end
| FStar_Pervasives_Native.Some (sol, forced_lhs_pattern) -> begin
(

let uu____15655 = forced_lhs_pattern
in (match (uu____15655) with
| (lhs_t, uu____15657, uu____15658, uu____15659) -> begin
((

let uu____15661 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____15661) with
| true -> begin
(

let uu____15662 = lhs1
in (match (uu____15662) with
| (t0, uu____15664, uu____15665, uu____15666) -> begin
(

let uu____15667 = forced_lhs_pattern
in (match (uu____15667) with
| (t11, uu____15669, uu____15670, uu____15671) -> begin
(

let uu____15672 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____15673 = (FStar_Syntax_Print.term_to_string t11)
in (FStar_Util.print2 "force_quasi_pattern succeeded, turning %s into %s\n" uu____15672 uu____15673)))
end))
end))
end
| uu____15674 -> begin
()
end));
(

let rhs_vars = (FStar_Syntax_Free.names rhs)
in (

let lhs_vars = (FStar_Syntax_Free.names lhs_t)
in (

let uu____15681 = (FStar_Util.set_is_subset_of rhs_vars lhs_vars)
in (match (uu____15681) with
| true -> begin
((

let uu____15683 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____15683) with
| true -> begin
(

let uu____15684 = (FStar_Syntax_Print.term_to_string rhs)
in (

let uu____15685 = (names_to_string rhs_vars)
in (

let uu____15686 = (names_to_string lhs_vars)
in (FStar_Util.print3 "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n" uu____15684 uu____15685 uu____15686))))
end
| uu____15687 -> begin
()
end));
(

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let wl2 = (extend_solution (p_pid orig) ((sol)::[]) wl1)
in (

let uu____15690 = (

let uu____15691 = (FStar_TypeChecker_Common.as_tprob orig)
in (solve_t env uu____15691 wl2))
in (match (uu____15690) with
| Failed (uu____15692) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(imitate_or_project n1 lhs1 rhs stopt);
)
end
| sol1 -> begin
sol1
end))));
)
end
| uu____15699 -> begin
((

let uu____15701 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____15701) with
| true -> begin
(FStar_Util.print_string "fvar check failed for quasi pattern ... im/proj\n")
end
| uu____15702 -> begin
()
end));
(imitate_or_project n1 lhs1 rhs stopt);
)
end))));
)
end))
end)))
in (

let check_head = (fun fvs1 t21 -> (

let uu____15714 = (FStar_Syntax_Util.head_and_args t21)
in (match (uu____15714) with
| (hd1, uu____15730) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____15751) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____15764) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____15765) -> begin
true
end
| uu____15782 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd1)
in (

let uu____15786 = (FStar_Util.set_is_subset_of fvs_hd fvs1)
in (match (uu____15786) with
| true -> begin
true
end
| uu____15787 -> begin
((

let uu____15789 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____15789) with
| true -> begin
(

let uu____15790 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s\n" uu____15790))
end
| uu____15791 -> begin
()
end));
false;
)
end)))
end)
end)))
in (match (maybe_pat_vars) with
| FStar_Pervasives_Native.Some (vars) -> begin
(

let t11 = (sn env t1)
in (

let t21 = (sn env t2)
in (

let lhs1 = ((t11), (uv), (k_uv), (args_lhs))
in (

let fvs1 = (FStar_Syntax_Free.names t11)
in (

let fvs2 = (FStar_Syntax_Free.names t21)
in (

let uu____15810 = (occurs_check env wl1 ((uv), (k_uv)) t21)
in (match (uu____15810) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____15823 = (

let uu____15824 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____15824))
in (giveup_or_defer1 orig uu____15823))
end
| uu____15825 -> begin
(

let uu____15826 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____15826) with
| true -> begin
(

let uu____15827 = (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t21)) && (Prims.op_disEquality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____15827) with
| true -> begin
(

let uu____15828 = (subterms args_lhs)
in (imitate' orig env wl1 uu____15828))
end
| uu____15831 -> begin
((

let uu____15833 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____15833) with
| true -> begin
(

let uu____15834 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____15835 = (names_to_string fvs1)
in (

let uu____15836 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" uu____15834 uu____15835 uu____15836))))
end
| uu____15837 -> begin
()
end));
(use_pattern_equality orig env wl1 lhs1 vars t21);
)
end))
end
| uu____15838 -> begin
(match ((((not (patterns_only)) && wl1.defer_ok) && (Prims.op_disEquality (p_rel orig) FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl1))
end
| uu____15839 -> begin
(

let uu____15840 = ((not (patterns_only)) && (check_head fvs1 t21))
in (match (uu____15840) with
| true -> begin
((

let uu____15842 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____15842) with
| true -> begin
(

let uu____15843 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____15844 = (names_to_string fvs1)
in (

let uu____15845 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n" uu____15843 uu____15844 uu____15845))))
end
| uu____15846 -> begin
()
end));
(

let uu____15847 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) lhs1 t21 uu____15847));
)
end
| uu____15856 -> begin
(giveup env "free-variable check failed on a non-redex" orig)
end))
end)
end))
end)
end)))))))
end
| FStar_Pervasives_Native.None when patterns_only -> begin
(giveup env "not a pattern" orig)
end
| FStar_Pervasives_Native.None -> begin
(match (wl1.defer_ok) with
| true -> begin
(solve env (defer "not a pattern" orig wl1))
end
| uu____15857 -> begin
(

let uu____15858 = (

let uu____15859 = (FStar_Syntax_Free.names t1)
in (check_head uu____15859 t2))
in (match (uu____15858) with
| true -> begin
(

let n_args_lhs = (FStar_List.length args_lhs)
in ((

let uu____15870 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____15870) with
| true -> begin
(

let uu____15871 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____15872 = (FStar_Util.string_of_int n_args_lhs)
in (FStar_Util.print2 "Not a pattern (%s) ... (lhs has %s args)\n" uu____15871 uu____15872)))
end
| uu____15879 -> begin
()
end));
(

let uu____15880 = (subterms args_lhs)
in (pattern_eq_imitate_or_project n_args_lhs (FStar_Pervasives_Native.fst lhs) t2 uu____15880));
))
end
| uu____15891 -> begin
(giveup env "head-symbol is free" orig)
end))
end)
end)))))
end)))
in (

let flex_flex1 = (fun orig lhs rhs -> (match ((wl.defer_ok && (Prims.op_disEquality (p_rel orig) FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex-flex deferred" orig wl))
end
| uu____15902 -> begin
(

let solve_both_pats = (fun wl1 uu____15957 uu____15958 r -> (match (((uu____15957), (uu____15958))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
(

let uu____16156 = ((FStar_Syntax_Unionfind.equiv u1 u2) && (binders_eq xs ys))
in (match (uu____16156) with
| true -> begin
(

let uu____16157 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____16157))
end
| uu____16158 -> begin
(

let xs1 = (sn_binders env xs)
in (

let ys1 = (sn_binders env ys)
in (

let zs = (intersect_vars xs1 ys1)
in ((

let uu____16181 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____16181) with
| true -> begin
(

let uu____16182 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____16183 = (FStar_Syntax_Print.binders_to_string ", " ys1)
in (

let uu____16184 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (

let uu____16185 = (FStar_Syntax_Print.term_to_string k1)
in (

let uu____16186 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" uu____16182 uu____16183 uu____16184 uu____16185 uu____16186))))))
end
| uu____16187 -> begin
()
end));
(

let subst_k = (fun k xs2 args -> (

let xs_len = (FStar_List.length xs2)
in (

let args_len = (FStar_List.length args)
in (match ((Prims.op_Equality xs_len args_len)) with
| true -> begin
(

let uu____16246 = (FStar_Syntax_Util.subst_of_list xs2 args)
in (FStar_Syntax_Subst.subst uu____16246 k))
end
| uu____16249 -> begin
(match ((args_len < xs_len)) with
| true -> begin
(

let uu____16260 = (FStar_Util.first_N args_len xs2)
in (match (uu____16260) with
| (xs3, xs_rest) -> begin
(

let k3 = (

let uu____16314 = (FStar_Syntax_Syntax.mk_GTotal k)
in (FStar_Syntax_Util.arrow xs_rest uu____16314))
in (

let uu____16317 = (FStar_Syntax_Util.subst_of_list xs3 args)
in (FStar_Syntax_Subst.subst uu____16317 k3)))
end))
end
| uu____16320 -> begin
(

let uu____16321 = (

let uu____16322 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____16323 = (FStar_Syntax_Print.binders_to_string ", " xs2)
in (

let uu____16324 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" uu____16322 uu____16323 uu____16324))))
in (failwith uu____16321))
end)
end))))
in (

let uu____16325 = (

let uu____16332 = (

let uu____16345 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals uu____16345))
in (match (uu____16332) with
| (bs, k1') -> begin
(

let uu____16370 = (

let uu____16383 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals uu____16383))
in (match (uu____16370) with
| (cs, k2') -> begin
(

let k1'_xs = (subst_k k1' bs args1)
in (

let k2'_ys = (subst_k k2' cs args2)
in (

let sub_prob = (

let uu____16411 = (

let uu____16416 = (p_scope orig)
in (mk_problem uu____16416 orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys FStar_Pervasives_Native.None "flex-flex kinding"))
in (FStar_All.pipe_left (fun _0_63 -> FStar_TypeChecker_Common.TProb (_0_63)) uu____16411))
in (

let uu____16421 = (

let uu____16426 = (

let uu____16427 = (FStar_Syntax_Subst.compress k1')
in uu____16427.FStar_Syntax_Syntax.n)
in (

let uu____16430 = (

let uu____16431 = (FStar_Syntax_Subst.compress k2')
in uu____16431.FStar_Syntax_Syntax.n)
in ((uu____16426), (uu____16430))))
in (match (uu____16421) with
| (FStar_Syntax_Syntax.Tm_type (uu____16440), uu____16441) -> begin
((k1'_xs), ((sub_prob)::[]))
end
| (uu____16444, FStar_Syntax_Syntax.Tm_type (uu____16445)) -> begin
((k2'_ys), ((sub_prob)::[]))
end
| uu____16448 -> begin
(

let uu____16453 = (FStar_Syntax_Util.type_u ())
in (match (uu____16453) with
| (t, uu____16465) -> begin
(

let uu____16466 = (new_uvar r zs t)
in (match (uu____16466) with
| (k_zs, uu____16478) -> begin
(

let kprob = (

let uu____16480 = (

let uu____16485 = (p_scope orig)
in (mk_problem uu____16485 orig k1'_xs FStar_TypeChecker_Common.EQ k_zs FStar_Pervasives_Native.None "flex-flex kinding"))
in (FStar_All.pipe_left (fun _0_64 -> FStar_TypeChecker_Common.TProb (_0_64)) uu____16480))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end)))))
end))
end))
in (match (uu____16325) with
| (k_u', sub_probs) -> begin
(

let uu____16498 = (

let uu____16509 = (

let uu____16510 = (new_uvar r zs k_u')
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____16510))
in (

let uu____16519 = (

let uu____16522 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs1 uu____16522))
in (

let uu____16525 = (

let uu____16528 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys1 uu____16528))
in ((uu____16509), (uu____16519), (uu____16525)))))
in (match (uu____16498) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs1 u_zs)
in (

let uu____16547 = (occurs_check env wl1 ((u1), (k1)) sub1)
in (match (uu____16547) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occcurs check")
end
| uu____16560 -> begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in (

let uu____16566 = (FStar_Syntax_Unionfind.equiv u1 u2)
in (match (uu____16566) with
| true -> begin
(

let wl2 = (solve_prob orig FStar_Pervasives_Native.None ((sol1)::[]) wl1)
in (solve env wl2))
end
| uu____16568 -> begin
(

let sub2 = (u_abs knew2 ys1 u_zs)
in (

let uu____16570 = (occurs_check env wl1 ((u2), (k2)) sub2)
in (match (uu____16570) with
| (occurs_ok1, msg1) -> begin
(match ((not (occurs_ok1))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occurs check")
end
| uu____16583 -> begin
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

let solve_one_pat = (fun uu____16623 uu____16624 -> (match (((uu____16623), (uu____16624))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
((

let uu____16742 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____16742) with
| true -> begin
(

let uu____16743 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____16744 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" uu____16743 uu____16744)))
end
| uu____16745 -> begin
()
end));
(

let uu____16746 = (FStar_Syntax_Unionfind.equiv u1 u2)
in (match (uu____16746) with
| true -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____16765 uu____16766 -> (match (((uu____16765), (uu____16766))) with
| ((a, uu____16784), (t21, uu____16786)) -> begin
(

let uu____16795 = (

let uu____16800 = (p_scope orig)
in (

let uu____16801 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem uu____16800 orig uu____16801 FStar_TypeChecker_Common.EQ t21 FStar_Pervasives_Native.None "flex-flex index")))
in (FStar_All.pipe_right uu____16795 (fun _0_65 -> FStar_TypeChecker_Common.TProb (_0_65))))
end)) xs args2)
in (

let guard = (

let uu____16807 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) FStar_Pervasives_Native.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____16807))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))))
end
| uu____16817 -> begin
(

let t21 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t21)
in (

let uu____16822 = (occurs_check env wl ((u1), (k1)) t21)
in (match (uu____16822) with
| (occurs_ok, uu____16830) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in (

let uu____16838 = (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars))
in (match (uu____16838) with
| true -> begin
(

let sol = (

let uu____16840 = (

let uu____16849 = (u_abs k1 xs t21)
in ((((u1), (k1))), (uu____16849)))
in TERM (uu____16840))
in (

let wl1 = (solve_prob orig FStar_Pervasives_Native.None ((sol)::[]) wl)
in (solve env wl1)))
end
| uu____16855 -> begin
(

let uu____16856 = (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok))
in (match (uu____16856) with
| true -> begin
(

let uu____16857 = (force_quasi_pattern (FStar_Pervasives_Native.Some (xs)) ((t21), (u2), (k2), (args2)))
in (match (uu____16857) with
| FStar_Pervasives_Native.None -> begin
(giveup_or_defer1 orig "flex-flex constraint")
end
| FStar_Pervasives_Native.Some (sol, (uu____16881, u21, k21, ys)) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____16907 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____16907) with
| true -> begin
(

let uu____16908 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" uu____16908))
end
| uu____16909 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____16915 -> begin
(giveup env "impossible" orig)
end);
))
end))
end
| uu____16916 -> begin
(giveup_or_defer1 orig "flex-flex constraint")
end))
end)))
end))))
end));
)
end))
in (

let uu____16917 = lhs
in (match (uu____16917) with
| (t1, u1, k1, args1) -> begin
(

let uu____16922 = rhs
in (match (uu____16922) with
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
| uu____16962 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: neither side is a pattern")
end
| uu____16971 -> begin
(

let uu____16972 = (force_quasi_pattern FStar_Pervasives_Native.None ((t1), (u1), (k1), (args1)))
in (match (uu____16972) with
| FStar_Pervasives_Native.None -> begin
(giveup env "flex-flex: neither side is a pattern, nor is coercible to a pattern" orig)
end
| FStar_Pervasives_Native.Some (sol, uu____16990) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____16997 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____16997) with
| true -> begin
(

let uu____16998 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" uu____16998))
end
| uu____16999 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____17005 -> begin
(giveup env "impossible" orig)
end);
))
end))
end)
end))))
end))
end))))
end))
in (

let orig = FStar_TypeChecker_Common.TProb (problem)
in ((def_check_prob "solve_t\'.2" orig);
(

let uu____17008 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____17008) with
| true -> begin
(

let uu____17009 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____17009))
end
| uu____17010 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in (

let uu____17013 = (FStar_Util.physical_equality t1 t2)
in (match (uu____17013) with
| true -> begin
(

let uu____17014 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____17014))
end
| uu____17015 -> begin
((

let uu____17017 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____17017) with
| true -> begin
(

let uu____17018 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____17019 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____17020 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print3 "Attempting %s (%s - %s)\n" uu____17018 uu____17019 uu____17020))))
end
| uu____17021 -> begin
()
end));
(

let r = (FStar_TypeChecker_Env.get_range env)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_delayed (uu____17023), uu____17024) -> begin
(failwith "Impossible: terms were not compressed")
end
| (uu____17049, FStar_Syntax_Syntax.Tm_delayed (uu____17050)) -> begin
(failwith "Impossible: terms were not compressed")
end
| (FStar_Syntax_Syntax.Tm_ascribed (uu____17075), uu____17076) -> begin
(

let uu____17103 = (

let uu___151_17104 = problem
in (

let uu____17105 = (FStar_Syntax_Util.unascribe t1)
in {FStar_TypeChecker_Common.pid = uu___151_17104.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____17105; FStar_TypeChecker_Common.relation = uu___151_17104.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___151_17104.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___151_17104.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___151_17104.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___151_17104.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___151_17104.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___151_17104.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___151_17104.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____17103 wl))
end
| (FStar_Syntax_Syntax.Tm_meta (uu____17106), uu____17107) -> begin
(

let uu____17114 = (

let uu___152_17115 = problem
in (

let uu____17116 = (FStar_Syntax_Util.unmeta t1)
in {FStar_TypeChecker_Common.pid = uu___152_17115.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____17116; FStar_TypeChecker_Common.relation = uu___152_17115.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___152_17115.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___152_17115.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___152_17115.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___152_17115.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___152_17115.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___152_17115.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___152_17115.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____17114 wl))
end
| (uu____17117, FStar_Syntax_Syntax.Tm_ascribed (uu____17118)) -> begin
(

let uu____17145 = (

let uu___153_17146 = problem
in (

let uu____17147 = (FStar_Syntax_Util.unascribe t2)
in {FStar_TypeChecker_Common.pid = uu___153_17146.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___153_17146.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___153_17146.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____17147; FStar_TypeChecker_Common.element = uu___153_17146.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___153_17146.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___153_17146.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___153_17146.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___153_17146.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___153_17146.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____17145 wl))
end
| (uu____17148, FStar_Syntax_Syntax.Tm_meta (uu____17149)) -> begin
(

let uu____17156 = (

let uu___154_17157 = problem
in (

let uu____17158 = (FStar_Syntax_Util.unmeta t2)
in {FStar_TypeChecker_Common.pid = uu___154_17157.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___154_17157.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___154_17157.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____17158; FStar_TypeChecker_Common.element = uu___154_17157.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___154_17157.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___154_17157.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___154_17157.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___154_17157.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___154_17157.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____17156 wl))
end
| (FStar_Syntax_Syntax.Tm_quoted (t11, uu____17160), FStar_Syntax_Syntax.Tm_quoted (t21, uu____17162)) -> begin
(

let uu____17171 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____17171))
end
| (FStar_Syntax_Syntax.Tm_bvar (uu____17172), uu____17173) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (uu____17174, FStar_Syntax_Syntax.Tm_bvar (uu____17175)) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (FStar_Syntax_Syntax.Tm_type (u1), FStar_Syntax_Syntax.Tm_type (u2)) -> begin
(solve_one_universe_eq env orig u1 u2 wl)
end
| (FStar_Syntax_Syntax.Tm_arrow (bs1, c1), FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) -> begin
(

let mk_c = (fun c uu___115_17230 -> (match (uu___115_17230) with
| [] -> begin
c
end
| bs -> begin
(

let uu____17252 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____17252))
end))
in (

let uu____17261 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____17261) with
| ((bs11, c11), (bs21, c21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let c12 = (FStar_Syntax_Subst.subst_comp subst1 c11)
in (

let c22 = (FStar_Syntax_Subst.subst_comp subst1 c21)
in (

let rel = (

let uu____17403 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____17403) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____17404 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (

let uu____17405 = (mk_problem scope orig c12 rel c22 FStar_Pervasives_Native.None "function co-domain")
in (FStar_All.pipe_left (fun _0_66 -> FStar_TypeChecker_Common.CProb (_0_66)) uu____17405)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___116_17481 -> (match (uu___116_17481) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____17515 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____17515) with
| ((bs11, tbody11), (bs21, tbody21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let uu____17651 = (

let uu____17656 = (FStar_Syntax_Subst.subst subst1 tbody11)
in (

let uu____17657 = (FStar_Syntax_Subst.subst subst1 tbody21)
in (mk_problem scope orig uu____17656 problem.FStar_TypeChecker_Common.relation uu____17657 FStar_Pervasives_Native.None "lambda co-domain")))
in (FStar_All.pipe_left (fun _0_67 -> FStar_TypeChecker_Common.TProb (_0_67)) uu____17651))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (uu____17662), uu____17663) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____17688) -> begin
true
end
| uu____17705 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____17728 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____17736 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let force_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
t
end
| uu____17751 -> begin
(

let uu____17752 = (env.FStar_TypeChecker_Env.type_of (

let uu___155_17760 = env
in {FStar_TypeChecker_Env.solver = uu___155_17760.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___155_17760.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___155_17760.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___155_17760.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___155_17760.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___155_17760.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___155_17760.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___155_17760.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___155_17760.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___155_17760.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___155_17760.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___155_17760.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___155_17760.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___155_17760.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___155_17760.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___155_17760.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___155_17760.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___155_17760.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___155_17760.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___155_17760.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___155_17760.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___155_17760.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___155_17760.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___155_17760.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___155_17760.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___155_17760.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___155_17760.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___155_17760.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___155_17760.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___155_17760.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___155_17760.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___155_17760.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___155_17760.FStar_TypeChecker_Env.dep_graph}) t)
in (match (uu____17752) with
| (uu____17763, ty, uu____17765) -> begin
(

let uu____17766 = (FStar_TypeChecker_Normalize.unfold_whnf env ty)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env t uu____17766))
end))
end))
in (

let uu____17767 = (

let uu____17784 = (maybe_eta t1)
in (

let uu____17791 = (maybe_eta t2)
in ((uu____17784), (uu____17791))))
in (match (uu____17767) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___156_17833 = problem
in {FStar_TypeChecker_Common.pid = uu___156_17833.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___156_17833.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___156_17833.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___156_17833.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___156_17833.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___156_17833.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___156_17833.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___156_17833.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____17856 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____17856) with
| true -> begin
(

let uu____17857 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____17857 t_abs wl))
end
| uu____17864 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___157_17872 = problem
in {FStar_TypeChecker_Common.pid = uu___157_17872.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___157_17872.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___157_17872.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___157_17872.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___157_17872.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___157_17872.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___157_17872.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___157_17872.FStar_TypeChecker_Common.rank}) wl)
end
| uu____17875 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____17896 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____17896) with
| true -> begin
(

let uu____17897 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____17897 t_abs wl))
end
| uu____17904 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___157_17912 = problem
in {FStar_TypeChecker_Common.pid = uu___157_17912.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___157_17912.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___157_17912.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___157_17912.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___157_17912.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___157_17912.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___157_17912.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___157_17912.FStar_TypeChecker_Common.rank}) wl)
end
| uu____17915 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| uu____17916 -> begin
(failwith "Impossible: at least one side is an abstraction")
end)))))
end
| (uu____17933, FStar_Syntax_Syntax.Tm_abs (uu____17934)) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____17959) -> begin
true
end
| uu____17976 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____17999 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____18007 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let force_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
t
end
| uu____18022 -> begin
(

let uu____18023 = (env.FStar_TypeChecker_Env.type_of (

let uu___155_18031 = env
in {FStar_TypeChecker_Env.solver = uu___155_18031.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___155_18031.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___155_18031.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___155_18031.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___155_18031.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___155_18031.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___155_18031.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___155_18031.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___155_18031.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___155_18031.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___155_18031.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___155_18031.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___155_18031.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___155_18031.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___155_18031.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___155_18031.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___155_18031.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___155_18031.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___155_18031.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___155_18031.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___155_18031.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___155_18031.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___155_18031.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___155_18031.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___155_18031.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___155_18031.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___155_18031.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___155_18031.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___155_18031.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___155_18031.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___155_18031.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___155_18031.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___155_18031.FStar_TypeChecker_Env.dep_graph}) t)
in (match (uu____18023) with
| (uu____18034, ty, uu____18036) -> begin
(

let uu____18037 = (FStar_TypeChecker_Normalize.unfold_whnf env ty)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env t uu____18037))
end))
end))
in (

let uu____18038 = (

let uu____18055 = (maybe_eta t1)
in (

let uu____18062 = (maybe_eta t2)
in ((uu____18055), (uu____18062))))
in (match (uu____18038) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___156_18104 = problem
in {FStar_TypeChecker_Common.pid = uu___156_18104.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___156_18104.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___156_18104.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___156_18104.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___156_18104.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___156_18104.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___156_18104.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___156_18104.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____18127 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____18127) with
| true -> begin
(

let uu____18128 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____18128 t_abs wl))
end
| uu____18135 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___157_18143 = problem
in {FStar_TypeChecker_Common.pid = uu___157_18143.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___157_18143.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___157_18143.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___157_18143.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___157_18143.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___157_18143.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___157_18143.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___157_18143.FStar_TypeChecker_Common.rank}) wl)
end
| uu____18146 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____18167 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____18167) with
| true -> begin
(

let uu____18168 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____18168 t_abs wl))
end
| uu____18175 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___157_18183 = problem
in {FStar_TypeChecker_Common.pid = uu___157_18183.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___157_18183.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___157_18183.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___157_18183.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___157_18183.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___157_18183.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___157_18183.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___157_18183.FStar_TypeChecker_Common.rank}) wl)
end
| uu____18186 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| uu____18187 -> begin
(failwith "Impossible: at least one side is an abstraction")
end)))))
end
| (FStar_Syntax_Syntax.Tm_refine (x1, ph1), FStar_Syntax_Syntax.Tm_refine (x2, phi2)) -> begin
(

let should_delta = (((

let uu____18219 = (FStar_Syntax_Free.uvars t1)
in (FStar_Util.set_is_empty uu____18219)) && (

let uu____18231 = (FStar_Syntax_Free.uvars t2)
in (FStar_Util.set_is_empty uu____18231))) && (

let uu____18246 = (head_matches env x1.FStar_Syntax_Syntax.sort x2.FStar_Syntax_Syntax.sort)
in (match (uu____18246) with
| MisMatch (FStar_Pervasives_Native.Some (d1), FStar_Pervasives_Native.Some (d2)) -> begin
(

let is_unfoldable = (fun uu___117_18256 -> (match (uu___117_18256) with
| FStar_Syntax_Syntax.Delta_constant -> begin
true
end
| FStar_Syntax_Syntax.Delta_defined_at_level (uu____18257) -> begin
true
end
| uu____18258 -> begin
false
end))
in ((is_unfoldable d1) && (is_unfoldable d2)))
end
| uu____18259 -> begin
false
end)))
in (

let uu____18260 = (as_refinement should_delta env wl t1)
in (match (uu____18260) with
| (x11, phi1) -> begin
(

let uu____18267 = (as_refinement should_delta env wl t2)
in (match (uu____18267) with
| (x21, phi21) -> begin
(

let base_prob = (

let uu____18275 = (

let uu____18280 = (p_scope orig)
in (mk_problem uu____18280 orig x11.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x21.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type"))
in (FStar_All.pipe_left (fun _0_68 -> FStar_TypeChecker_Common.TProb (_0_68)) uu____18275))
in (

let x12 = (FStar_Syntax_Syntax.freshen_bv x11)
in (

let subst1 = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x12))))::[]
in (

let phi11 = (FStar_Syntax_Subst.subst subst1 phi1)
in (

let phi22 = (FStar_Syntax_Subst.subst subst1 phi21)
in (

let env1 = (FStar_TypeChecker_Env.push_bv env x12)
in (

let mk_imp1 = (fun imp phi12 phi23 -> (

let uu____18314 = (imp phi12 phi23)
in (FStar_All.pipe_right uu____18314 (guard_on_element wl problem x12))))
in (

let fallback = (fun uu____18318 -> (

let impl = (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp1 FStar_Syntax_Util.mk_iff phi11 phi22)
end
| uu____18320 -> begin
(mk_imp1 FStar_Syntax_Util.mk_imp phi11 phi22)
end)
in (

let guard = (

let uu____18324 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____18324 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env1 (attempt ((base_prob)::[]) wl1))))))
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let ref_prob = (

let uu____18333 = (

let uu____18338 = (

let uu____18339 = (p_scope orig)
in (

let uu____18346 = (

let uu____18353 = (FStar_Syntax_Syntax.mk_binder x12)
in (uu____18353)::[])
in (FStar_List.append uu____18339 uu____18346)))
in (mk_problem uu____18338 orig phi11 FStar_TypeChecker_Common.EQ phi22 FStar_Pervasives_Native.None "refinement formula"))
in (FStar_All.pipe_left (fun _0_69 -> FStar_TypeChecker_Common.TProb (_0_69)) uu____18333))
in (

let uu____18362 = (solve env1 (

let uu___158_18364 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___158_18364.ctr; defer_ok = false; smt_ok = uu___158_18364.smt_ok; tcenv = uu___158_18364.tcenv}))
in (match (uu____18362) with
| Failed (uu____18371) -> begin
(fallback ())
end
| Success (uu____18376) -> begin
(

let guard = (

let uu____18380 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (

let uu____18385 = (

let uu____18386 = (FStar_All.pipe_right (p_guard ref_prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____18386 (guard_on_element wl problem x12)))
in (FStar_Syntax_Util.mk_conj uu____18380 uu____18385)))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (

let wl2 = (

let uu___159_18395 = wl1
in {attempting = uu___159_18395.attempting; wl_deferred = uu___159_18395.wl_deferred; ctr = (wl1.ctr + (Prims.parse_int "1")); defer_ok = uu___159_18395.defer_ok; smt_ok = uu___159_18395.smt_ok; tcenv = uu___159_18395.tcenv})
in (solve env1 (attempt ((base_prob)::[]) wl2)))))
end)))
end
| uu____18396 -> begin
(fallback ())
end)))))))))
end))
end)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____18397), FStar_Syntax_Syntax.Tm_uvar (uu____18398)) -> begin
(

let uu____18431 = (destruct_flex_t t1)
in (

let uu____18432 = (destruct_flex_t t2)
in (flex_flex1 orig uu____18431 uu____18432)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____18433); FStar_Syntax_Syntax.pos = uu____18434; FStar_Syntax_Syntax.vars = uu____18435}, uu____18436), FStar_Syntax_Syntax.Tm_uvar (uu____18437)) -> begin
(

let uu____18490 = (destruct_flex_t t1)
in (

let uu____18491 = (destruct_flex_t t2)
in (flex_flex1 orig uu____18490 uu____18491)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____18492), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____18493); FStar_Syntax_Syntax.pos = uu____18494; FStar_Syntax_Syntax.vars = uu____18495}, uu____18496)) -> begin
(

let uu____18549 = (destruct_flex_t t1)
in (

let uu____18550 = (destruct_flex_t t2)
in (flex_flex1 orig uu____18549 uu____18550)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____18551); FStar_Syntax_Syntax.pos = uu____18552; FStar_Syntax_Syntax.vars = uu____18553}, uu____18554), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____18555); FStar_Syntax_Syntax.pos = uu____18556; FStar_Syntax_Syntax.vars = uu____18557}, uu____18558)) -> begin
(

let uu____18631 = (destruct_flex_t t1)
in (

let uu____18632 = (destruct_flex_t t2)
in (flex_flex1 orig uu____18631 uu____18632)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____18633), uu____18634) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(

let uu____18651 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____18651 t2 wl))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____18658); FStar_Syntax_Syntax.pos = uu____18659; FStar_Syntax_Syntax.vars = uu____18660}, uu____18661), uu____18662) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(

let uu____18699 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____18699 t2 wl))
end
| (uu____18706, FStar_Syntax_Syntax.Tm_uvar (uu____18707)) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (uu____18724, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____18725); FStar_Syntax_Syntax.pos = uu____18726; FStar_Syntax_Syntax.vars = uu____18727}, uu____18728)) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____18765), FStar_Syntax_Syntax.Tm_type (uu____18766)) -> begin
(solve_t' env (

let uu___160_18784 = problem
in {FStar_TypeChecker_Common.pid = uu___160_18784.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___160_18784.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___160_18784.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___160_18784.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___160_18784.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___160_18784.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___160_18784.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___160_18784.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___160_18784.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____18785); FStar_Syntax_Syntax.pos = uu____18786; FStar_Syntax_Syntax.vars = uu____18787}, uu____18788), FStar_Syntax_Syntax.Tm_type (uu____18789)) -> begin
(solve_t' env (

let uu___160_18827 = problem
in {FStar_TypeChecker_Common.pid = uu___160_18827.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___160_18827.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___160_18827.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___160_18827.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___160_18827.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___160_18827.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___160_18827.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___160_18827.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___160_18827.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____18828), FStar_Syntax_Syntax.Tm_arrow (uu____18829)) -> begin
(solve_t' env (

let uu___160_18859 = problem
in {FStar_TypeChecker_Common.pid = uu___160_18859.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___160_18859.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___160_18859.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___160_18859.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___160_18859.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___160_18859.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___160_18859.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___160_18859.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___160_18859.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____18860); FStar_Syntax_Syntax.pos = uu____18861; FStar_Syntax_Syntax.vars = uu____18862}, uu____18863), FStar_Syntax_Syntax.Tm_arrow (uu____18864)) -> begin
(solve_t' env (

let uu___160_18914 = problem
in {FStar_TypeChecker_Common.pid = uu___160_18914.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___160_18914.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___160_18914.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___160_18914.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___160_18914.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___160_18914.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___160_18914.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___160_18914.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___160_18914.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____18915), uu____18916) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____18933 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____18935 = (

let uu____18936 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____18936))
in (match (uu____18935) with
| true -> begin
(

let uu____18937 = (FStar_All.pipe_left (fun _0_70 -> FStar_TypeChecker_Common.TProb (_0_70)) (

let uu___161_18943 = problem
in {FStar_TypeChecker_Common.pid = uu___161_18943.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___161_18943.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___161_18943.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___161_18943.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___161_18943.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___161_18943.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___161_18943.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___161_18943.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___161_18943.FStar_TypeChecker_Common.rank}))
in (

let uu____18944 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____18937 uu____18944 t2 wl)))
end
| uu____18951 -> begin
(

let uu____18952 = (base_and_refinement env t2)
in (match (uu____18952) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18981 = (FStar_All.pipe_left (fun _0_71 -> FStar_TypeChecker_Common.TProb (_0_71)) (

let uu___162_18987 = problem
in {FStar_TypeChecker_Common.pid = uu___162_18987.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___162_18987.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___162_18987.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___162_18987.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_18987.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_18987.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_18987.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_18987.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_18987.FStar_TypeChecker_Common.rank}))
in (

let uu____18988 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____18981 uu____18988 t_base wl)))
end
| FStar_Pervasives_Native.Some (y, phi) -> begin
(

let y' = (

let uu___163_19002 = y
in {FStar_Syntax_Syntax.ppname = uu___163_19002.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___163_19002.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let base_prob = (

let uu____19005 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_72 -> FStar_TypeChecker_Common.TProb (_0_72)) uu____19005))
in (

let guard = (

let uu____19017 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____19017 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl1)))))))
end)
end))
end)))
end)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19025); FStar_Syntax_Syntax.pos = uu____19026; FStar_Syntax_Syntax.vars = uu____19027}, uu____19028), uu____19029) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____19066 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____19068 = (

let uu____19069 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____19069))
in (match (uu____19068) with
| true -> begin
(

let uu____19070 = (FStar_All.pipe_left (fun _0_73 -> FStar_TypeChecker_Common.TProb (_0_73)) (

let uu___161_19076 = problem
in {FStar_TypeChecker_Common.pid = uu___161_19076.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___161_19076.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___161_19076.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___161_19076.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___161_19076.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___161_19076.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___161_19076.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___161_19076.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___161_19076.FStar_TypeChecker_Common.rank}))
in (

let uu____19077 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____19070 uu____19077 t2 wl)))
end
| uu____19084 -> begin
(

let uu____19085 = (base_and_refinement env t2)
in (match (uu____19085) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____19114 = (FStar_All.pipe_left (fun _0_74 -> FStar_TypeChecker_Common.TProb (_0_74)) (

let uu___162_19120 = problem
in {FStar_TypeChecker_Common.pid = uu___162_19120.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___162_19120.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___162_19120.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___162_19120.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_19120.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_19120.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_19120.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_19120.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_19120.FStar_TypeChecker_Common.rank}))
in (

let uu____19121 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____19114 uu____19121 t_base wl)))
end
| FStar_Pervasives_Native.Some (y, phi) -> begin
(

let y' = (

let uu___163_19135 = y
in {FStar_Syntax_Syntax.ppname = uu___163_19135.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___163_19135.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let base_prob = (

let uu____19138 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_75 -> FStar_TypeChecker_Common.TProb (_0_75)) uu____19138))
in (

let guard = (

let uu____19150 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____19150 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl1)))))))
end)
end))
end)))
end)
end
| (uu____19158, FStar_Syntax_Syntax.Tm_uvar (uu____19159)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| uu____19176 -> begin
(

let uu____19177 = (base_and_refinement env t1)
in (match (uu____19177) with
| (t_base, uu____19189) -> begin
(solve_t env (

let uu___164_19203 = problem
in {FStar_TypeChecker_Common.pid = uu___164_19203.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___164_19203.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___164_19203.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_19203.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_19203.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_19203.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_19203.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_19203.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (uu____19204, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19205); FStar_Syntax_Syntax.pos = uu____19206; FStar_Syntax_Syntax.vars = uu____19207}, uu____19208)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| uu____19245 -> begin
(

let uu____19246 = (base_and_refinement env t1)
in (match (uu____19246) with
| (t_base, uu____19258) -> begin
(solve_t env (

let uu___164_19272 = problem
in {FStar_TypeChecker_Common.pid = uu___164_19272.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___164_19272.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___164_19272.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_19272.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_19272.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_19272.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_19272.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_19272.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (FStar_Syntax_Syntax.Tm_refine (uu____19273), uu____19274) -> begin
(

let t21 = (

let uu____19284 = (base_and_refinement env t2)
in (FStar_All.pipe_left force_refinement uu____19284))
in (solve_t env (

let uu___165_19308 = problem
in {FStar_TypeChecker_Common.pid = uu___165_19308.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___165_19308.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___165_19308.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___165_19308.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___165_19308.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___165_19308.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___165_19308.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___165_19308.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___165_19308.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____19309, FStar_Syntax_Syntax.Tm_refine (uu____19310)) -> begin
(

let t11 = (

let uu____19320 = (base_and_refinement env t1)
in (FStar_All.pipe_left force_refinement uu____19320))
in (solve_t env (

let uu___166_19344 = problem
in {FStar_TypeChecker_Common.pid = uu___166_19344.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___166_19344.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___166_19344.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___166_19344.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_19344.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___166_19344.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___166_19344.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_19344.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_19344.FStar_TypeChecker_Common.rank}) wl))
end
| (FStar_Syntax_Syntax.Tm_match (uu____19347), uu____19348) -> begin
(

let head1 = (

let uu____19374 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____19374 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____19418 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____19418 FStar_Pervasives_Native.fst))
in ((

let uu____19460 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____19460) with
| true -> begin
(

let uu____19461 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____19462 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____19463 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____19461 uu____19462 uu____19463))))
end
| uu____19464 -> begin
()
end));
(

let uu____19465 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____19465) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____19480 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____19480) with
| true -> begin
(

let guard = (

let uu____19492 = (

let uu____19493 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____19493 FStar_Syntax_Util.Equal))
in (match (uu____19492) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____19496 -> begin
(

let uu____19497 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_76 -> FStar_Pervasives_Native.Some (_0_76)) uu____19497))
end))
in (

let uu____19500 = (solve_prob orig guard [] wl)
in (solve env uu____19500)))
end
| uu____19501 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____19502 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____19503), uu____19504) -> begin
(

let head1 = (

let uu____19514 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____19514 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____19558 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____19558 FStar_Pervasives_Native.fst))
in ((

let uu____19600 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____19600) with
| true -> begin
(

let uu____19601 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____19602 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____19603 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____19601 uu____19602 uu____19603))))
end
| uu____19604 -> begin
()
end));
(

let uu____19605 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____19605) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____19620 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____19620) with
| true -> begin
(

let guard = (

let uu____19632 = (

let uu____19633 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____19633 FStar_Syntax_Util.Equal))
in (match (uu____19632) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____19636 -> begin
(

let uu____19637 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_77 -> FStar_Pervasives_Native.Some (_0_77)) uu____19637))
end))
in (

let uu____19640 = (solve_prob orig guard [] wl)
in (solve env uu____19640)))
end
| uu____19641 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____19642 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_name (uu____19643), uu____19644) -> begin
(

let head1 = (

let uu____19648 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____19648 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____19692 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____19692 FStar_Pervasives_Native.fst))
in ((

let uu____19734 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____19734) with
| true -> begin
(

let uu____19735 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____19736 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____19737 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____19735 uu____19736 uu____19737))))
end
| uu____19738 -> begin
()
end));
(

let uu____19739 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____19739) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____19754 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____19754) with
| true -> begin
(

let guard = (

let uu____19766 = (

let uu____19767 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____19767 FStar_Syntax_Util.Equal))
in (match (uu____19766) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____19770 -> begin
(

let uu____19771 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_78 -> FStar_Pervasives_Native.Some (_0_78)) uu____19771))
end))
in (

let uu____19774 = (solve_prob orig guard [] wl)
in (solve env uu____19774)))
end
| uu____19775 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____19776 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_constant (uu____19777), uu____19778) -> begin
(

let head1 = (

let uu____19782 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____19782 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____19826 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____19826 FStar_Pervasives_Native.fst))
in ((

let uu____19868 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____19868) with
| true -> begin
(

let uu____19869 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____19870 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____19871 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____19869 uu____19870 uu____19871))))
end
| uu____19872 -> begin
()
end));
(

let uu____19873 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____19873) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____19888 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____19888) with
| true -> begin
(

let guard = (

let uu____19900 = (

let uu____19901 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____19901 FStar_Syntax_Util.Equal))
in (match (uu____19900) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____19904 -> begin
(

let uu____19905 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_79 -> FStar_Pervasives_Native.Some (_0_79)) uu____19905))
end))
in (

let uu____19908 = (solve_prob orig guard [] wl)
in (solve env uu____19908)))
end
| uu____19909 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____19910 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____19911), uu____19912) -> begin
(

let head1 = (

let uu____19916 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____19916 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____19960 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____19960 FStar_Pervasives_Native.fst))
in ((

let uu____20002 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____20002) with
| true -> begin
(

let uu____20003 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____20004 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____20005 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____20003 uu____20004 uu____20005))))
end
| uu____20006 -> begin
()
end));
(

let uu____20007 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____20007) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____20022 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____20022) with
| true -> begin
(

let guard = (

let uu____20034 = (

let uu____20035 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____20035 FStar_Syntax_Util.Equal))
in (match (uu____20034) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____20038 -> begin
(

let uu____20039 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_80 -> FStar_Pervasives_Native.Some (_0_80)) uu____20039))
end))
in (

let uu____20042 = (solve_prob orig guard [] wl)
in (solve env uu____20042)))
end
| uu____20043 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____20044 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_app (uu____20045), uu____20046) -> begin
(

let head1 = (

let uu____20064 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____20064 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____20108 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____20108 FStar_Pervasives_Native.fst))
in ((

let uu____20150 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____20150) with
| true -> begin
(

let uu____20151 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____20152 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____20153 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____20151 uu____20152 uu____20153))))
end
| uu____20154 -> begin
()
end));
(

let uu____20155 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____20155) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____20170 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____20170) with
| true -> begin
(

let guard = (

let uu____20182 = (

let uu____20183 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____20183 FStar_Syntax_Util.Equal))
in (match (uu____20182) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____20186 -> begin
(

let uu____20187 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_81 -> FStar_Pervasives_Native.Some (_0_81)) uu____20187))
end))
in (

let uu____20190 = (solve_prob orig guard [] wl)
in (solve env uu____20190)))
end
| uu____20191 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____20192 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____20193, FStar_Syntax_Syntax.Tm_match (uu____20194)) -> begin
(

let head1 = (

let uu____20220 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____20220 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____20264 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____20264 FStar_Pervasives_Native.fst))
in ((

let uu____20306 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____20306) with
| true -> begin
(

let uu____20307 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____20308 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____20309 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____20307 uu____20308 uu____20309))))
end
| uu____20310 -> begin
()
end));
(

let uu____20311 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____20311) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____20326 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____20326) with
| true -> begin
(

let guard = (

let uu____20338 = (

let uu____20339 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____20339 FStar_Syntax_Util.Equal))
in (match (uu____20338) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____20342 -> begin
(

let uu____20343 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_82 -> FStar_Pervasives_Native.Some (_0_82)) uu____20343))
end))
in (

let uu____20346 = (solve_prob orig guard [] wl)
in (solve env uu____20346)))
end
| uu____20347 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____20348 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____20349, FStar_Syntax_Syntax.Tm_uinst (uu____20350)) -> begin
(

let head1 = (

let uu____20360 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____20360 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____20404 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____20404 FStar_Pervasives_Native.fst))
in ((

let uu____20446 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____20446) with
| true -> begin
(

let uu____20447 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____20448 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____20449 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____20447 uu____20448 uu____20449))))
end
| uu____20450 -> begin
()
end));
(

let uu____20451 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____20451) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____20466 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____20466) with
| true -> begin
(

let guard = (

let uu____20478 = (

let uu____20479 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____20479 FStar_Syntax_Util.Equal))
in (match (uu____20478) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____20482 -> begin
(

let uu____20483 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_83 -> FStar_Pervasives_Native.Some (_0_83)) uu____20483))
end))
in (

let uu____20486 = (solve_prob orig guard [] wl)
in (solve env uu____20486)))
end
| uu____20487 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____20488 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____20489, FStar_Syntax_Syntax.Tm_name (uu____20490)) -> begin
(

let head1 = (

let uu____20494 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____20494 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____20538 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____20538 FStar_Pervasives_Native.fst))
in ((

let uu____20580 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____20580) with
| true -> begin
(

let uu____20581 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____20582 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____20583 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____20581 uu____20582 uu____20583))))
end
| uu____20584 -> begin
()
end));
(

let uu____20585 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____20585) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____20600 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____20600) with
| true -> begin
(

let guard = (

let uu____20612 = (

let uu____20613 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____20613 FStar_Syntax_Util.Equal))
in (match (uu____20612) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____20616 -> begin
(

let uu____20617 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_84 -> FStar_Pervasives_Native.Some (_0_84)) uu____20617))
end))
in (

let uu____20620 = (solve_prob orig guard [] wl)
in (solve env uu____20620)))
end
| uu____20621 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____20622 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____20623, FStar_Syntax_Syntax.Tm_constant (uu____20624)) -> begin
(

let head1 = (

let uu____20628 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____20628 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____20672 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____20672 FStar_Pervasives_Native.fst))
in ((

let uu____20714 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____20714) with
| true -> begin
(

let uu____20715 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____20716 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____20717 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____20715 uu____20716 uu____20717))))
end
| uu____20718 -> begin
()
end));
(

let uu____20719 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____20719) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____20734 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____20734) with
| true -> begin
(

let guard = (

let uu____20746 = (

let uu____20747 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____20747 FStar_Syntax_Util.Equal))
in (match (uu____20746) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____20750 -> begin
(

let uu____20751 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_85 -> FStar_Pervasives_Native.Some (_0_85)) uu____20751))
end))
in (

let uu____20754 = (solve_prob orig guard [] wl)
in (solve env uu____20754)))
end
| uu____20755 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____20756 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____20757, FStar_Syntax_Syntax.Tm_fvar (uu____20758)) -> begin
(

let head1 = (

let uu____20762 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____20762 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____20806 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____20806 FStar_Pervasives_Native.fst))
in ((

let uu____20848 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____20848) with
| true -> begin
(

let uu____20849 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____20850 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____20851 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____20849 uu____20850 uu____20851))))
end
| uu____20852 -> begin
()
end));
(

let uu____20853 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____20853) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____20868 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____20868) with
| true -> begin
(

let guard = (

let uu____20880 = (

let uu____20881 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____20881 FStar_Syntax_Util.Equal))
in (match (uu____20880) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____20884 -> begin
(

let uu____20885 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_86 -> FStar_Pervasives_Native.Some (_0_86)) uu____20885))
end))
in (

let uu____20888 = (solve_prob orig guard [] wl)
in (solve env uu____20888)))
end
| uu____20889 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____20890 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____20891, FStar_Syntax_Syntax.Tm_app (uu____20892)) -> begin
(

let head1 = (

let uu____20910 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____20910 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____20954 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____20954 FStar_Pervasives_Native.fst))
in ((

let uu____20996 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____20996) with
| true -> begin
(

let uu____20997 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____20998 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____20999 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____20997 uu____20998 uu____20999))))
end
| uu____21000 -> begin
()
end));
(

let uu____21001 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____21001) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____21016 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____21016) with
| true -> begin
(

let guard = (

let uu____21028 = (

let uu____21029 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____21029 FStar_Syntax_Util.Equal))
in (match (uu____21028) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____21032 -> begin
(

let uu____21033 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_87 -> FStar_Pervasives_Native.Some (_0_87)) uu____21033))
end))
in (

let uu____21036 = (solve_prob orig guard [] wl)
in (solve env uu____21036)))
end
| uu____21037 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____21038 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_let (uu____21039), FStar_Syntax_Syntax.Tm_let (uu____21040)) -> begin
(

let uu____21065 = (FStar_Syntax_Util.term_eq t1 t2)
in (match (uu____21065) with
| true -> begin
(

let uu____21066 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____21066))
end
| uu____21067 -> begin
(giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig)
end))
end
| (FStar_Syntax_Syntax.Tm_let (uu____21068), uu____21069) -> begin
(

let uu____21082 = (

let uu____21087 = (

let uu____21088 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____21089 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____21090 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____21091 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)" uu____21088 uu____21089 uu____21090 uu____21091)))))
in ((FStar_Errors.Fatal_UnificationNotWellFormed), (uu____21087)))
in (FStar_Errors.raise_error uu____21082 t1.FStar_Syntax_Syntax.pos))
end
| (uu____21092, FStar_Syntax_Syntax.Tm_let (uu____21093)) -> begin
(

let uu____21106 = (

let uu____21111 = (

let uu____21112 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____21113 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____21114 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____21115 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)" uu____21112 uu____21113 uu____21114 uu____21115)))))
in ((FStar_Errors.Fatal_UnificationNotWellFormed), (uu____21111)))
in (FStar_Errors.raise_error uu____21106 t1.FStar_Syntax_Syntax.pos))
end
| uu____21116 -> begin
(giveup env "head tag mismatch" orig)
end));
)
end))))
end));
)))))))))));
))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (

let c1 = problem.FStar_TypeChecker_Common.lhs
in (

let c2 = problem.FStar_TypeChecker_Common.rhs
in (

let orig = FStar_TypeChecker_Common.CProb (problem)
in (

let sub_prob = (fun t1 rel t2 reason -> (

let uu____21144 = (p_scope orig)
in (mk_problem uu____21144 orig t1 rel t2 FStar_Pervasives_Native.None reason)))
in (

let solve_eq = (fun c1_comp c2_comp -> ((

let uu____21153 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____21153) with
| true -> begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end
| uu____21154 -> begin
()
end));
(match ((not ((FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)))) with
| true -> begin
(

let uu____21155 = (

let uu____21156 = (FStar_Syntax_Print.lid_to_string c1_comp.FStar_Syntax_Syntax.effect_name)
in (

let uu____21157 = (FStar_Syntax_Print.lid_to_string c2_comp.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible effects: %s <> %s" uu____21156 uu____21157)))
in (giveup env uu____21155 orig))
end
| uu____21158 -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____21177 uu____21178 -> (match (((uu____21177), (uu____21178))) with
| ((a1, uu____21196), (a2, uu____21198)) -> begin
(

let uu____21207 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _0_88 -> FStar_TypeChecker_Common.TProb (_0_88)) uu____21207))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (

let uu____21217 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) FStar_Pervasives_Native.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____21217))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))))
end);
))
in (

let solve_sub = (fun c11 edge c21 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let lift_c1 = (fun uu____21241 -> (

let wp = (match (c11.FStar_Syntax_Syntax.effect_args) with
| ((wp1, uu____21248))::[] -> begin
wp1
end
| uu____21265 -> begin
(

let uu____21274 = (

let uu____21275 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c11.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" uu____21275))
in (failwith uu____21274))
end)
in (

let univs1 = (match (c11.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
(

let uu____21283 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (uu____21283)::[])
end
| x -> begin
x
end)
in (

let uu____21285 = (

let uu____21294 = (

let uu____21295 = (

let uu____21296 = (FStar_List.hd univs1)
in (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp uu____21296 c11.FStar_Syntax_Syntax.result_typ wp))
in (FStar_Syntax_Syntax.as_arg uu____21295))
in (uu____21294)::[])
in {FStar_Syntax_Syntax.comp_univs = univs1; FStar_Syntax_Syntax.effect_name = c21.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c11.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____21285; FStar_Syntax_Syntax.flags = c11.FStar_Syntax_Syntax.flags}))))
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____21297 = (lift_c1 ())
in (solve_eq uu____21297 c21))
end
| uu____21298 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___118_21303 -> (match (uu___118_21303) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| uu____21304 -> begin
false
end))))
in (

let uu____21305 = (match (((c11.FStar_Syntax_Syntax.effect_args), (c21.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____21339))::uu____21340, ((wp2, uu____21342))::uu____21343) -> begin
((wp1), (wp2))
end
| uu____21400 -> begin
(

let uu____21421 = (

let uu____21426 = (

let uu____21427 = (FStar_Syntax_Print.lid_to_string c11.FStar_Syntax_Syntax.effect_name)
in (

let uu____21428 = (FStar_Syntax_Print.lid_to_string c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____21427 uu____21428)))
in ((FStar_Errors.Fatal_ExpectNormalizedEffect), (uu____21426)))
in (FStar_Errors.raise_error uu____21421 env.FStar_TypeChecker_Env.range))
end)
in (match (uu____21305) with
| (wpc1, wpc2) -> begin
(

let uu____21447 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____21447) with
| true -> begin
(

let uu____21450 = (problem_using_guard orig c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ FStar_Pervasives_Native.None "result type")
in (solve_t env uu____21450 wl))
end
| uu____21453 -> begin
(

let uu____21454 = (

let uu____21461 = (FStar_TypeChecker_Env.effect_decl_opt env c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.must uu____21461))
in (match (uu____21454) with
| (c2_decl, qualifiers) -> begin
(

let uu____21482 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____21482) with
| true -> begin
(

let c1_repr = (

let uu____21486 = (

let uu____21487 = (

let uu____21488 = (lift_c1 ())
in (FStar_Syntax_Syntax.mk_Comp uu____21488))
in (

let uu____21489 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____21487 uu____21489)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env uu____21486))
in (

let c2_repr = (

let uu____21491 = (

let uu____21492 = (FStar_Syntax_Syntax.mk_Comp c21)
in (

let uu____21493 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____21492 uu____21493)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env uu____21491))
in (

let prob = (

let uu____21495 = (

let uu____21500 = (

let uu____21501 = (FStar_Syntax_Print.term_to_string c1_repr)
in (

let uu____21502 = (FStar_Syntax_Print.term_to_string c2_repr)
in (FStar_Util.format2 "sub effect repr: %s <: %s" uu____21501 uu____21502)))
in (sub_prob c1_repr problem.FStar_TypeChecker_Common.relation c2_repr uu____21500))
in FStar_TypeChecker_Common.TProb (uu____21495))
in (

let wl1 = (

let uu____21504 = (

let uu____21507 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in FStar_Pervasives_Native.Some (uu____21507))
in (solve_prob orig uu____21504 [] wl))
in (solve env (attempt ((prob)::[]) wl1))))))
end
| uu____21512 -> begin
(

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____21514 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____21516 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____21516) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____21517 -> begin
()
end));
(

let c1_univ = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____21519 = (

let uu____21522 = (

let uu____21523 = (

let uu____21538 = (FStar_TypeChecker_Env.inst_effect_fun_with ((c1_univ)::[]) env c2_decl c2_decl.FStar_Syntax_Syntax.trivial)
in (

let uu____21539 = (

let uu____21542 = (FStar_Syntax_Syntax.as_arg c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____21543 = (

let uu____21546 = (

let uu____21547 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c1_univ c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____21547))
in (uu____21546)::[])
in (uu____21542)::uu____21543))
in ((uu____21538), (uu____21539))))
in FStar_Syntax_Syntax.Tm_app (uu____21523))
in (FStar_Syntax_Syntax.mk uu____21522))
in (uu____21519 FStar_Pervasives_Native.None r)));
)
end
| uu____21553 -> begin
(

let c1_univ = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (

let c2_univ = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____21556 = (

let uu____21559 = (

let uu____21560 = (

let uu____21575 = (FStar_TypeChecker_Env.inst_effect_fun_with ((c2_univ)::[]) env c2_decl c2_decl.FStar_Syntax_Syntax.stronger)
in (

let uu____21576 = (

let uu____21579 = (FStar_Syntax_Syntax.as_arg c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____21580 = (

let uu____21583 = (FStar_Syntax_Syntax.as_arg wpc2)
in (

let uu____21584 = (

let uu____21587 = (

let uu____21588 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c1_univ c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____21588))
in (uu____21587)::[])
in (uu____21583)::uu____21584))
in (uu____21579)::uu____21580))
in ((uu____21575), (uu____21576))))
in FStar_Syntax_Syntax.Tm_app (uu____21560))
in (FStar_Syntax_Syntax.mk uu____21559))
in (uu____21556 FStar_Pervasives_Native.None r))))
end)
end)
in (

let base_prob = (

let uu____21595 = (sub_prob c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _0_89 -> FStar_TypeChecker_Common.TProb (_0_89)) uu____21595))
in (

let wl1 = (

let uu____21605 = (

let uu____21608 = (

let uu____21611 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____21611 g))
in (FStar_All.pipe_left (fun _0_90 -> FStar_Pervasives_Native.Some (_0_90)) uu____21608))
in (solve_prob orig uu____21605 [] wl))
in (solve env (attempt ((base_prob)::[]) wl1)))))
end))
end))
end))
end)))
end))))
in (

let uu____21624 = (FStar_Util.physical_equality c1 c2)
in (match (uu____21624) with
| true -> begin
(

let uu____21625 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____21625))
end
| uu____21626 -> begin
((

let uu____21628 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____21628) with
| true -> begin
(

let uu____21629 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____21630 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____21629 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____21630)))
end
| uu____21631 -> begin
()
end));
(

let uu____21632 = (

let uu____21637 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____21638 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____21637), (uu____21638))))
in (match (uu____21632) with
| (c11, c21) -> begin
(match (((c11.FStar_Syntax_Syntax.n), (c21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____21642), FStar_Syntax_Syntax.Total (t2, uu____21644)) when (FStar_Syntax_Util.non_informative t2) -> begin
(

let uu____21661 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____21661 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____21664), FStar_Syntax_Syntax.Total (uu____21665)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| (FStar_Syntax_Syntax.Total (t1, uu____21683), FStar_Syntax_Syntax.Total (t2, uu____21685)) -> begin
(

let uu____21702 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____21702 wl))
end
| (FStar_Syntax_Syntax.GTotal (t1, uu____21706), FStar_Syntax_Syntax.GTotal (t2, uu____21708)) -> begin
(

let uu____21725 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____21725 wl))
end
| (FStar_Syntax_Syntax.Total (t1, uu____21729), FStar_Syntax_Syntax.GTotal (t2, uu____21731)) -> begin
(

let uu____21748 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____21748 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____21751), FStar_Syntax_Syntax.Comp (uu____21752)) -> begin
(

let uu____21761 = (

let uu___167_21766 = problem
in (

let uu____21771 = (

let uu____21772 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____21772))
in {FStar_TypeChecker_Common.pid = uu___167_21766.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____21771; FStar_TypeChecker_Common.relation = uu___167_21766.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___167_21766.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___167_21766.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___167_21766.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___167_21766.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___167_21766.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___167_21766.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___167_21766.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____21761 wl))
end
| (FStar_Syntax_Syntax.Total (uu____21773), FStar_Syntax_Syntax.Comp (uu____21774)) -> begin
(

let uu____21783 = (

let uu___167_21788 = problem
in (

let uu____21793 = (

let uu____21794 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____21794))
in {FStar_TypeChecker_Common.pid = uu___167_21788.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____21793; FStar_TypeChecker_Common.relation = uu___167_21788.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___167_21788.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___167_21788.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___167_21788.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___167_21788.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___167_21788.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___167_21788.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___167_21788.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____21783 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____21795), FStar_Syntax_Syntax.GTotal (uu____21796)) -> begin
(

let uu____21805 = (

let uu___168_21810 = problem
in (

let uu____21815 = (

let uu____21816 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____21816))
in {FStar_TypeChecker_Common.pid = uu___168_21810.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___168_21810.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___168_21810.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____21815; FStar_TypeChecker_Common.element = uu___168_21810.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___168_21810.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___168_21810.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___168_21810.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___168_21810.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___168_21810.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____21805 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____21817), FStar_Syntax_Syntax.Total (uu____21818)) -> begin
(

let uu____21827 = (

let uu___168_21832 = problem
in (

let uu____21837 = (

let uu____21838 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____21838))
in {FStar_TypeChecker_Common.pid = uu___168_21832.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___168_21832.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___168_21832.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____21837; FStar_TypeChecker_Common.element = uu___168_21832.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___168_21832.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___168_21832.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___168_21832.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___168_21832.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___168_21832.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____21827 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____21839), FStar_Syntax_Syntax.Comp (uu____21840)) -> begin
(

let uu____21841 = ((((FStar_Syntax_Util.is_ml_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) || ((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_total_comp c21))) || (((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB)))
in (match (uu____21841) with
| true -> begin
(

let uu____21842 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c11) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c21) FStar_Pervasives_Native.None "result type")
in (solve_t env uu____21842 wl))
end
| uu____21845 -> begin
(

let c1_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (

let c2_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____21848 = (match ((FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) with
| true -> begin
((c1_comp), (c2_comp))
end
| uu____21857 -> begin
(

let uu____21858 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let uu____21859 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((uu____21858), (uu____21859))))
end)
in (match (uu____21848) with
| (c1_comp1, c2_comp1) -> begin
(solve_eq c1_comp1 c2_comp1)
end))
end
| uu____21862 -> begin
(

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((

let uu____21866 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____21866) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c12.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c22.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____21867 -> begin
()
end));
(

let uu____21868 = (FStar_TypeChecker_Env.monad_leq env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____21868) with
| FStar_Pervasives_Native.None -> begin
(

let uu____21871 = (

let uu____21872 = (FStar_Syntax_Print.lid_to_string c12.FStar_Syntax_Syntax.effect_name)
in (

let uu____21873 = (FStar_Syntax_Print.lid_to_string c22.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____21872 uu____21873)))
in (giveup env uu____21871 orig))
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

let uu____21878 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____21916 -> (match (uu____21916) with
| (uu____21929, uu____21930, u, uu____21932, uu____21933, uu____21934) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____21878 (FStar_String.concat ", "))))


let ineqs_to_string : (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.string = (fun ineqs -> (

let vars = (

let uu____21965 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs) (FStar_List.map FStar_Syntax_Print.univ_to_string))
in (FStar_All.pipe_right uu____21965 (FStar_String.concat ", ")))
in (

let ineqs1 = (

let uu____21983 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs) (FStar_List.map (fun uu____22011 -> (match (uu____22011) with
| (u1, u2) -> begin
(

let uu____22018 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____22019 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "%s < %s" uu____22018 uu____22019)))
end))))
in (FStar_All.pipe_right uu____21983 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred), (g.FStar_TypeChecker_Env.univ_ineqs))) with
| (FStar_TypeChecker_Common.Trivial, [], (uu____22036, [])) -> begin
"{}"
end
| uu____22061 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____22078 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____22078) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____22079 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____22081 = (FStar_List.map (fun uu____22091 -> (match (uu____22091) with
| (uu____22096, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right uu____22081 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (

let uu____22101 = (ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs)
in (FStar_Util.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n" form carry uu____22101 imps)))))
end))


let new_t_problem : 'Auu____22109 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  'Auu____22109 FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term, 'Auu____22109) FStar_TypeChecker_Common.problem = (fun env lhs rel rhs elt loc -> (

let reason = (

let uu____22143 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____22143) with
| true -> begin
(

let uu____22144 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____22145 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____22144 (rel_to_string rel) uu____22145)))
end
| uu____22146 -> begin
"TOP"
end))
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (

let uu____22169 = (

let uu____22172 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_91 -> FStar_Pervasives_Native.Some (_0_91)) uu____22172))
in (FStar_Syntax_Syntax.new_bv uu____22169 t1))
in (

let env1 = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (

let uu____22181 = (

let uu____22184 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _0_92 -> FStar_Pervasives_Native.Some (_0_92)) uu____22184))
in (

let uu____22187 = (FStar_TypeChecker_Env.get_range env1)
in (new_t_problem env1 t1 rel t2 uu____22181 uu____22187)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option = (fun env probs err -> (

let probs1 = (

let uu____22217 = (FStar_Options.eager_inference ())
in (match (uu____22217) with
| true -> begin
(

let uu___169_22218 = probs
in {attempting = uu___169_22218.attempting; wl_deferred = uu___169_22218.wl_deferred; ctr = uu___169_22218.ctr; defer_ok = false; smt_ok = uu___169_22218.smt_ok; tcenv = uu___169_22218.tcenv})
end
| uu____22219 -> begin
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
((

let uu____22229 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____22229) with
| true -> begin
(

let uu____22230 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____22230))
end
| uu____22231 -> begin
()
end));
(

let result = (err ((d), (s)))
in ((FStar_Syntax_Unionfind.rollback tx);
result;
));
)
end)))))


let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
((

let uu____22244 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____22244) with
| true -> begin
(

let uu____22245 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____22245))
end
| uu____22246 -> begin
()
end));
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env f)
in ((

let uu____22249 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____22249) with
| true -> begin
(

let uu____22250 = (FStar_Syntax_Print.term_to_string f1)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____22250))
end
| uu____22251 -> begin
()
end));
(

let f2 = (

let uu____22253 = (

let uu____22254 = (FStar_Syntax_Util.unmeta f1)
in uu____22254.FStar_Syntax_Syntax.n)
in (match (uu____22253) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____22258 -> begin
FStar_TypeChecker_Common.NonTrivial (f1)
end))
in (

let uu___170_22259 = g
in {FStar_TypeChecker_Env.guard_f = f2; FStar_TypeChecker_Env.deferred = uu___170_22259.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___170_22259.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___170_22259.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____22278 = (

let uu____22279 = (

let uu____22280 = (

let uu____22281 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____22281 (fun _0_93 -> FStar_TypeChecker_Common.NonTrivial (_0_93))))
in {FStar_TypeChecker_Env.guard_f = uu____22280; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env uu____22279))
in (FStar_All.pipe_left (fun _0_94 -> FStar_Pervasives_Native.Some (_0_94)) uu____22278))
end))


let with_guard_no_simp : 'Auu____22308 . 'Auu____22308  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____22328 = (

let uu____22329 = (

let uu____22330 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____22330 (fun _0_95 -> FStar_TypeChecker_Common.NonTrivial (_0_95))))
in {FStar_TypeChecker_Env.guard_f = uu____22329; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in FStar_Pervasives_Native.Some (uu____22328))
end))


let try_teq : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun smt_ok env t1 t2 -> ((

let uu____22368 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____22368) with
| true -> begin
(

let uu____22369 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____22370 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" uu____22369 uu____22370)))
end
| uu____22371 -> begin
()
end));
(

let prob = (

let uu____22373 = (

let uu____22378 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None uu____22378))
in (FStar_All.pipe_left (fun _0_96 -> FStar_TypeChecker_Common.TProb (_0_96)) uu____22373))
in (

let g = (

let uu____22386 = (

let uu____22389 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____22389 (fun uu____22391 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____22386))
in g));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____22409 = (try_teq true env t1 t2)
in (match (uu____22409) with
| FStar_Pervasives_Native.None -> begin
((

let uu____22413 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____22414 = (FStar_TypeChecker_Err.basic_type_error env FStar_Pervasives_Native.None t2 t1)
in (FStar_Errors.log_issue uu____22413 uu____22414)));
trivial_guard;
)
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____22421 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____22421) with
| true -> begin
(

let uu____22422 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____22423 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____22424 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____22422 uu____22423 uu____22424))))
end
| uu____22425 -> begin
()
end));
g;
)
end)))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env e t1 t2 -> (

let uu____22438 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____22439 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t2 t1)
in (FStar_Errors.log_issue uu____22438 uu____22439))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env c1 c2 -> ((

let uu____22456 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____22456) with
| true -> begin
(

let uu____22457 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____22458 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" uu____22457 uu____22458)))
end
| uu____22459 -> begin
()
end));
(

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____22461 -> begin
FStar_TypeChecker_Common.SUB
end)
in (

let prob = (

let uu____22463 = (

let uu____22468 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 FStar_Pervasives_Native.None uu____22468 "sub_comp"))
in (FStar_All.pipe_left (fun _0_97 -> FStar_TypeChecker_Common.CProb (_0_97)) uu____22463))
in (

let uu____22473 = (

let uu____22476 = (singleton env prob)
in (solve_and_commit env uu____22476 (fun uu____22478 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____22473))));
))


let solve_universe_inequalities' : FStar_Syntax_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun tx env uu____22507 -> (match (uu____22507) with
| (variables, ineqs) -> begin
(

let fail1 = (fun u1 u2 -> ((FStar_Syntax_Unionfind.rollback tx);
(

let uu____22546 = (

let uu____22551 = (

let uu____22552 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____22553 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Universe %s and %s are incompatible" uu____22552 uu____22553)))
in ((FStar_Errors.Fatal_IncompatibleUniverse), (uu____22551)))
in (

let uu____22554 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____22546 uu____22554)));
))
in (

let equiv1 = (fun v1 v' -> (

let uu____22562 = (

let uu____22567 = (FStar_Syntax_Subst.compress_univ v1)
in (

let uu____22568 = (FStar_Syntax_Subst.compress_univ v')
in ((uu____22567), (uu____22568))))
in (match (uu____22562) with
| (FStar_Syntax_Syntax.U_unif (v0), FStar_Syntax_Syntax.U_unif (v0')) -> begin
(FStar_Syntax_Unionfind.univ_equiv v0 v0')
end
| uu____22587 -> begin
false
end)))
in (

let sols = (FStar_All.pipe_right variables (FStar_List.collect (fun v1 -> (

let uu____22617 = (FStar_Syntax_Subst.compress_univ v1)
in (match (uu____22617) with
| FStar_Syntax_Syntax.U_unif (uu____22624) -> begin
(

let lower_bounds_of_v = (FStar_All.pipe_right ineqs (FStar_List.collect (fun uu____22653 -> (match (uu____22653) with
| (u, v') -> begin
(

let uu____22662 = (equiv1 v1 v')
in (match (uu____22662) with
| true -> begin
(

let uu____22665 = (FStar_All.pipe_right variables (FStar_Util.for_some (equiv1 u)))
in (match (uu____22665) with
| true -> begin
[]
end
| uu____22670 -> begin
(u)::[]
end))
end
| uu____22671 -> begin
[]
end))
end))))
in (

let lb = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max (lower_bounds_of_v)))
in (((lb), (v1)))::[]))
end
| uu____22681 -> begin
[]
end)))))
in (

let uu____22686 = (

let wl = (

let uu___171_22690 = (empty_worklist env)
in {attempting = uu___171_22690.attempting; wl_deferred = uu___171_22690.wl_deferred; ctr = uu___171_22690.ctr; defer_ok = false; smt_ok = uu___171_22690.smt_ok; tcenv = uu___171_22690.tcenv})
in (FStar_All.pipe_right sols (FStar_List.map (fun uu____22708 -> (match (uu____22708) with
| (lb, v1) -> begin
(

let uu____22715 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl lb v1)
in (match (uu____22715) with
| USolved (wl1) -> begin
()
end
| uu____22717 -> begin
(fail1 lb v1)
end))
end)))))
in (

let rec check_ineq = (fun uu____22725 -> (match (uu____22725) with
| (u, v1) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u)
in (

let v2 = (FStar_TypeChecker_Normalize.normalize_universe env v1)
in (match (((u1), (v2))) with
| (FStar_Syntax_Syntax.U_zero, uu____22734) -> begin
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
| (FStar_Syntax_Syntax.U_name (uu____22757), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_unif (uu____22759), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_max (us), uu____22770) -> begin
(FStar_All.pipe_right us (FStar_Util.for_all (fun u2 -> (check_ineq ((u2), (v2))))))
end
| (uu____22777, FStar_Syntax_Syntax.U_max (vs)) -> begin
(FStar_All.pipe_right vs (FStar_Util.for_some (fun v3 -> (check_ineq ((u1), (v3))))))
end
| uu____22785 -> begin
false
end)))
end))
in (

let uu____22790 = (FStar_All.pipe_right ineqs (FStar_Util.for_all (fun uu____22805 -> (match (uu____22805) with
| (u, v1) -> begin
(

let uu____22812 = (check_ineq ((u), (v1)))
in (match (uu____22812) with
| true -> begin
true
end
| uu____22813 -> begin
((

let uu____22815 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____22815) with
| true -> begin
(

let uu____22816 = (FStar_Syntax_Print.univ_to_string u)
in (

let uu____22817 = (FStar_Syntax_Print.univ_to_string v1)
in (FStar_Util.print2 "%s </= %s" uu____22816 uu____22817)))
end
| uu____22818 -> begin
()
end));
false;
)
end))
end))))
in (match (uu____22790) with
| true -> begin
()
end
| uu____22819 -> begin
((

let uu____22821 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____22821) with
| true -> begin
((

let uu____22823 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Partially solved inequality constraints are: %s\n" uu____22823));
(FStar_Syntax_Unionfind.rollback tx);
(

let uu____22833 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Original solved inequality constraints are: %s\n" uu____22833));
)
end
| uu____22842 -> begin
()
end));
(

let uu____22843 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_FailToSolveUniverseInEquality), ("Failed to solve universe inequalities for inductives")) uu____22843));
)
end)))))))
end))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun env ineqs -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Syntax_Unionfind.commit tx);
)))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail1 = (fun uu____22891 -> (match (uu____22891) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ErrorInSolveDeferredConstraints), (msg)) (p_loc d)))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in ((

let uu____22905 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____22905) with
| true -> begin
(

let uu____22906 = (wl_to_string wl)
in (

let uu____22907 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" uu____22906 uu____22907)))
end
| uu____22920 -> begin
()
end));
(

let g1 = (

let uu____22922 = (solve_and_commit env wl fail1)
in (match (uu____22922) with
| FStar_Pervasives_Native.Some ([]) -> begin
(

let uu___172_22935 = g
in {FStar_TypeChecker_Env.guard_f = uu___172_22935.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu___172_22935.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___172_22935.FStar_TypeChecker_Env.implicits})
end
| uu____22940 -> begin
(failwith "impossible: Unexpected deferred constraints remain")
end))
in ((solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___173_22944 = g1
in {FStar_TypeChecker_Env.guard_f = uu___173_22944.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___173_22944.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = uu___173_22944.FStar_TypeChecker_Env.implicits});
));
))))


let last_proof_ns : FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let maybe_update_proof_ns : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (

let pns = env.FStar_TypeChecker_Env.proof_ns
in (

let uu____22994 = (FStar_ST.op_Bang last_proof_ns)
in (match (uu____22994) with
| FStar_Pervasives_Native.None -> begin
(FStar_ST.op_Colon_Equals last_proof_ns (FStar_Pervasives_Native.Some (pns)))
end
| FStar_Pervasives_Native.Some (old) -> begin
(match ((Prims.op_Equality old pns)) with
| true -> begin
()
end
| uu____23056 -> begin
((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(FStar_ST.op_Colon_Equals last_proof_ns (FStar_Pervasives_Native.Some (pns)));
)
end)
end))))


let discharge_guard' : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun use_env_range_msg env g use_smt -> (

let debug1 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTQuery")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Tac"))))
in (

let g1 = (solve_deferred_constraints env g)
in (

let ret_g = (

let uu___174_23115 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___174_23115.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___174_23115.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___174_23115.FStar_TypeChecker_Env.implicits})
in (

let uu____23116 = (

let uu____23117 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____23117)))
in (match (uu____23116) with
| true -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| uu____23120 -> begin
(match (g1.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((match (debug1) with
| true -> begin
(

let uu____23125 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____23126 = (

let uu____23127 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____23127))
in (FStar_Errors.diag uu____23125 uu____23126)))
end
| uu____23128 -> begin
()
end);
(

let vc1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env vc)
in ((match (debug1) with
| true -> begin
(

let uu____23131 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____23132 = (

let uu____23133 = (FStar_Syntax_Print.term_to_string vc1)
in (FStar_Util.format1 "After normalization VC=\n%s\n" uu____23133))
in (FStar_Errors.diag uu____23131 uu____23132)))
end
| uu____23134 -> begin
()
end);
(

let uu____23136 = (FStar_TypeChecker_Env.get_range env)
in (def_check_closed_in_env uu____23136 "discharge_guard\'" env vc1));
(

let uu____23137 = (check_trivial vc1)
in (match (uu____23137) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc2) -> begin
(match ((not (use_smt))) with
| true -> begin
((match (debug1) with
| true -> begin
(

let uu____23144 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____23145 = (

let uu____23146 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Cannot solve without SMT : %s\n" uu____23146))
in (FStar_Errors.diag uu____23144 uu____23145)))
end
| uu____23147 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end
| uu____23148 -> begin
((match (debug1) with
| true -> begin
(

let uu____23151 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____23152 = (

let uu____23153 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____23153))
in (FStar_Errors.diag uu____23151 uu____23152)))
end
| uu____23154 -> begin
()
end);
(

let vcs = (

let uu____23164 = (FStar_Options.use_tactics ())
in (match (uu____23164) with
| true -> begin
(FStar_Options.with_saved_options (fun uu____23183 -> ((

let uu____23185 = (FStar_Options.set_options FStar_Options.Set "--no_tactics")
in (FStar_All.pipe_left FStar_Pervasives.ignore uu____23185));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.preprocess env vc2);
)))
end
| uu____23186 -> begin
(

let uu____23187 = (

let uu____23194 = (FStar_Options.peek ())
in ((env), (vc2), (uu____23194)))
in (uu____23187)::[])
end))
in (FStar_All.pipe_right vcs (FStar_List.iter (fun uu____23228 -> (match (uu____23228) with
| (env1, goal, opts) -> begin
(

let goal1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env1 goal)
in (

let uu____23239 = (check_trivial goal1)
in (match (uu____23239) with
| FStar_TypeChecker_Common.Trivial -> begin
(match (debug1) with
| true -> begin
(FStar_Util.print_string "Goal completely solved by tactic\n")
end
| uu____23241 -> begin
()
end)
end
| FStar_TypeChecker_Common.NonTrivial (goal2) -> begin
((FStar_Options.push ());
(FStar_Options.set opts);
(maybe_update_proof_ns env1);
(match (debug1) with
| true -> begin
(

let uu____23247 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____23248 = (

let uu____23249 = (FStar_Syntax_Print.term_to_string goal2)
in (

let uu____23250 = (FStar_TypeChecker_Env.string_of_proof_ns env1)
in (FStar_Util.format2 "Trying to solve:\n> %s\nWith proof_ns:\n %s\n" uu____23249 uu____23250)))
in (FStar_Errors.diag uu____23247 uu____23248)))
end
| uu____23251 -> begin
()
end);
(match (debug1) with
| true -> begin
(

let uu____23253 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____23254 = (

let uu____23255 = (FStar_Syntax_Print.term_to_string goal2)
in (FStar_Util.format1 "Before calling solver VC=\n%s\n" uu____23255))
in (FStar_Errors.diag uu____23253 uu____23254)))
end
| uu____23256 -> begin
()
end);
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env1 goal2);
(FStar_Options.pop ());
)
end)))
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

let uu____23265 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____23265) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____23271 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ExpectTrivialPreCondition), ("Expected a trivial pre-condition")) uu____23271))
end)))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let uu____23278 = (discharge_guard' FStar_Pervasives_Native.None env g true)
in (match (uu____23278) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end)))


let resolve_implicits' : Prims.bool  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun must_total forcelax g -> (

let unresolved = (fun u -> (

let uu____23297 = (FStar_Syntax_Unionfind.find u)
in (match (uu____23297) with
| FStar_Pervasives_Native.None -> begin
true
end
| uu____23300 -> begin
false
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____23318 = acc
in (match (uu____23318) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____23337 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd1)::tl1 -> begin
(

let uu____23404 = hd1
in (match (uu____23404) with
| (uu____23417, env, u, tm, k, r) -> begin
(

let uu____23423 = (unresolved u)
in (match (uu____23423) with
| true -> begin
(until_fixpoint (((hd1)::out), (changed)) tl1)
end
| uu____23450 -> begin
(

let tm1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (

let env1 = (match (forcelax) with
| true -> begin
(

let uu___175_23453 = env
in {FStar_TypeChecker_Env.solver = uu___175_23453.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___175_23453.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___175_23453.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___175_23453.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___175_23453.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___175_23453.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___175_23453.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___175_23453.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___175_23453.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___175_23453.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___175_23453.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___175_23453.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___175_23453.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___175_23453.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___175_23453.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___175_23453.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___175_23453.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___175_23453.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___175_23453.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___175_23453.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___175_23453.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___175_23453.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___175_23453.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___175_23453.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___175_23453.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___175_23453.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___175_23453.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___175_23453.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___175_23453.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___175_23453.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___175_23453.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___175_23453.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___175_23453.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___175_23453.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___175_23453.FStar_TypeChecker_Env.dep_graph})
end
| uu____23454 -> begin
env
end)
in ((

let uu____23456 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("RelCheck")))
in (match (uu____23456) with
| true -> begin
(

let uu____23457 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____23458 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____23459 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" uu____23457 uu____23458 uu____23459))))
end
| uu____23460 -> begin
()
end));
(

let g1 = (FStar_All.try_with (fun uu___177_23463 -> (match (()) with
| () -> begin
(env1.FStar_TypeChecker_Env.check_type_of must_total env1 tm1 k)
end)) (fun uu___176_23467 -> (match (uu___176_23467) with
| e -> begin
((

let uu____23470 = (

let uu____23479 = (

let uu____23486 = (

let uu____23487 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____23488 = (FStar_TypeChecker_Normalize.term_to_string env1 tm1)
in (FStar_Util.format2 "Failed while checking implicit %s set to %s" uu____23487 uu____23488)))
in ((FStar_Errors.Error_BadImplicit), (uu____23486), (r)))
in (uu____23479)::[])
in (FStar_Errors.add_errors uu____23470));
(FStar_Exn.raise e);
)
end)))
in (

let g2 = (match (env1.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___178_23502 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___178_23502.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___178_23502.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___178_23502.FStar_TypeChecker_Env.implicits})
end
| uu____23503 -> begin
g1
end)
in (

let g' = (

let uu____23505 = (discharge_guard' (FStar_Pervasives_Native.Some ((fun uu____23511 -> (FStar_Syntax_Print.term_to_string tm1)))) env1 g2 true)
in (match (uu____23505) with
| FStar_Pervasives_Native.Some (g3) -> begin
g3
end
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end))
in (until_fixpoint (((FStar_List.append g'.FStar_TypeChecker_Env.implicits out)), (true)) tl1))));
)))
end))
end))
end)
end)))
in (

let uu___179_23539 = g
in (

let uu____23540 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___179_23539.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___179_23539.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___179_23539.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____23540})))))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (resolve_implicits' true false g))


let resolve_implicits_tac : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (resolve_implicits' false true g))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g1 = (

let uu____23594 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____23594 resolve_implicits))
in (match (g1.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(

let uu____23607 = (discharge_guard env g1)
in (FStar_All.pipe_left FStar_Pervasives.ignore uu____23607))
end
| ((reason, uu____23609, uu____23610, e, t, r))::uu____23614 -> begin
(

let uu____23641 = (

let uu____23646 = (

let uu____23647 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____23648 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Failed to resolve implicit argument of type \'%s\' introduced in %s" uu____23647 uu____23648)))
in ((FStar_Errors.Fatal_FailToResolveImplicitArgument), (uu____23646)))
in (FStar_Errors.raise_error uu____23641 r))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___180_23655 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___180_23655.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___180_23655.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ((((u1), (u2)))::[])); FStar_TypeChecker_Env.implicits = uu___180_23655.FStar_TypeChecker_Env.implicits}))


let discharge_guard_nosmt : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun env g -> (

let uu____23678 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____23678) with
| FStar_Pervasives_Native.Some (uu____23683) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end)))


let teq_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____23693 = (try_teq false env t1 t2)
in (match (uu____23693) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g) -> begin
(discharge_guard_nosmt env g)
end)))


let check_subtyping : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.option = (fun env t1 t2 -> ((

let uu____23713 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____23713) with
| true -> begin
(

let uu____23714 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____23715 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23714 uu____23715)))
end
| uu____23716 -> begin
()
end));
(

let uu____23717 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____23717) with
| (prob, x) -> begin
(

let g = (

let uu____23733 = (

let uu____23736 = (singleton' env prob true)
in (solve_and_commit env uu____23736 (fun uu____23738 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____23733))
in ((

let uu____23748 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____23748) with
| true -> begin
(

let uu____23749 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____23750 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____23751 = (

let uu____23752 = (FStar_Util.must g)
in (guard_to_string env uu____23752))
in (FStar_Util.print3 "check_subtyping succeeded: %s <: %s\n\tguard is %s\n" uu____23749 uu____23750 uu____23751))))
end
| uu____23753 -> begin
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

let uu____23780 = (check_subtyping env t1 t2)
in (match (uu____23780) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (x, g) -> begin
(

let uu____23799 = (

let uu____23800 = (FStar_Syntax_Syntax.mk_binder x)
in (abstract_guard uu____23800 g))
in FStar_Pervasives_Native.Some (uu____23799))
end)))


let get_subtyping_prop : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> (

let uu____23812 = (check_subtyping env t1 t2)
in (match (uu____23812) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (x, g) -> begin
(

let uu____23831 = (

let uu____23832 = (

let uu____23833 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____23833)::[])
in (close_guard env uu____23832 g))
in FStar_Pervasives_Native.Some (uu____23831))
end)))


let subtype_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> ((

let uu____23844 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____23844) with
| true -> begin
(

let uu____23845 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____23846 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23845 uu____23846)))
end
| uu____23847 -> begin
()
end));
(

let uu____23848 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____23848) with
| (prob, x) -> begin
(

let g = (

let uu____23858 = (

let uu____23861 = (singleton' env prob false)
in (solve_and_commit env uu____23861 (fun uu____23863 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____23858))
in (match (g) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g1) -> begin
(

let g2 = (

let uu____23874 = (

let uu____23875 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____23875)::[])
in (close_guard env uu____23874 g1))
in (discharge_guard_nosmt env g2))
end))
end));
))






open Prims
open FStar_Pervasives

let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu____36; FStar_TypeChecker_Env.implicits = uu____37} -> begin
true
end
| uu____64 -> begin
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

let uu___121_101 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.NonTrivial (f'); FStar_TypeChecker_Env.deferred = uu___121_101.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___121_101.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___121_101.FStar_TypeChecker_Env.implicits}))
end))


let abstract_guard : FStar_Syntax_Syntax.binder  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun b g -> (abstract_guard_n ((b)::[]) g))


let def_check_vars_in_set : FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.term  ->  unit = (fun rng msg vset t -> (

let uu____136 = (FStar_Options.defensive ())
in (match (uu____136) with
| true -> begin
(

let s = (FStar_Syntax_Free.names t)
in (

let uu____140 = (

let uu____141 = (

let uu____142 = (FStar_Util.set_difference s vset)
in (FStar_All.pipe_left FStar_Util.set_is_empty uu____142))
in (not (uu____141)))
in (match (uu____140) with
| true -> begin
(

let uu____147 = (

let uu____152 = (

let uu____153 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____154 = (

let uu____155 = (FStar_Util.set_elements s)
in (FStar_All.pipe_right uu____155 (FStar_Syntax_Print.bvs_to_string ",\n\t")))
in (FStar_Util.format3 "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n" msg uu____153 uu____154)))
in ((FStar_Errors.Warning_Defensive), (uu____152)))
in (FStar_Errors.log_issue rng uu____147))
end
| uu____160 -> begin
()
end)))
end
| uu____161 -> begin
()
end)))


let def_check_closed : FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  unit = (fun rng msg t -> (

let uu____177 = (

let uu____178 = (FStar_Options.defensive ())
in (not (uu____178)))
in (match (uu____177) with
| true -> begin
()
end
| uu____179 -> begin
(def_check_vars_in_set rng msg FStar_Syntax_Free.empty t)
end)))


let def_check_closed_in : FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  unit = (fun rng msg l t -> (

let uu____204 = (

let uu____205 = (FStar_Options.defensive ())
in (not (uu____205)))
in (match (uu____204) with
| true -> begin
()
end
| uu____206 -> begin
(

let uu____207 = (FStar_Util.as_set l FStar_Syntax_Syntax.order_bv)
in (def_check_vars_in_set rng msg uu____207 t))
end)))


let def_check_closed_in_env : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  unit = (fun rng msg e t -> (

let uu____230 = (

let uu____231 = (FStar_Options.defensive ())
in (not (uu____231)))
in (match (uu____230) with
| true -> begin
()
end
| uu____232 -> begin
(

let uu____233 = (FStar_TypeChecker_Env.bound_vars e)
in (def_check_closed_in rng msg uu____233 t))
end)))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___122_247 = g
in (

let uu____248 = (

let uu____249 = (

let uu____250 = (

let uu____257 = (

let uu____258 = (

let uu____273 = (

let uu____276 = (FStar_Syntax_Syntax.as_arg e)
in (uu____276)::[])
in ((f), (uu____273)))
in FStar_Syntax_Syntax.Tm_app (uu____258))
in (FStar_Syntax_Syntax.mk uu____257))
in (uu____250 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _0_17 -> FStar_TypeChecker_Common.NonTrivial (_0_17)) uu____249))
in {FStar_TypeChecker_Env.guard_f = uu____248; FStar_TypeChecker_Env.deferred = uu___122_247.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___122_247.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___122_247.FStar_TypeChecker_Env.implicits}))
end))


let map_guard : FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  FStar_TypeChecker_Env.guard_t = (fun g map1 -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___123_298 = g
in (

let uu____299 = (

let uu____300 = (map1 f)
in FStar_TypeChecker_Common.NonTrivial (uu____300))
in {FStar_TypeChecker_Env.guard_f = uu____299; FStar_TypeChecker_Env.deferred = uu___123_298.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___123_298.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___123_298.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____306) -> begin
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

let uu____321 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (uu____321))
end))


let check_trivial : FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (

let uu____327 = (

let uu____328 = (FStar_Syntax_Util.unmeta t)
in uu____328.FStar_Syntax_Syntax.n)
in (match (uu____327) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____332 -> begin
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

let uu____373 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = uu____373; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (((FStar_List.append (FStar_Pervasives_Native.fst g1.FStar_TypeChecker_Env.univ_ineqs) (FStar_Pervasives_Native.fst g2.FStar_TypeChecker_Env.univ_ineqs))), ((FStar_List.append (FStar_Pervasives_Native.snd g1.FStar_TypeChecker_Env.univ_ineqs) (FStar_Pervasives_Native.snd g2.FStar_TypeChecker_Env.univ_ineqs)))); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard_univs : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun us bs g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let f1 = (FStar_List.fold_right2 (fun u b f1 -> (

let uu____454 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____454) with
| true -> begin
f1
end
| uu____455 -> begin
(FStar_Syntax_Util.mk_forall u (FStar_Pervasives_Native.fst b) f1)
end))) us bs f)
in (

let uu___124_456 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.NonTrivial (f1); FStar_TypeChecker_Env.deferred = uu___124_456.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___124_456.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___124_456.FStar_TypeChecker_Env.implicits}))
end))


let close_forall : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____481 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____481) with
| true -> begin
f1
end
| uu____482 -> begin
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

let uu___125_500 = g
in (

let uu____501 = (

let uu____502 = (close_forall env binders f)
in FStar_TypeChecker_Common.NonTrivial (uu____502))
in {FStar_TypeChecker_Env.guard_f = uu____501; FStar_TypeChecker_Env.deferred = uu___125_500.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___125_500.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___125_500.FStar_TypeChecker_Env.implicits}))
end))


let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (

let uv = (FStar_Syntax_Unionfind.fresh ())
in (match (binders) with
| [] -> begin
(

let uv1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k)))) FStar_Pervasives_Native.None r)
in ((uv1), (uv1)))
end
| uu____538 -> begin
(

let args = (FStar_All.pipe_right binders (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder))
in (

let k' = (

let uu____563 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders uu____563))
in (

let uv1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k')))) FStar_Pervasives_Native.None r)
in (

let uu____571 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((uv1), (args)))) FStar_Pervasives_Native.None r)
in ((uu____571), (uv1))))))
end)))

type uvi =
| TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)


let uu___is_TERM : uvi  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TERM (_0) -> begin
true
end
| uu____622 -> begin
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
| uu____664 -> begin
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
| uu____872 -> begin
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
| uu____890 -> begin
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
| uu____915 -> begin
false
end))


let uu___is_CONTRAVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CONTRAVARIANT -> begin
true
end
| uu____921 -> begin
false
end))


let uu___is_INVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| INVARIANT -> begin
true
end
| uu____927 -> begin
false
end))


type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem


type cprob =
(FStar_Syntax_Syntax.comp, unit) FStar_TypeChecker_Common.problem


type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun uu___91_952 -> (match (uu___91_952) with
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

let uu____960 = (

let uu____961 = (FStar_Syntax_Subst.compress t)
in uu____961.FStar_Syntax_Syntax.n)
in (match (uu____960) with
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let uu____990 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____991 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "%s : %s" uu____990 uu____991)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty); FStar_Syntax_Syntax.pos = uu____994; FStar_Syntax_Syntax.vars = uu____995}, args) -> begin
(

let uu____1041 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____1042 = (FStar_Syntax_Print.term_to_string ty)
in (

let uu____1043 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "(%s : %s) %s" uu____1041 uu____1042 uu____1043))))
end
| uu____1044 -> begin
"--"
end))
in (

let uu____1045 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format3 "%s (%s)\t%s" compact uu____1045 detail)))))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env uu___92_1055 -> (match (uu___92_1055) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____1061 = (

let uu____1064 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1065 = (

let uu____1068 = (term_to_string p.FStar_TypeChecker_Common.lhs)
in (

let uu____1069 = (

let uu____1072 = (

let uu____1075 = (term_to_string p.FStar_TypeChecker_Common.rhs)
in (uu____1075)::[])
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::uu____1072)
in (uu____1068)::uu____1069))
in (uu____1064)::uu____1065))
in (FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____1061))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____1081 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1082 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____1083 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1081 uu____1082 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1083))))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env uu___93_1093 -> (match (uu___93_1093) with
| UNIV (u, t) -> begin
(

let x = (

let uu____1097 = (FStar_Options.hide_uvar_nums ())
in (match (uu____1097) with
| true -> begin
"?"
end
| uu____1098 -> begin
(

let uu____1099 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____1099 FStar_Util.string_of_int))
end))
in (

let uu____1100 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x uu____1100)))
end
| TERM ((u, uu____1102), t) -> begin
(

let x = (

let uu____1109 = (FStar_Options.hide_uvar_nums ())
in (match (uu____1109) with
| true -> begin
"?"
end
| uu____1110 -> begin
(

let uu____1111 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____1111 FStar_Util.string_of_int))
end))
in (

let uu____1112 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x uu____1112)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (

let uu____1127 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right uu____1127 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (

let uu____1141 = (

let uu____1144 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right uu____1144 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right uu____1141 (FStar_String.concat ", "))))


let args_to_string : 'Auu____1157 . (FStar_Syntax_Syntax.term * 'Auu____1157) Prims.list  ->  Prims.string = (fun args -> (

let uu____1175 = (FStar_All.pipe_right args (FStar_List.map (fun uu____1193 -> (match (uu____1193) with
| (x, uu____1199) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____1175 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> (

let uu____1207 = (

let uu____1208 = (FStar_Options.eager_inference ())
in (not (uu____1208)))
in {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = uu____1207; smt_ok = true; tcenv = env}))


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let uu___126_1230 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = uu___126_1230.wl_deferred; ctr = uu___126_1230.ctr; defer_ok = uu___126_1230.defer_ok; smt_ok = smt_ok; tcenv = uu___126_1230.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard : 'Auu____1247 . FStar_TypeChecker_Env.env  ->  ('Auu____1247 * FStar_TypeChecker_Common.prob) Prims.list  ->  worklist = (fun env g -> (

let uu___127_1270 = (empty_worklist env)
in (

let uu____1271 = (FStar_List.map FStar_Pervasives_Native.snd g)
in {attempting = uu____1271; wl_deferred = uu___127_1270.wl_deferred; ctr = uu___127_1270.ctr; defer_ok = false; smt_ok = uu___127_1270.smt_ok; tcenv = uu___127_1270.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu___128_1291 = wl
in {attempting = uu___128_1291.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = uu___128_1291.ctr; defer_ok = uu___128_1291.defer_ok; smt_ok = uu___128_1291.smt_ok; tcenv = uu___128_1291.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let uu___129_1312 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = uu___129_1312.wl_deferred; ctr = uu___129_1312.ctr; defer_ok = uu___129_1312.defer_ok; smt_ok = uu___129_1312.smt_ok; tcenv = uu___129_1312.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> ((

let uu____1329 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____1329) with
| true -> begin
(

let uu____1330 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1330))
end
| uu____1331 -> begin
()
end));
Failed (((prob), (reason)));
))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun uu___94_1336 -> (match (uu___94_1336) with
| FStar_TypeChecker_Common.EQ -> begin
FStar_TypeChecker_Common.EQ
end
| FStar_TypeChecker_Common.SUB -> begin
FStar_TypeChecker_Common.SUBINV
end
| FStar_TypeChecker_Common.SUBINV -> begin
FStar_TypeChecker_Common.SUB
end))


let invert : 'Auu____1343 'Auu____1344 . ('Auu____1343, 'Auu____1344) FStar_TypeChecker_Common.problem  ->  ('Auu____1343, 'Auu____1344) FStar_TypeChecker_Common.problem = (fun p -> (

let uu___130_1362 = p
in {FStar_TypeChecker_Common.pid = uu___130_1362.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = uu___130_1362.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___130_1362.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___130_1362.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___130_1362.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___130_1362.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___130_1362.FStar_TypeChecker_Common.rank}))


let maybe_invert : 'Auu____1373 'Auu____1374 . ('Auu____1373, 'Auu____1374) FStar_TypeChecker_Common.problem  ->  ('Auu____1373, 'Auu____1374) FStar_TypeChecker_Common.problem = (fun p -> (match ((Prims.op_Equality p.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUBINV)) with
| true -> begin
(invert p)
end
| uu____1392 -> begin
p
end))


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___95_1397 -> (match (uu___95_1397) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_18 -> FStar_TypeChecker_Common.TProb (_0_18)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_19 -> FStar_TypeChecker_Common.CProb (_0_19)))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel uu___96_1425 -> (match (uu___96_1425) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun uu___97_1430 -> (match (uu___97_1430) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun uu___98_1445 -> (match (uu___98_1445) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun uu___99_1462 -> (match (uu___99_1462) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun uu___100_1479 -> (match (uu___100_1479) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun uu___101_1498 -> (match (uu___101_1498) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let def_scope_wf : 'Auu____1521 . Prims.string  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.bv * 'Auu____1521) Prims.list  ->  unit = (fun msg rng r -> (

let uu____1549 = (

let uu____1550 = (FStar_Options.defensive ())
in (not (uu____1550)))
in (match (uu____1549) with
| true -> begin
()
end
| uu____1551 -> begin
(

let rec aux = (fun prev next -> (match (next) with
| [] -> begin
()
end
| ((bv, uu____1584))::bs -> begin
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


let def_check_scoped : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  unit = (fun msg prob phi -> (

let uu____1629 = (

let uu____1630 = (FStar_Options.defensive ())
in (not (uu____1630)))
in (match (uu____1629) with
| true -> begin
()
end
| uu____1631 -> begin
(

let uu____1632 = (

let uu____1635 = (p_scope prob)
in (FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst) uu____1635))
in (def_check_closed_in (p_loc prob) msg uu____1632 phi))
end)))


let def_check_prob : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  unit = (fun msg prob -> ((

let uu____1665 = (

let uu____1666 = (FStar_Options.defensive ())
in (not (uu____1666)))
in (match (uu____1665) with
| true -> begin
()
end
| uu____1667 -> begin
(

let uu____1668 = (p_scope prob)
in (def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1668))
end));
(

let uu____1676 = (FStar_All.pipe_left FStar_Pervasives_Native.fst (p_guard prob))
in (def_check_scoped (Prims.strcat msg ".guard") prob uu____1676));
(

let uu____1682 = (FStar_All.pipe_left FStar_Pervasives_Native.snd (p_guard prob))
in (def_check_scoped (Prims.strcat msg ".guard_type") prob uu____1682));
(match (prob) with
| FStar_TypeChecker_Common.TProb (p) -> begin
((def_check_scoped (Prims.strcat msg ".lhs") prob p.FStar_TypeChecker_Common.lhs);
(def_check_scoped (Prims.strcat msg ".rhs") prob p.FStar_TypeChecker_Common.rhs);
)
end
| uu____1693 -> begin
()
end);
))


let mk_eq2 : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun prob t1 t2 -> (

let uu____1714 = (FStar_Syntax_Util.type_u ())
in (match (uu____1714) with
| (t_type, u) -> begin
(

let uu____1721 = (

let uu____1726 = (p_scope prob)
in (new_uvar t1.FStar_Syntax_Syntax.pos uu____1726 t_type))
in (match (uu____1721) with
| (tt, uu____1728) -> begin
(FStar_Syntax_Util.mk_eq2 u tt t1 t2)
end))
end)))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___102_1733 -> (match (uu___102_1733) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _0_20 -> FStar_TypeChecker_Common.TProb (_0_20)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _0_21 -> FStar_TypeChecker_Common.CProb (_0_21)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> (

let uu____1757 = (FStar_All.pipe_right (p_reason p) FStar_List.length)
in (Prims.op_Equality uu____1757 (Prims.parse_int "1"))))


let next_pid : unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____1771 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
)))


let mk_problem : 'Auu____1995 'Auu____1996 . FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  'Auu____1995  ->  FStar_TypeChecker_Common.rel  ->  'Auu____1995  ->  'Auu____1996 FStar_Pervasives_Native.option  ->  Prims.string  ->  ('Auu____1995, 'Auu____1996) FStar_TypeChecker_Common.problem = (fun scope orig lhs rel rhs elt reason -> (

let uu____2040 = (next_pid ())
in (

let uu____2041 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____2040; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____2041; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})))


let new_problem : 'Auu____2064 'Auu____2065 . FStar_TypeChecker_Env.env  ->  'Auu____2064  ->  FStar_TypeChecker_Common.rel  ->  'Auu____2064  ->  'Auu____2065 FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  Prims.string  ->  ('Auu____2064, 'Auu____2065) FStar_TypeChecker_Common.problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (

let uu____2110 = (next_pid ())
in (

let uu____2111 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____2110; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____2111; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None}))))


let problem_using_guard : 'Auu____2132 'Auu____2133 . FStar_TypeChecker_Common.prob  ->  'Auu____2132  ->  FStar_TypeChecker_Common.rel  ->  'Auu____2132  ->  'Auu____2133 FStar_Pervasives_Native.option  ->  Prims.string  ->  ('Auu____2132, 'Auu____2133) FStar_TypeChecker_Common.problem = (fun orig lhs rel rhs elt reason -> (

let uu____2172 = (next_pid ())
in (

let uu____2173 = (p_scope orig)
in {FStar_TypeChecker_Common.pid = uu____2172; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = uu____2173; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})))


let guard_on_element : 'Auu____2184 . worklist  ->  ('Auu____2184, FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_TypeChecker_Common.problem  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun wl problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| FStar_Pervasives_Native.None -> begin
(

let u = (wl.tcenv.FStar_TypeChecker_Env.universe_of wl.tcenv x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Util.mk_forall u x phi))
end
| FStar_Pervasives_Native.Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (

let uu____2244 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____2244) with
| true -> begin
(

let uu____2245 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (

let uu____2246 = (prob_to_string env d)
in (

let uu____2247 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" uu____2245 uu____2246 uu____2247 s))))
end
| uu____2250 -> begin
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
| uu____2253 -> begin
(failwith "impossible")
end)
in (

let uu____2254 = (match (d1) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____2268 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (

let uu____2269 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((uu____2268), (uu____2269))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____2275 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (

let uu____2276 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((uu____2275), (uu____2276))))
end)
in (match (uu____2254) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___103_2294 -> (match (uu___103_2294) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Syntax_Unionfind.univ_union u u')
end
| uu____2306 -> begin
(FStar_Syntax_Unionfind.univ_change u t)
end)
end
| TERM ((u, uu____2308), t) -> begin
((def_check_closed t.FStar_Syntax_Syntax.pos "commit" t);
(FStar_Syntax_Util.set_uvar u t);
)
end)))))


let find_term_uvar : FStar_Syntax_Syntax.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun uv s -> (FStar_Util.find_map s (fun uu___104_2333 -> (match (uu___104_2333) with
| UNIV (uu____2336) -> begin
FStar_Pervasives_Native.None
end
| TERM ((u, uu____2342), t) -> begin
(

let uu____2348 = (FStar_Syntax_Unionfind.equiv uv u)
in (match (uu____2348) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____2351 -> begin
FStar_Pervasives_Native.None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe_uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun u s -> (FStar_Util.find_map s (fun uu___105_2372 -> (match (uu___105_2372) with
| UNIV (u', t) -> begin
(

let uu____2377 = (FStar_Syntax_Unionfind.univ_equiv u u')
in (match (uu____2377) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____2380 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____2381 -> begin
FStar_Pervasives_Native.None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____2392 = (

let uu____2393 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env uu____2393))
in (FStar_Syntax_Subst.compress uu____2392)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____2404 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress uu____2404)))


let norm_arg : 'Auu____2411 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * 'Auu____2411)  ->  (FStar_Syntax_Syntax.term * 'Auu____2411) = (fun env t -> (

let uu____2434 = (sn env (FStar_Pervasives_Native.fst t))
in ((uu____2434), ((FStar_Pervasives_Native.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____2469 -> (match (uu____2469) with
| (x, imp) -> begin
(

let uu____2480 = (

let uu___131_2481 = x
in (

let uu____2482 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___131_2481.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___131_2481.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2482}))
in ((uu____2480), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____2503 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____2503))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____2507 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____2507))
end
| uu____2510 -> begin
u2
end)))
in (

let uu____2511 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2511))))


let base_and_refinement_maybe_delta : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option) = (fun should_delta env t1 -> (

let norm_refinement = (fun env1 t -> (

let steps = (match (should_delta) with
| true -> begin
(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]
end
| uu____2557 -> begin
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
| uu____2636 -> begin
(

let uu____2637 = (norm_refinement env t12)
in (match (uu____2637) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x1, phi1); FStar_Syntax_Syntax.pos = uu____2654; FStar_Syntax_Syntax.vars = uu____2655} -> begin
((x1.FStar_Syntax_Syntax.sort), (FStar_Pervasives_Native.Some (((x1), (phi1)))))
end
| tt -> begin
(

let uu____2681 = (

let uu____2682 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____2683 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" uu____2682 uu____2683)))
in (failwith uu____2681))
end))
end)
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____2699 = (FStar_Syntax_Util.unfold_lazy i)
in (aux norm1 uu____2699))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____2700) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____2735 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____2737 = (

let uu____2738 = (FStar_Syntax_Subst.compress t1')
in uu____2738.FStar_Syntax_Syntax.n)
in (match (uu____2737) with
| FStar_Syntax_Syntax.Tm_refine (uu____2755) -> begin
(aux true t1')
end
| uu____2762 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2777) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____2806 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____2808 = (

let uu____2809 = (FStar_Syntax_Subst.compress t1')
in uu____2809.FStar_Syntax_Syntax.n)
in (match (uu____2808) with
| FStar_Syntax_Syntax.Tm_refine (uu____2826) -> begin
(aux true t1')
end
| uu____2833 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_app (uu____2848) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____2891 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____2893 = (

let uu____2894 = (FStar_Syntax_Subst.compress t1')
in uu____2894.FStar_Syntax_Syntax.n)
in (match (uu____2893) with
| FStar_Syntax_Syntax.Tm_refine (uu____2911) -> begin
(aux true t1')
end
| uu____2918 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_type (uu____2933) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_constant (uu____2948) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_name (uu____2963) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2978) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____2993) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_abs (uu____3020) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_quoted (uu____3051) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3072) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_let (uu____3103) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_match (uu____3130) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_meta (uu____3167) -> begin
(

let uu____3174 = (

let uu____3175 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3176 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3175 uu____3176)))
in (failwith uu____3174))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3191) -> begin
(

let uu____3218 = (

let uu____3219 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3220 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3219 uu____3220)))
in (failwith uu____3218))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____3235) -> begin
(

let uu____3260 = (

let uu____3261 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3262 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3261 uu____3262)))
in (failwith uu____3260))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____3277 = (

let uu____3278 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3279 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3278 uu____3279)))
in (failwith uu____3277))
end)))
in (

let uu____3294 = (whnf env t1)
in (aux false uu____3294)))))


let base_and_refinement : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option) = (fun env t -> (base_and_refinement_maybe_delta false env t))


let normalize_refinement : 'Auu____3325 . FStar_TypeChecker_Normalize.steps  ->  FStar_TypeChecker_Env.env  ->  'Auu____3325  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____3356 = (base_and_refinement env t)
in (FStar_All.pipe_right uu____3356 FStar_Pervasives_Native.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (

let uu____3392 = (FStar_Syntax_Syntax.null_bv t)
in ((uu____3392), (FStar_Syntax_Util.t_true))))


let as_refinement : 'Auu____3403 . Prims.bool  ->  FStar_TypeChecker_Env.env  ->  'Auu____3403  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun delta1 env wl t -> (

let uu____3428 = (base_and_refinement_maybe_delta delta1 env t)
in (match (uu____3428) with
| (t_base, refinement) -> begin
(match (refinement) with
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end
| FStar_Pervasives_Native.Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement : (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun uu____3509 -> (match (uu____3509) with
| (t_base, refopt) -> begin
(

let uu____3536 = (match (refopt) with
| FStar_Pervasives_Native.Some (y, phi) -> begin
((y), (phi))
end
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end)
in (match (uu____3536) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl prob -> (prob_to_string wl.tcenv prob))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (

let uu____3574 = (

let uu____3577 = (

let uu____3580 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____3603 -> (match (uu____3603) with
| (uu____3610, uu____3611, x) -> begin
x
end))))
in (FStar_List.append wl.attempting uu____3580))
in (FStar_List.map (wl_prob_to_string wl) uu____3577))
in (FStar_All.pipe_right uu____3574 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____3630 = (

let uu____3643 = (

let uu____3644 = (FStar_Syntax_Subst.compress k)
in uu____3644.FStar_Syntax_Syntax.n)
in (match (uu____3643) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((Prims.op_Equality (FStar_List.length bs) (FStar_List.length ys))) with
| true -> begin
(

let uu____3697 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (uu____3697)))
end
| uu____3710 -> begin
(

let uu____3711 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____3711) with
| (ys', t1, uu____3734) -> begin
(

let uu____3739 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t1))), (uu____3739)))
end))
end)
end
| uu____3780 -> begin
(

let uu____3781 = (

let uu____3792 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____3792)))
in ((((ys), (t))), (uu____3781)))
end))
in (match (uu____3630) with
| ((ys1, t1), (xs, c)) -> begin
(match ((Prims.op_disEquality (FStar_List.length xs) (FStar_List.length ys1))) with
| true -> begin
(FStar_Syntax_Util.abs ys1 t1 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None []))))
end
| uu____3839 -> begin
(

let c1 = (

let uu____3841 = (FStar_Syntax_Util.rename_binders xs ys1)
in (FStar_Syntax_Subst.subst_comp uu____3841 c))
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

let uu____3880 = (p_guard prob)
in (match (uu____3880) with
| (uu____3885, uv) -> begin
((

let uu____3888 = (

let uu____3889 = (FStar_Syntax_Subst.compress uv)
in uu____3889.FStar_Syntax_Syntax.n)
in (match (uu____3888) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi1 = (u_abs k bs phi)
in ((

let uu____3921 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____3921) with
| true -> begin
(

let uu____3922 = (FStar_Util.string_of_int (p_pid prob))
in (

let uu____3923 = (FStar_Syntax_Print.term_to_string uv)
in (

let uu____3924 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" uu____3922 uu____3923 uu____3924))))
end
| uu____3925 -> begin
()
end));
(def_check_closed (p_loc prob) "solve_prob\'" phi1);
(FStar_Syntax_Util.set_uvar uvar phi1);
)))
end
| uu____3927 -> begin
(match ((not (resolve_ok))) with
| true -> begin
(failwith "Impossible: this instance has already been assigned a solution")
end
| uu____3928 -> begin
()
end)
end));
(commit uvis);
(

let uu___132_3930 = wl
in {attempting = uu___132_3930.attempting; wl_deferred = uu___132_3930.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___132_3930.defer_ok; smt_ok = uu___132_3930.smt_ok; tcenv = uu___132_3930.tcenv});
)
end)));
))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____3951 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____3951) with
| true -> begin
(

let uu____3952 = (FStar_Util.string_of_int pid)
in (

let uu____3953 = (

let uu____3954 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right uu____3954 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____3952 uu____3953)))
end
| uu____3959 -> begin
()
end));
(commit sol);
(

let uu___133_3961 = wl
in {attempting = uu___133_3961.attempting; wl_deferred = uu___133_3961.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___133_3961.defer_ok; smt_ok = uu___133_3961.smt_ok; tcenv = uu___133_3961.tcenv});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> ((def_check_prob "solve_prob.prob" prob);
(FStar_Util.iter_opt logical_guard (def_check_scoped "solve_prob.guard" prob));
(

let conj_guard1 = (fun t g -> (match (((t), (g))) with
| (uu____4013, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (FStar_Pervasives_Native.None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
FStar_Pervasives_Native.Some (f)
end
| (FStar_Pervasives_Native.Some (t1), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(

let uu____4025 = (FStar_Syntax_Util.mk_conj t1 f)
in FStar_Pervasives_Native.Some (uu____4025))
end))
in ((

let uu____4031 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____4031) with
| true -> begin
(

let uu____4032 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (

let uu____4033 = (

let uu____4034 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right uu____4034 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____4032 uu____4033)))
end
| uu____4039 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
));
))


let rec occurs : 'b . worklist  ->  (FStar_Syntax_Syntax.uvar * 'b)  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun wl uk t -> (

let uu____4073 = (

let uu____4080 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right uu____4080 FStar_Util.set_elements))
in (FStar_All.pipe_right uu____4073 (FStar_Util.for_some (fun uu____4116 -> (match (uu____4116) with
| (uv, uu____4122) -> begin
(FStar_Syntax_Unionfind.equiv uv (FStar_Pervasives_Native.fst uk))
end))))))


let occurs_check : 'Auu____4135 'Auu____4136 . 'Auu____4135  ->  worklist  ->  (FStar_Syntax_Syntax.uvar * 'Auu____4136)  ->  FStar_Syntax_Syntax.typ  ->  (Prims.bool * Prims.string FStar_Pervasives_Native.option) = (fun env wl uk t -> (

let occurs_ok = (

let uu____4172 = (occurs wl uk t)
in (not (uu____4172)))
in (

let msg = (match (occurs_ok) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4178 -> begin
(

let uu____4179 = (

let uu____4180 = (FStar_Syntax_Print.uvar_to_string (FStar_Pervasives_Native.fst uk))
in (

let uu____4181 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" uu____4180 uu____4181)))
in FStar_Pervasives_Native.Some (uu____4179))
end)
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check : 'Auu____4198 'Auu____4199 . 'Auu____4198  ->  worklist  ->  (FStar_Syntax_Syntax.uvar * 'Auu____4199)  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.term  ->  (Prims.bool * Prims.bool * (Prims.string FStar_Pervasives_Native.option * FStar_Syntax_Syntax.bv FStar_Util.set * FStar_Syntax_Syntax.bv FStar_Util.set)) = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let uu____4258 = (occurs_check env wl uk t)
in (match (uu____4258) with
| (occurs_ok, msg) -> begin
(

let uu____4289 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (uu____4289), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars : 'Auu____4316 'Auu____4317 . (FStar_Syntax_Syntax.bv * 'Auu____4316) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____4317) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____4317) Prims.list = (fun v1 v2 -> (

let as_set1 = (fun v3 -> (FStar_All.pipe_right v3 (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set1 v1)
in (

let uu____4405 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____4459 uu____4460 -> (match (((uu____4459), (uu____4460))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____4541 = (

let uu____4542 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation uu____4542))
in (match (uu____4541) with
| true -> begin
((isect), (isect_set))
end
| uu____4563 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____4567 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____4567) with
| true -> begin
(

let uu____4580 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (uu____4580)))
end
| uu____4595 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (uu____4405) with
| (isect, uu____4621) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq : 'Auu____4650 'Auu____4651 . (FStar_Syntax_Syntax.bv * 'Auu____4650) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____4651) Prims.list  ->  Prims.bool = (fun v1 v2 -> ((Prims.op_Equality (FStar_List.length v1) (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____4708 uu____4709 -> (match (((uu____4708), (uu____4709))) with
| ((a, uu____4727), (b, uu____4729)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt : 'Auu____4748 'Auu____4749 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____4748) Prims.list  ->  (FStar_Syntax_Syntax.term * 'Auu____4749)  ->  (FStar_Syntax_Syntax.bv * 'Auu____4749) FStar_Pervasives_Native.option = (fun env seen arg -> (

let hd1 = (norm_arg env arg)
in (match ((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(

let uu____4803 = (FStar_All.pipe_right seen (FStar_Util.for_some (fun uu____4817 -> (match (uu____4817) with
| (b, uu____4823) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end))))
in (match (uu____4803) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4834 -> begin
FStar_Pervasives_Native.Some (((a), ((FStar_Pervasives_Native.snd hd1))))
end))
end
| uu____4839 -> begin
FStar_Pervasives_Native.None
end)))


let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option = (fun env seen args -> (match (args) with
| [] -> begin
FStar_Pervasives_Native.Some ((FStar_List.rev seen))
end
| (hd1)::rest -> begin
(

let uu____4918 = (pat_var_opt env seen hd1)
in (match (uu____4918) with
| FStar_Pervasives_Native.None -> begin
((

let uu____4932 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____4932) with
| true -> begin
(

let uu____4933 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (FStar_Pervasives_Native.fst hd1))
in (FStar_Util.print1 "Not a pattern: %s\n" uu____4933))
end
| uu____4934 -> begin
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

let uu____4953 = (

let uu____4954 = (FStar_Syntax_Subst.compress t)
in uu____4954.FStar_Syntax_Syntax.n)
in (match (uu____4953) with
| FStar_Syntax_Syntax.Tm_uvar (uu____4957) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____4974); FStar_Syntax_Syntax.pos = uu____4975; FStar_Syntax_Syntax.vars = uu____4976}, uu____4977) -> begin
true
end
| uu____5014 -> begin
false
end)))


let destruct_flex_t : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.pos = uu____5140; FStar_Syntax_Syntax.vars = uu____5141}, args) -> begin
((t), (uv), (k), (args))
end
| uu____5209 -> begin
(failwith "Not a flex-uvar")
end))


let destruct_flex_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) * FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option) = (fun env t -> (

let uu____5290 = (destruct_flex_t t)
in (match (uu____5290) with
| (t1, uv, k, args) -> begin
(

let uu____5405 = (pat_vars env [] args)
in (match (uu____5405) with
| FStar_Pervasives_Native.Some (vars) -> begin
((((t1), (uv), (k), (args))), (FStar_Pervasives_Native.Some (vars)))
end
| uu____5503 -> begin
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
| uu____5587 -> begin
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
| uu____5624 -> begin
false
end))


let uu___is_FullMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullMatch -> begin
true
end
| uu____5630 -> begin
false
end))


let string_of_option : 'Auu____5637 . ('Auu____5637  ->  Prims.string)  ->  'Auu____5637 FStar_Pervasives_Native.option  ->  Prims.string = (fun f uu___106_5652 -> (match (uu___106_5652) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____5658 = (f x)
in (Prims.strcat "Some " uu____5658))
end))


let string_of_match_result : match_result  ->  Prims.string = (fun uu___107_5663 -> (match (uu___107_5663) with
| MisMatch (d1, d2) -> begin
(

let uu____5674 = (

let uu____5675 = (string_of_option FStar_Syntax_Print.delta_depth_to_string d1)
in (

let uu____5676 = (

let uu____5677 = (

let uu____5678 = (string_of_option FStar_Syntax_Print.delta_depth_to_string d2)
in (Prims.strcat uu____5678 ")"))
in (Prims.strcat ") (" uu____5677))
in (Prims.strcat uu____5675 uu____5676)))
in (Prims.strcat "MisMatch (" uu____5674))
end
| HeadMatch -> begin
"HeadMatch"
end
| FullMatch -> begin
"FullMatch"
end))


let head_match : match_result  ->  match_result = (fun uu___108_5683 -> (match (uu___108_5683) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____5698 -> begin
HeadMatch
end))


let and_match : match_result  ->  (unit  ->  match_result)  ->  match_result = (fun m1 m2 -> (match (m1) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| HeadMatch -> begin
(

let uu____5728 = (m2 ())
in (match (uu____5728) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____5743 -> begin
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
| uu____5755 -> begin
FStar_Syntax_Syntax.delta_constant
end)
end
| FStar_Syntax_Syntax.Delta_constant_at_level (i) when (i > (Prims.parse_int "0")) -> begin
(

let uu____5757 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5757) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Syntax.delta_constant
end
| uu____5768 -> begin
fv.FStar_Syntax_Syntax.fv_delta
end))
end
| d -> begin
d
end))


let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____5791) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____5800) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____5828 = (FStar_Syntax_Util.unfold_lazy i)
in (delta_depth_of_term env uu____5828))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_bvar (uu____5829) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_name (uu____5830) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uvar (uu____5831) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_let (uu____5848) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_match (uu____5861) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____5885) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____5891, uu____5892) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____5934) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____5955; FStar_Syntax_Syntax.index = uu____5956; FStar_Syntax_Syntax.sort = t2}, uu____5958) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_constant (uu____5965) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)
end
| FStar_Syntax_Syntax.Tm_type (uu____5966) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____5967) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____5980) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)
end
| FStar_Syntax_Syntax.Tm_abs (uu____5987) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.delta_constant)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____6005 = (fv_delta_depth env fv)
in FStar_Pervasives_Native.Some (uu____6005))
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
| uu____6025 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____6032 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____6032) with
| true -> begin
FullMatch
end
| uu____6033 -> begin
(

let uu____6034 = (

let uu____6043 = (

let uu____6046 = (fv_delta_depth env f)
in FStar_Pervasives_Native.Some (uu____6046))
in (

let uu____6047 = (

let uu____6050 = (fv_delta_depth env g)
in FStar_Pervasives_Native.Some (uu____6050))
in ((uu____6043), (uu____6047))))
in MisMatch (uu____6034))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____6056), FStar_Syntax_Syntax.Tm_uinst (g, uu____6058)) -> begin
(

let uu____6067 = (head_matches env f g)
in (FStar_All.pipe_right uu____6067 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____6070 = (FStar_Const.eq_const c d)
in (match (uu____6070) with
| true -> begin
FullMatch
end
| uu____6071 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, uu____6077), FStar_Syntax_Syntax.Tm_uvar (uv', uu____6079)) -> begin
(

let uu____6128 = (FStar_Syntax_Unionfind.equiv uv uv')
in (match (uu____6128) with
| true -> begin
FullMatch
end
| uu____6129 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____6135), FStar_Syntax_Syntax.Tm_refine (y, uu____6137)) -> begin
(

let uu____6146 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____6146 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____6148), uu____6149) -> begin
(

let uu____6154 = (head_matches env x.FStar_Syntax_Syntax.sort t21)
in (FStar_All.pipe_right uu____6154 head_match))
end
| (uu____6155, FStar_Syntax_Syntax.Tm_refine (x, uu____6157)) -> begin
(

let uu____6162 = (head_matches env t11 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____6162 head_match))
end
| (FStar_Syntax_Syntax.Tm_type (uu____6163), FStar_Syntax_Syntax.Tm_type (uu____6164)) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_arrow (uu____6165), FStar_Syntax_Syntax.Tm_arrow (uu____6166)) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____6192), FStar_Syntax_Syntax.Tm_app (head', uu____6194)) -> begin
(

let uu____6235 = (head_matches env head1 head')
in (FStar_All.pipe_right uu____6235 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____6237), uu____6238) -> begin
(

let uu____6259 = (head_matches env head1 t21)
in (FStar_All.pipe_right uu____6259 head_match))
end
| (uu____6260, FStar_Syntax_Syntax.Tm_app (head1, uu____6262)) -> begin
(

let uu____6283 = (head_matches env t11 head1)
in (FStar_All.pipe_right uu____6283 head_match))
end
| uu____6284 -> begin
(

let uu____6289 = (

let uu____6298 = (delta_depth_of_term env t11)
in (

let uu____6301 = (delta_depth_of_term env t21)
in ((uu____6298), (uu____6301))))
in MisMatch (uu____6289))
end))))


let head_matches_delta : 'Auu____6318 . FStar_TypeChecker_Env.env  ->  'Auu____6318  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (match_result * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) FStar_Pervasives_Native.option) = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let uu____6357 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____6357) with
| (head1, uu____6375) -> begin
(

let uu____6396 = (

let uu____6397 = (FStar_Syntax_Util.un_uinst head1)
in uu____6397.FStar_Syntax_Syntax.n)
in (match (uu____6396) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____6403 = (

let uu____6404 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____6404 FStar_Option.isSome))
in (match (uu____6403) with
| true -> begin
(

let uu____6423 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right uu____6423 (fun _0_22 -> FStar_Pervasives_Native.Some (_0_22))))
end
| uu____6426 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____6427 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (

let success = (fun d r t11 t21 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (((t11), (t21)))
end
| uu____6475 -> begin
FStar_Pervasives_Native.None
end))))
in (

let fail1 = (fun r -> ((r), (FStar_Pervasives_Native.None)))
in (

let rec aux = (fun retry n_delta t11 t21 -> (

let r = (head_matches env t11 t21)
in (

let reduce_one_and_try_again = (fun d1 d2 -> (

let d1_greater_than_d2 = (FStar_TypeChecker_Common.delta_depth_greater_than d1 d2)
in (

let uu____6560 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env wl t11)
in ((t1'), (t21)))
end
| uu____6570 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env wl t21)
in ((t11), (t2')))
end)
in (match (uu____6560) with
| (t12, t22) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
end))))
in (

let reduce_both_and_try_again = (fun d r1 -> (

let uu____6605 = (FStar_TypeChecker_Common.decr_delta_depth d)
in (match (uu____6605) with
| FStar_Pervasives_Native.None -> begin
(fail1 r1)
end
| FStar_Pervasives_Native.Some (d1) -> begin
(

let t12 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env wl t11)
in (

let t22 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env wl t21)
in (aux retry (n_delta + (Prims.parse_int "1")) t12 t22)))
end)))
in (match (r) with
| MisMatch (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational_at_level (i)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational_at_level (j))) when (((i > (Prims.parse_int "1")) || (j > (Prims.parse_int "1"))) && (Prims.op_disEquality i j)) -> begin
(reduce_one_and_try_again (FStar_Syntax_Syntax.Delta_equational_at_level (i)) (FStar_Syntax_Syntax.Delta_equational_at_level (j)))
end
| MisMatch (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational_at_level (uu____6637)), uu____6638) -> begin
(match ((not (retry))) with
| true -> begin
(fail1 r)
end
| uu____6655 -> begin
(

let uu____6656 = (

let uu____6665 = (maybe_inline t11)
in (

let uu____6668 = (maybe_inline t21)
in ((uu____6665), (uu____6668))))
in (match (uu____6656) with
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
| MisMatch (uu____6705, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational_at_level (uu____6706))) -> begin
(match ((not (retry))) with
| true -> begin
(fail1 r)
end
| uu____6723 -> begin
(

let uu____6724 = (

let uu____6733 = (maybe_inline t11)
in (

let uu____6736 = (maybe_inline t21)
in ((uu____6733), (uu____6736))))
in (match (uu____6724) with
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
(reduce_both_and_try_again d1 r)
end
| MisMatch (FStar_Pervasives_Native.Some (d1), FStar_Pervasives_Native.Some (d2)) -> begin
(reduce_one_and_try_again d1 d2)
end
| MisMatch (uu____6785) -> begin
(fail1 r)
end
| uu____6794 -> begin
(success n_delta r t11 t21)
end)))))
in (

let r = (aux true (Prims.parse_int "0") t1 t2)
in ((

let uu____6807 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelDelta")))
in (match (uu____6807) with
| true -> begin
(

let uu____6808 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6809 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____6810 = (string_of_match_result (FStar_Pervasives_Native.fst r))
in (

let uu____6817 = (match ((Prims.op_Equality (FStar_Pervasives_Native.snd r) FStar_Pervasives_Native.None)) with
| true -> begin
"None"
end
| uu____6834 -> begin
(

let uu____6835 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd r) FStar_Util.must)
in (FStar_All.pipe_right uu____6835 (fun uu____6869 -> (match (uu____6869) with
| (t11, t21) -> begin
(

let uu____6876 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____6877 = (

let uu____6878 = (FStar_Syntax_Print.term_to_string t21)
in (Prims.strcat "; " uu____6878))
in (Prims.strcat uu____6876 uu____6877)))
end))))
end)
in (FStar_Util.print4 "head_matches (%s, %s) = %s (%s)\n" uu____6808 uu____6809 uu____6810 uu____6817)))))
end
| uu____6879 -> begin
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
| uu____6918 -> begin
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
| uu____6962 -> begin
false
end))


let __proj__C__item___0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_0) -> begin
_0
end))


type tcs =
tc Prims.list


let tc_to_string : tc  ->  Prims.string = (fun uu___109_6976 -> (match (uu___109_6976) with
| T (t, uu____6978) -> begin
(term_to_string t)
end
| C (c) -> begin
(FStar_Syntax_Print.comp_to_string c)
end))


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____7002 = (FStar_Syntax_Util.type_u ())
in (match (uu____7002) with
| (t, uu____7008) -> begin
(

let uu____7009 = (new_uvar r binders t)
in (FStar_Pervasives_Native.fst uu____7009))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____7024 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____7024 FStar_Pervasives_Native.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * variance * tc) Prims.list) = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (

let uu____7098 = (head_matches env t1 t')
in (match (uu____7098) with
| MisMatch (uu____7099) -> begin
false
end
| uu____7108 -> begin
true
end)))
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let rebuild = (fun args' -> (

let args1 = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((uu____7208, imp), T (t2, uu____7211)) -> begin
((t2), (imp))
end
| uu____7234 -> begin
(failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd1), (args1)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun uu____7301 -> (match (uu____7301) with
| (t2, uu____7315) -> begin
((FStar_Pervasives_Native.None), (INVARIANT), (T (((t2), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____7362 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7362) with
| (bs1, c1) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs2 tcs1 -> (match (((bs2), (tcs1))) with
| (((x, imp))::bs3, (T (t2, uu____7447))::tcs2) -> begin
(aux (((((

let uu___134_7486 = x
in {FStar_Syntax_Syntax.ppname = uu___134_7486.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___134_7486.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (imp)))::out) bs3 tcs2)
end
| ([], (C (c2))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c2)
end
| uu____7504 -> begin
(failwith "Bad reconstruction")
end))
in (aux [] bs1 tcs)))
in (

let rec decompose1 = (fun out uu___110_7561 -> (match (uu___110_7561) with
| [] -> begin
(FStar_List.rev ((((FStar_Pervasives_Native.None), (COVARIANT), (C (c1))))::out))
end
| (hd1)::rest -> begin
(decompose1 ((((FStar_Pervasives_Native.Some (hd1)), (CONTRAVARIANT), (T ((((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (

let uu____7680 = (decompose1 [] bs1)
in ((rebuild), (matches), (uu____7680)))))
end))
end
| uu____7731 -> begin
(

let rebuild = (fun uu___111_7739 -> (match (uu___111_7739) with
| [] -> begin
t1
end
| uu____7742 -> begin
(failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t2 -> (FStar_Util.return_all true))), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun uu___112_7777 -> (match (uu___112_7777) with
| T (t, uu____7779) -> begin
t
end
| uu____7792 -> begin
(failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun uu___113_7797 -> (match (uu___113_7797) with
| T (t, uu____7799) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| uu____7812 -> begin
(failwith "Impossible")
end))


let imitation_sub_probs : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * variance * tc) Prims.list  ->  (FStar_TypeChecker_Common.prob Prims.list * tc Prims.list * FStar_Syntax_Syntax.formula) = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope1 args q -> (match (q) with
| (uu____7944, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope1 r)
in (

let uu____7973 = (new_uvar r scope1 k)
in (match (uu____7973) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| uu____7991 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) FStar_Pervasives_Native.None r)
end)
in (

let uu____8008 = (

let uu____8009 = (mk_problem scope1 orig gi_ps (vary_rel rel variance) ti FStar_Pervasives_Native.None "type subterm")
in (FStar_All.pipe_left (fun _0_23 -> FStar_TypeChecker_Common.TProb (_0_23)) uu____8009))
in ((T (((gi_xs), (mk_kind)))), (uu____8008))))
end)))
end
| (uu____8024, uu____8025, C (uu____8026)) -> begin
(failwith "impos")
end))
in (

let rec aux = (fun scope1 args qs1 -> (match (qs1) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs2 -> begin
(

let uu____8179 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.pos = uu____8196; FStar_Syntax_Syntax.vars = uu____8197})) -> begin
(

let uu____8220 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____8220) with
| (T (gi_xs, uu____8246), prob) -> begin
(

let uu____8260 = (

let uu____8261 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_24 -> C (_0_24)) uu____8261))
in ((uu____8260), ((prob)::[])))
end
| uu____8264 -> begin
(failwith "impossible")
end))
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.pos = uu____8279; FStar_Syntax_Syntax.vars = uu____8280})) -> begin
(

let uu____8303 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____8303) with
| (T (gi_xs, uu____8329), prob) -> begin
(

let uu____8343 = (

let uu____8344 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_25 -> C (_0_25)) uu____8344))
in ((uu____8343), ((prob)::[])))
end
| uu____8347 -> begin
(failwith "impossible")
end))
end
| (uu____8358, uu____8359, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.pos = uu____8361; FStar_Syntax_Syntax.vars = uu____8362})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((FStar_Pervasives_Native.None), (INVARIANT), (T ((((FStar_Pervasives_Native.fst t)), (generic_kind))))))))
in (

let components1 = (((FStar_Pervasives_Native.None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let uu____8497 = (

let uu____8506 = (FStar_List.map (sub_prob scope1 args) components1)
in (FStar_All.pipe_right uu____8506 FStar_List.unzip))
in (match (uu____8497) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (

let uu____8560 = (

let uu____8561 = (

let uu____8564 = (FStar_List.hd tcs)
in (FStar_All.pipe_right uu____8564 un_T))
in (

let uu____8565 = (

let uu____8574 = (FStar_List.tl tcs)
in (FStar_All.pipe_right uu____8574 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____8561; FStar_Syntax_Syntax.effect_args = uu____8565; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____8560))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| uu____8583 -> begin
(

let uu____8596 = (sub_prob scope1 args q)
in (match (uu____8596) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (uu____8179) with
| (tc, probs) -> begin
(

let uu____8627 = (match (((q), (tc))) with
| ((FStar_Pervasives_Native.Some (b, imp), uu____8690, uu____8691), T (t, uu____8693)) -> begin
(

let b1 = (((

let uu___135_8734 = b
in {FStar_Syntax_Syntax.ppname = uu___135_8734.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___135_8734.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let uu____8735 = (

let uu____8742 = (FStar_Syntax_Util.arg_of_non_null_binder b1)
in (uu____8742)::args)
in ((FStar_Pervasives_Native.Some (b1)), ((b1)::scope1), (uu____8735))))
end
| uu____8777 -> begin
((FStar_Pervasives_Native.None), (scope1), (args))
end)
in (match (uu____8627) with
| (bopt, scope2, args1) -> begin
(

let uu____8861 = (aux scope2 args1 qs2)
in (match (uu____8861) with
| (sub_probs, tcs, f) -> begin
(

let f1 = (match (bopt) with
| FStar_Pervasives_Native.None -> begin
(

let f1 = (

let uu____8899 = (

let uu____8902 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst))))
in (f)::uu____8902)
in (FStar_Syntax_Util.mk_conj_l uu____8899))
in ((def_check_closed (p_loc orig) "imitation_sub_probs (1)" f1);
f1;
))
end
| FStar_Pervasives_Native.Some (b) -> begin
(

let u_b = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (

let f1 = (

let uu____8927 = (

let uu____8930 = (FStar_Syntax_Util.mk_forall u_b (FStar_Pervasives_Native.fst b) f)
in (

let uu____8931 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst))))
in (uu____8930)::uu____8931))
in (FStar_Syntax_Util.mk_conj_l uu____8927))
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


let compress_tprob : 'Auu____9005 . worklist  ->  (FStar_Syntax_Syntax.term, 'Auu____9005) FStar_TypeChecker_Common.problem  ->  (FStar_Syntax_Syntax.term, 'Auu____9005) FStar_TypeChecker_Common.problem = (fun wl p -> (

let uu___136_9028 = p
in (

let uu____9033 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____9034 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___136_9028.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____9033; FStar_TypeChecker_Common.relation = uu___136_9028.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____9034; FStar_TypeChecker_Common.element = uu___136_9028.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___136_9028.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___136_9028.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___136_9028.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___136_9028.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___136_9028.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p1) -> begin
(

let uu____9050 = (compress_tprob wl p1)
in (FStar_All.pipe_right uu____9050 (fun _0_26 -> FStar_TypeChecker_Common.TProb (_0_26))))
end
| FStar_TypeChecker_Common.CProb (uu____9059) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (

let uu____9083 = (compress_prob wl pr)
in (FStar_All.pipe_right uu____9083 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____9093 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____9093) with
| (lh, uu____9113) -> begin
(

let uu____9134 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____9134) with
| (rh, uu____9154) -> begin
(

let uu____9175 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____9192), FStar_Syntax_Syntax.Tm_uvar (uu____9193)) -> begin
((flex_flex), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____9230), uu____9231) when ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (uu____9252, FStar_Syntax_Syntax.Tm_uvar (uu____9253)) when ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____9274), uu____9275) -> begin
(

let uu____9292 = (base_and_refinement wl.tcenv tp.FStar_TypeChecker_Common.rhs)
in (match (uu____9292) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
((flex_rigid), (tp))
end
| uu____9341 -> begin
(

let rank = (

let uu____9349 = (is_top_level_prob prob)
in (match (uu____9349) with
| true -> begin
flex_refine
end
| uu____9350 -> begin
flex_refine_inner
end))
in (

let uu____9351 = (

let uu___137_9356 = tp
in (

let uu____9361 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___137_9356.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___137_9356.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___137_9356.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____9361; FStar_TypeChecker_Common.element = uu___137_9356.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___137_9356.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___137_9356.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___137_9356.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___137_9356.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___137_9356.FStar_TypeChecker_Common.rank}))
in ((rank), (uu____9351))))
end)
end))
end
| (uu____9372, FStar_Syntax_Syntax.Tm_uvar (uu____9373)) -> begin
(

let uu____9390 = (base_and_refinement wl.tcenv tp.FStar_TypeChecker_Common.lhs)
in (match (uu____9390) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
((rigid_flex), (tp))
end
| uu____9439 -> begin
(

let uu____9446 = (

let uu___138_9453 = tp
in (

let uu____9458 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___138_9453.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____9458; FStar_TypeChecker_Common.relation = uu___138_9453.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___138_9453.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___138_9453.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___138_9453.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___138_9453.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___138_9453.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___138_9453.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___138_9453.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (uu____9446)))
end)
end))
end
| (uu____9475, uu____9476) -> begin
((rigid_rigid), (tp))
end)
in (match (uu____9175) with
| (rank, tp1) -> begin
(

let uu____9495 = (FStar_All.pipe_right (

let uu___139_9501 = tp1
in {FStar_TypeChecker_Common.pid = uu___139_9501.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___139_9501.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___139_9501.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___139_9501.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___139_9501.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___139_9501.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___139_9501.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___139_9501.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___139_9501.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rank)}) (fun _0_27 -> FStar_TypeChecker_Common.TProb (_0_27)))
in ((rank), (uu____9495)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____9511 = (FStar_All.pipe_right (

let uu___140_9517 = cp
in {FStar_TypeChecker_Common.pid = uu___140_9517.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___140_9517.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___140_9517.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___140_9517.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___140_9517.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___140_9517.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___140_9517.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___140_9517.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___140_9517.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rigid_rigid)}) (fun _0_28 -> FStar_TypeChecker_Common.CProb (_0_28)))
in ((rigid_rigid), (uu____9511)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun uu____9578 probs -> (match (uu____9578) with
| (min_rank, min1, out) -> begin
(match (probs) with
| [] -> begin
((min1), (out), (min_rank))
end
| (hd1)::tl1 -> begin
(

let uu____9631 = (rank wl hd1)
in (match (uu____9631) with
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
| uu____9677 -> begin
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
| uu____9707 -> begin
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
| uu____9747 -> begin
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
| uu____9761 -> begin
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
| uu____9775 -> begin
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

let uu____9827 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____9827) with
| (k, uu____9833) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Syntax_Unionfind.univ_equiv v1 v2)
end
| uu____9843 -> begin
false
end)
end)))))
end
| uu____9844 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (

let rec filter_out_common_univs = (fun u12 u22 -> (

let common_elts = (FStar_All.pipe_right u12 (FStar_List.fold_left (fun uvs uv1 -> (

let uu____9896 = (FStar_All.pipe_right u22 (FStar_List.existsML (fun uv2 -> (

let uu____9902 = (FStar_Syntax_Util.compare_univs uv1 uv2)
in (Prims.op_Equality uu____9902 (Prims.parse_int "0"))))))
in (match (uu____9896) with
| true -> begin
(uv1)::uvs
end
| uu____9905 -> begin
uvs
end))) []))
in (

let filter1 = (FStar_List.filter (fun u -> (

let uu____9918 = (FStar_All.pipe_right common_elts (FStar_List.existsML (fun u' -> (

let uu____9924 = (FStar_Syntax_Util.compare_univs u u')
in (Prims.op_Equality uu____9924 (Prims.parse_int "0"))))))
in (not (uu____9918)))))
in (

let uu____9925 = (filter1 u12)
in (

let uu____9928 = (filter1 u22)
in ((uu____9925), (uu____9928)))))))
in (

let try_umax_components = (fun u12 u22 msg -> (match (((u12), (u22))) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(

let uu____9957 = (filter_out_common_univs us1 us2)
in (match (uu____9957) with
| (us11, us21) -> begin
(match ((Prims.op_Equality (FStar_List.length us11) (FStar_List.length us21))) with
| true -> begin
(

let rec aux = (fun wl1 us12 us22 -> (match (((us12), (us22))) with
| ((u13)::us13, (u23)::us23) -> begin
(

let uu____10016 = (really_solve_universe_eq pid_orig wl1 u13 u23)
in (match (uu____10016) with
| USolved (wl2) -> begin
(aux wl2 us13 us23)
end
| failed -> begin
failed
end))
end
| uu____10019 -> begin
USolved (wl1)
end))
in (aux wl us11 us21))
end
| uu____10028 -> begin
(

let uu____10029 = (

let uu____10030 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____10031 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" uu____10030 uu____10031)))
in UFailed (uu____10029))
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

let uu____10055 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____10055) with
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

let uu____10081 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____10081) with
| USolved (wl2) -> begin
(aux wl2 us2)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____10084 -> begin
(

let uu____10089 = (

let uu____10090 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____10091 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" uu____10090 uu____10091 msg)))
in UFailed (uu____10089))
end))
in (match (((u11), (u21))) with
| (FStar_Syntax_Syntax.U_bvar (uu____10092), uu____10093) -> begin
(

let uu____10094 = (

let uu____10095 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____10096 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____10095 uu____10096)))
in (failwith uu____10094))
end
| (FStar_Syntax_Syntax.U_unknown, uu____10097) -> begin
(

let uu____10098 = (

let uu____10099 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____10100 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____10099 uu____10100)))
in (failwith uu____10098))
end
| (uu____10101, FStar_Syntax_Syntax.U_bvar (uu____10102)) -> begin
(

let uu____10103 = (

let uu____10104 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____10105 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____10104 uu____10105)))
in (failwith uu____10103))
end
| (uu____10106, FStar_Syntax_Syntax.U_unknown) -> begin
(

let uu____10107 = (

let uu____10108 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____10109 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____10108 uu____10109)))
in (failwith uu____10107))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____10112 -> begin
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

let uu____10133 = (FStar_Syntax_Unionfind.univ_equiv v1 v2)
in (match (uu____10133) with
| true -> begin
USolved (wl)
end
| uu____10134 -> begin
(

let wl1 = (extend_solution pid_orig ((UNIV (((v1), (u21))))::[]) wl)
in USolved (wl1))
end))
end
| (FStar_Syntax_Syntax.U_unif (v1), u) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____10155 = (occurs_univ v1 u3)
in (match (uu____10155) with
| true -> begin
(

let uu____10156 = (

let uu____10157 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____10158 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____10157 uu____10158)))
in (try_umax_components u11 u21 uu____10156))
end
| uu____10159 -> begin
(

let uu____10160 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____10160))
end)))
end
| (u, FStar_Syntax_Syntax.U_unif (v1)) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____10180 = (occurs_univ v1 u3)
in (match (uu____10180) with
| true -> begin
(

let uu____10181 = (

let uu____10182 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____10183 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____10182 uu____10183)))
in (try_umax_components u11 u21 uu____10181))
end
| uu____10184 -> begin
(

let uu____10185 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____10185))
end)))
end
| (FStar_Syntax_Syntax.U_max (uu____10194), uu____10195) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____10198 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____10201 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____10201) with
| true -> begin
USolved (wl)
end
| uu____10202 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (uu____10203, FStar_Syntax_Syntax.U_max (uu____10204)) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____10207 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____10210 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____10210) with
| true -> begin
USolved (wl)
end
| uu____10211 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (FStar_Syntax_Syntax.U_succ (uu____10212), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_succ (uu____10213), FStar_Syntax_Syntax.U_name (uu____10214)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ (uu____10215)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name (uu____10216)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____10217), FStar_Syntax_Syntax.U_succ (uu____10218)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____10219), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end)))))))


let solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (match (wl.tcenv.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
USolved (wl)
end
| uu____10240 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders : 'a 'b . ('a Prims.list * ('a Prims.list  ->  'b))  ->  ('a Prims.list * ('a Prims.list  ->  'b))  ->  (('a Prims.list * 'b) * ('a Prims.list * 'b)) = (fun bc1 bc2 -> (

let uu____10319 = bc1
in (match (uu____10319) with
| (bs1, mk_cod1) -> begin
(

let uu____10363 = bc2
in (match (uu____10363) with
| (bs2, mk_cod2) -> begin
(

let rec aux = (fun bs11 bs21 -> (match (((bs11), (bs21))) with
| ((x)::xs, (y)::ys) -> begin
(

let uu____10474 = (aux xs ys)
in (match (uu____10474) with
| ((xs1, xr), (ys1, yr)) -> begin
(((((x)::xs1), (xr))), ((((y)::ys1), (yr))))
end))
end
| (xs, ys) -> begin
(

let uu____10557 = (

let uu____10564 = (mk_cod1 xs)
in (([]), (uu____10564)))
in (

let uu____10567 = (

let uu____10574 = (mk_cod2 ys)
in (([]), (uu____10574)))
in ((uu____10557), (uu____10567))))
end))
in (aux bs1 bs2))
end))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____10759 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____10759) with
| true -> begin
(

let uu____10760 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" uu____10760))
end
| uu____10761 -> begin
()
end));
(

let uu____10762 = (next_prob probs)
in (match (uu____10762) with
| (FStar_Pervasives_Native.Some (hd1), tl1, rank1) -> begin
(

let probs1 = (

let uu___141_10783 = probs
in {attempting = tl1; wl_deferred = uu___141_10783.wl_deferred; ctr = uu___141_10783.ctr; defer_ok = uu___141_10783.defer_ok; smt_ok = uu___141_10783.smt_ok; tcenv = uu___141_10783.tcenv})
in (match (hd1) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs1)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match ((((not (probs1.defer_ok)) && (flex_refine_inner <= rank1)) && (rank1 <= flex_rigid))) with
| true -> begin
(

let uu____10794 = (solve_flex_rigid_join env tp probs1)
in (match (uu____10794) with
| FStar_Pervasives_Native.None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| FStar_Pervasives_Native.Some (wl) -> begin
(solve env wl)
end))
end
| uu____10798 -> begin
(match ((((not (probs1.defer_ok)) && (rigid_flex <= rank1)) && (rank1 <= refine_flex))) with
| true -> begin
(

let uu____10799 = (solve_rigid_flex_meet env tp probs1)
in (match (uu____10799) with
| FStar_Pervasives_Native.None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| FStar_Pervasives_Native.Some (wl) -> begin
(solve env wl)
end))
end
| uu____10803 -> begin
(solve_t' env (maybe_invert tp) probs1)
end)
end)
end))
end
| (FStar_Pervasives_Native.None, uu____10804, uu____10805) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| uu____10822 -> begin
(

let uu____10831 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____10890 -> (match (uu____10890) with
| (c, uu____10898, uu____10899) -> begin
(c < probs.ctr)
end))))
in (match (uu____10831) with
| (attempt1, rest) -> begin
(match (attempt1) with
| [] -> begin
(

let uu____10940 = (FStar_List.map (fun uu____10955 -> (match (uu____10955) with
| (uu____10966, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (uu____10940))
end
| uu____10969 -> begin
(

let uu____10978 = (

let uu___142_10979 = probs
in (

let uu____10980 = (FStar_All.pipe_right attempt1 (FStar_List.map (fun uu____11001 -> (match (uu____11001) with
| (uu____11008, uu____11009, y) -> begin
y
end))))
in {attempting = uu____10980; wl_deferred = rest; ctr = uu___142_10979.ctr; defer_ok = uu___142_10979.defer_ok; smt_ok = uu___142_10979.smt_ok; tcenv = uu___142_10979.tcenv}))
in (solve env uu____10978))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____11016 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____11016) with
| USolved (wl1) -> begin
(

let uu____11018 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____11018))
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

let uu____11070 = (solve_universe_eq (p_pid orig) wl1 u1 u2)
in (match (uu____11070) with
| USolved (wl2) -> begin
(aux wl2 us11 us21)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____11073 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t11 = (whnf env t1)
in (

let t21 = (whnf env t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.pos = uu____11085; FStar_Syntax_Syntax.vars = uu____11086}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.pos = uu____11089; FStar_Syntax_Syntax.vars = uu____11090}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____11102), uu____11103) -> begin
(failwith "Impossible: expect head symbols to match")
end
| (uu____11110, FStar_Syntax_Syntax.Tm_uinst (uu____11111)) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____11118 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____11128 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11128) with
| true -> begin
(

let uu____11129 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" uu____11129 msg))
end
| uu____11130 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____11131 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist FStar_Pervasives_Native.option = (fun env tp wl -> ((

let uu____11138 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11138) with
| true -> begin
(

let uu____11139 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" uu____11139))
end
| uu____11140 -> begin
()
end));
(

let uu____11141 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____11141) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let uu____11207 = (head_matches_delta env () t1 t2)
in (match (uu____11207) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (uu____11248) -> begin
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

let uu____11297 = (match (ts) with
| FStar_Pervasives_Native.Some (t11, t21) -> begin
(

let uu____11312 = (FStar_Syntax_Subst.compress t11)
in (

let uu____11313 = (FStar_Syntax_Subst.compress t21)
in ((uu____11312), (uu____11313))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____11318 = (FStar_Syntax_Subst.compress t1)
in (

let uu____11319 = (FStar_Syntax_Subst.compress t2)
in ((uu____11318), (uu____11319))))
end)
in (match (uu____11297) with
| (t11, t21) -> begin
(

let eq_prob = (fun t12 t22 -> (

let uu____11349 = (new_problem env t12 FStar_TypeChecker_Common.EQ t22 FStar_Pervasives_Native.None t12.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _0_29 -> FStar_TypeChecker_Common.TProb (_0_29)) uu____11349)))
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(

let uu____11380 = (

let uu____11389 = (

let uu____11392 = (

let uu____11399 = (

let uu____11400 = (

let uu____11407 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (uu____11407)))
in FStar_Syntax_Syntax.Tm_refine (uu____11400))
in (FStar_Syntax_Syntax.mk uu____11399))
in (uu____11392 FStar_Pervasives_Native.None t11.FStar_Syntax_Syntax.pos))
in (

let uu____11415 = (

let uu____11418 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (uu____11418)::[])
in ((uu____11389), (uu____11415))))
in FStar_Pervasives_Native.Some (uu____11380))
end
| (uu____11431, FStar_Syntax_Syntax.Tm_refine (x, uu____11433)) -> begin
(

let uu____11438 = (

let uu____11445 = (

let uu____11448 = (eq_prob x.FStar_Syntax_Syntax.sort t11)
in (uu____11448)::[])
in ((t11), (uu____11445)))
in FStar_Pervasives_Native.Some (uu____11438))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____11458), uu____11459) -> begin
(

let uu____11464 = (

let uu____11471 = (

let uu____11474 = (eq_prob x.FStar_Syntax_Syntax.sort t21)
in (uu____11474)::[])
in ((t21), (uu____11471)))
in FStar_Pervasives_Native.Some (uu____11464))
end
| uu____11483 -> begin
(

let uu____11488 = (FStar_Syntax_Util.head_and_args t11)
in (match (uu____11488) with
| (head1, uu____11512) -> begin
(

let uu____11533 = (

let uu____11534 = (FStar_Syntax_Util.un_uinst head1)
in uu____11534.FStar_Syntax_Syntax.n)
in (match (uu____11533) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____11545; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant_at_level (i); FStar_Syntax_Syntax.fv_qual = uu____11547}) when (i > (Prims.parse_int "0")) -> begin
(

let prev = (match ((i > (Prims.parse_int "1"))) with
| true -> begin
FStar_Syntax_Syntax.Delta_constant_at_level ((i - (Prims.parse_int "1")))
end
| uu____11551 -> begin
FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "0"))
end)
in (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t21)
in (disjoin t12 t22))))
end
| uu____11554 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____11567) -> begin
(

let uu____11592 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___114_11618 -> (match (uu___114_11618) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| FStar_Pervasives_Native.Some (rank1) when (is_rigid_flex rank1) -> begin
(

let uu____11625 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.rhs)
in (match (uu____11625) with
| (u', uu____11641) -> begin
(

let uu____11662 = (

let uu____11663 = (whnf env u')
in uu____11663.FStar_Syntax_Syntax.n)
in (match (uu____11662) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____11667) -> begin
(FStar_Syntax_Unionfind.equiv uv uv')
end
| uu____11692 -> begin
false
end))
end))
end
| uu____11693 -> begin
false
end)
end
| uu____11696 -> begin
false
end))))
in (match (uu____11592) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun uu____11734 tps -> (match (uu____11734) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
FStar_Pervasives_Native.Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____11782 = (

let uu____11791 = (whnf env hd1.FStar_TypeChecker_Common.lhs)
in (disjoin bound uu____11791))
in (match (uu____11782) with
| FStar_Pervasives_Native.Some (bound1, sub1) -> begin
(make_lower_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____11826 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let uu____11835 = (

let uu____11844 = (

let uu____11851 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((uu____11851), ([])))
in (make_lower_bound uu____11844 lower_bounds))
in (match (uu____11835) with
| FStar_Pervasives_Native.None -> begin
((

let uu____11863 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11863) with
| true -> begin
(FStar_Util.print_string "No lower bounds\n")
end
| uu____11864 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (lhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in ((

let uu____11883 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11883) with
| true -> begin
(

let wl' = (

let uu___143_11885 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___143_11885.wl_deferred; ctr = uu___143_11885.ctr; defer_ok = uu___143_11885.defer_ok; smt_ok = uu___143_11885.smt_ok; tcenv = uu___143_11885.tcenv})
in (

let uu____11886 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" uu____11886)))
end
| uu____11887 -> begin
()
end));
(

let uu____11888 = (solve_t env eq_prob (

let uu___144_11890 = wl
in {attempting = sub_probs; wl_deferred = uu___144_11890.wl_deferred; ctr = uu___144_11890.ctr; defer_ok = uu___144_11890.defer_ok; smt_ok = uu___144_11890.smt_ok; tcenv = uu___144_11890.tcenv}))
in (match (uu____11888) with
| Success (uu____11893) -> begin
(

let wl1 = (

let uu___145_11895 = wl
in {attempting = rest; wl_deferred = uu___145_11895.wl_deferred; ctr = uu___145_11895.ctr; defer_ok = uu___145_11895.defer_ok; smt_ok = uu___145_11895.smt_ok; tcenv = uu___145_11895.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) FStar_Pervasives_Native.None [] wl1)
in (

let uu____11897 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p FStar_Pervasives_Native.None [] wl3)) wl2 lower_bounds)
in FStar_Pervasives_Native.Some (wl2))))
end
| uu____11902 -> begin
FStar_Pervasives_Native.None
end));
))
end)))
end))
end
| uu____11903 -> begin
(failwith "Impossible: Not a rigid-flex")
end)))
end));
))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist FStar_Pervasives_Native.option = (fun env tp wl -> ((

let uu____11912 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11912) with
| true -> begin
(

let uu____11913 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" uu____11913))
end
| uu____11914 -> begin
()
end));
(

let uu____11915 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____11915) with
| (u, args) -> begin
(

let uu____11954 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (uu____11954) with
| (ok, head_match1, partial_match, fallback, failed_match) -> begin
(

let max1 = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____11983 -> begin
i
end))
in (

let base_types_match = (fun t1 t2 -> (

let uu____12003 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____12003) with
| (h1, args1) -> begin
(

let uu____12044 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____12044) with
| (h2, uu____12064) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
(

let uu____12091 = (FStar_Syntax_Syntax.fv_eq tc1 tc2)
in (match (uu____12091) with
| true -> begin
(match ((Prims.op_Equality (FStar_List.length args1) (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____12108 -> begin
(

let uu____12109 = (

let uu____12112 = (

let uu____12113 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_30 -> FStar_TypeChecker_Common.TProb (_0_30)) uu____12113))
in (uu____12112)::[])
in FStar_Pervasives_Native.Some (uu____12109))
end)
end
| uu____12124 -> begin
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
| uu____12145 -> begin
(

let uu____12146 = (

let uu____12149 = (

let uu____12150 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_31 -> FStar_TypeChecker_Common.TProb (_0_31)) uu____12150))
in (uu____12149)::[])
in FStar_Pervasives_Native.Some (uu____12146))
end)
end
| uu____12161 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____12164 -> begin
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

let uu____12258 = (

let uu____12267 = (

let uu____12270 = (FStar_Syntax_Util.mk_conj phi11 phi21)
in (FStar_Syntax_Util.refine x1 uu____12270))
in ((uu____12267), (m1)))
in FStar_Pervasives_Native.Some (uu____12258))))))
end))
end
| (uu____12283, FStar_Syntax_Syntax.Tm_refine (y, uu____12285)) -> begin
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
| (FStar_Syntax_Syntax.Tm_refine (x, uu____12333), uu____12334) -> begin
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
| uu____12381 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____12434) -> begin
(

let uu____12459 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___115_12485 -> (match (uu___115_12485) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| FStar_Pervasives_Native.Some (rank1) when (is_flex_rigid rank1) -> begin
(

let uu____12492 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.lhs)
in (match (uu____12492) with
| (u', uu____12508) -> begin
(

let uu____12529 = (

let uu____12530 = (whnf env u')
in uu____12530.FStar_Syntax_Syntax.n)
in (match (uu____12529) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____12534) -> begin
(FStar_Syntax_Unionfind.equiv uv uv')
end
| uu____12559 -> begin
false
end))
end))
end
| uu____12560 -> begin
false
end)
end
| uu____12563 -> begin
false
end))))
in (match (uu____12459) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun uu____12605 tps -> (match (uu____12605) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
FStar_Pervasives_Native.Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____12667 = (

let uu____12678 = (whnf env hd1.FStar_TypeChecker_Common.rhs)
in (conjoin bound uu____12678))
in (match (uu____12667) with
| FStar_Pervasives_Native.Some (bound1, sub1) -> begin
(make_upper_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____12729 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let uu____12740 = (

let uu____12751 = (

let uu____12760 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((uu____12760), ([])))
in (make_upper_bound uu____12751 upper_bounds))
in (match (uu____12740) with
| FStar_Pervasives_Native.None -> begin
((

let uu____12774 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____12774) with
| true -> begin
(FStar_Util.print_string "No upper bounds\n")
end
| uu____12775 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "joining refinements")
in ((

let uu____12800 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____12800) with
| true -> begin
(

let wl' = (

let uu___146_12802 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___146_12802.wl_deferred; ctr = uu___146_12802.ctr; defer_ok = uu___146_12802.defer_ok; smt_ok = uu___146_12802.smt_ok; tcenv = uu___146_12802.tcenv})
in (

let uu____12803 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" uu____12803)))
end
| uu____12804 -> begin
()
end));
(

let uu____12805 = (solve_t env eq_prob (

let uu___147_12807 = wl
in {attempting = sub_probs; wl_deferred = uu___147_12807.wl_deferred; ctr = uu___147_12807.ctr; defer_ok = uu___147_12807.defer_ok; smt_ok = uu___147_12807.smt_ok; tcenv = uu___147_12807.tcenv}))
in (match (uu____12805) with
| Success (uu____12810) -> begin
(

let wl1 = (

let uu___148_12812 = wl
in {attempting = rest; wl_deferred = uu___148_12812.wl_deferred; ctr = uu___148_12812.ctr; defer_ok = uu___148_12812.defer_ok; smt_ok = uu___148_12812.smt_ok; tcenv = uu___148_12812.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) FStar_Pervasives_Native.None [] wl1)
in (

let uu____12814 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p FStar_Pervasives_Native.None [] wl3)) wl2 upper_bounds)
in FStar_Pervasives_Native.Some (wl2))))
end
| uu____12819 -> begin
FStar_Pervasives_Native.None
end));
))
end)))
end))
end
| uu____12820 -> begin
(failwith "Impossible: Not a flex-rigid")
end)))))
end))
end));
))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> ((

let uu____12838 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12838) with
| true -> begin
(

let uu____12839 = (FStar_Syntax_Print.binders_to_string ", " bs1)
in (

let uu____12840 = (FStar_Syntax_Print.binders_to_string ", " bs2)
in (FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n" uu____12839 (rel_to_string (p_rel orig)) uu____12840)))
end
| uu____12841 -> begin
()
end));
(

let rec aux = (fun scope env1 subst1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
(

let rhs_prob = (rhs scope env1 subst1)
in ((

let uu____12910 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____12910) with
| true -> begin
(

let uu____12911 = (prob_to_string env1 rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" uu____12911))
end
| uu____12912 -> begin
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

let uu___149_12965 = hd1
in (

let uu____12966 = (FStar_Syntax_Subst.subst subst1 hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___149_12965.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___149_12965.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____12966}))
in (

let hd21 = (

let uu___150_12970 = hd2
in (

let uu____12971 = (FStar_Syntax_Subst.subst subst1 hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___150_12970.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___150_12970.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____12971}))
in (

let prob = (

let uu____12975 = (

let uu____12980 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd11.FStar_Syntax_Syntax.sort uu____12980 hd21.FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None "Formal parameter"))
in (FStar_All.pipe_left (fun _0_32 -> FStar_TypeChecker_Common.TProb (_0_32)) uu____12975))
in (

let hd12 = (FStar_Syntax_Syntax.freshen_bv hd11)
in (

let subst2 = (

let uu____12991 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd12))))::uu____12991)
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 hd12)
in (

let uu____12995 = (aux (FStar_List.append scope ((((hd12), (imp)))::[])) env2 subst2 xs1 ys1)
in (match (uu____12995) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi1 = (

let uu____13033 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (

let uu____13038 = (close_forall env2 ((((hd12), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj uu____13033 uu____13038)))
in ((

let uu____13048 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____13048) with
| true -> begin
(

let uu____13049 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____13050 = (FStar_Syntax_Print.bv_to_string hd12)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" uu____13049 uu____13050)))
end
| uu____13051 -> begin
()
end));
FStar_Util.Inl ((((prob)::sub_probs), (phi1)));
))
end
| fail1 -> begin
fail1
end))))))))
end
| uu____13073 -> begin
FStar_Util.Inr ("arity or argument-qualifier mismatch")
end))
in (

let scope = (p_scope orig)
in (

let uu____13083 = (aux scope env [] bs1 bs2)
in (match (uu____13083) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (phi)) [] wl)
in (solve env (attempt sub_probs wl1)))
end))));
))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> ((def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb (problem)));
(

let uu____13108 = (compress_tprob wl problem)
in (solve_t' env uu____13108 wl));
))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> ((def_check_prob "solve_t\'.1" (FStar_TypeChecker_Common.TProb (problem)));
(

let giveup_or_defer1 = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env1 orig wl1 head1 head2 t1 t2 -> (

let uu____13160 = (head_matches_delta env1 wl1 t1 t2)
in (match (uu____13160) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____13191), uu____13192) -> begin
(

let rec may_relate = (fun head3 -> (

let uu____13219 = (

let uu____13220 = (FStar_Syntax_Subst.compress head3)
in uu____13220.FStar_Syntax_Syntax.n)
in (match (uu____13219) with
| FStar_Syntax_Syntax.Tm_name (uu____13223) -> begin
true
end
| FStar_Syntax_Syntax.Tm_match (uu____13224) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____13247; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational_at_level (uu____13248); FStar_Syntax_Syntax.fv_qual = uu____13249}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____13252; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (uu____13253); FStar_Syntax_Syntax.fv_qual = uu____13254}) -> begin
(Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____13258, uu____13259) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____13301) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____13307) -> begin
(may_relate t)
end
| uu____13312 -> begin
false
end)))
in (

let uu____13313 = (((may_relate head1) || (may_relate head2)) && wl1.smt_ok)
in (match (uu____13313) with
| true -> begin
(

let guard = (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_eq2 orig t1 t2)
end
| uu____13315 -> begin
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

let uu____13334 = (

let uu____13335 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t11 uu____13335 t21))
in (FStar_Syntax_Util.mk_forall u_x x uu____13334))))
end))
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB)) with
| true -> begin
(has_type_guard t1 t2)
end
| uu____13336 -> begin
(has_type_guard t2 t1)
end))
end)
in (

let uu____13337 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl1)
in (solve env1 uu____13337)))
end
| uu____13338 -> begin
(

let uu____13339 = (

let uu____13340 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____13341 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.format2 "head mismatch (%s vs %s)" uu____13340 uu____13341)))
in (giveup env1 uu____13339 orig))
end)))
end
| (uu____13342, FStar_Pervasives_Native.Some (t11, t21)) -> begin
(solve_t env1 (

let uu___151_13356 = problem
in {FStar_TypeChecker_Common.pid = uu___151_13356.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___151_13356.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___151_13356.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___151_13356.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___151_13356.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___151_13356.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___151_13356.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___151_13356.FStar_TypeChecker_Common.rank}) wl1)
end
| (uu____13357, FStar_Pervasives_Native.None) -> begin
((

let uu____13369 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____13369) with
| true -> begin
(

let uu____13370 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____13371 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____13372 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____13373 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n" uu____13370 uu____13371 uu____13372 uu____13373)))))
end
| uu____13374 -> begin
()
end));
(

let uu____13375 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____13375) with
| (head11, args1) -> begin
(

let uu____13412 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____13412) with
| (head21, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((Prims.op_disEquality nargs (FStar_List.length args2))) with
| true -> begin
(

let uu____13466 = (

let uu____13467 = (FStar_Syntax_Print.term_to_string head11)
in (

let uu____13468 = (args_to_string args1)
in (

let uu____13469 = (FStar_Syntax_Print.term_to_string head21)
in (

let uu____13470 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____13467 uu____13468 uu____13469 uu____13470)))))
in (giveup env1 uu____13466 orig))
end
| uu____13471 -> begin
(

let uu____13472 = ((Prims.op_Equality nargs (Prims.parse_int "0")) || (

let uu____13478 = (FStar_Syntax_Util.eq_args args1 args2)
in (Prims.op_Equality uu____13478 FStar_Syntax_Util.Equal)))
in (match (uu____13472) with
| true -> begin
(

let uu____13479 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____13479) with
| USolved (wl2) -> begin
(

let uu____13481 = (solve_prob orig FStar_Pervasives_Native.None [] wl2)
in (solve env1 uu____13481))
end
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end))
end
| uu____13484 -> begin
(

let uu____13485 = (base_and_refinement env1 t1)
in (match (uu____13485) with
| (base1, refinement1) -> begin
(

let uu____13510 = (base_and_refinement env1 t2)
in (match (uu____13510) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(

let uu____13567 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____13567) with
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end
| USolved (wl2) -> begin
(

let subprobs = (FStar_List.map2 (fun uu____13589 uu____13590 -> (match (((uu____13589), (uu____13590))) with
| ((a, uu____13608), (a', uu____13610)) -> begin
(

let uu____13619 = (

let uu____13624 = (p_scope orig)
in (mk_problem uu____13624 orig a FStar_TypeChecker_Common.EQ a' FStar_Pervasives_Native.None "index"))
in (FStar_All.pipe_left (fun _0_33 -> FStar_TypeChecker_Common.TProb (_0_33)) uu____13619))
end)) args1 args2)
in ((

let uu____13630 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____13630) with
| true -> begin
(

let uu____13631 = (FStar_Syntax_Print.list_to_string (prob_to_string env1) subprobs)
in (FStar_Util.print1 "Adding subproblems for arguments: %s" uu____13631))
end
| uu____13632 -> begin
()
end));
(

let formula = (

let uu____13634 = (FStar_List.map (fun p -> (FStar_Pervasives_Native.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____13634))
in (

let wl3 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) [] wl2)
in (solve env1 (attempt subprobs wl3))));
))
end))
end
| uu____13640 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env1 (

let uu___152_13676 = problem
in {FStar_TypeChecker_Common.pid = uu___152_13676.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___152_13676.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___152_13676.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___152_13676.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___152_13676.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___152_13676.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___152_13676.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___152_13676.FStar_TypeChecker_Common.rank}) wl1)))
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

let force_quasi_pattern = (fun xs_opt uu____13713 -> (match (uu____13713) with
| (t, u, k, args) -> begin
(

let debug1 = (fun f -> (

let uu____13757 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____13757) with
| true -> begin
(f ())
end
| uu____13758 -> begin
()
end)))
in (

let rec aux = (fun pat_args pat_args_set pattern_vars pattern_var_set seen_formals formals res_t args1 -> ((debug1 (fun uu____13869 -> (

let uu____13870 = (FStar_Syntax_Print.binders_to_string ", " pat_args)
in (FStar_Util.print1 "pat_args so far: {%s}\n" uu____13870))));
(match (((formals), (args1))) with
| ([], []) -> begin
(

let pat_args1 = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun uu____13938 -> (match (uu____13938) with
| (x, imp) -> begin
(

let uu____13949 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____13949), (imp)))
end))))
in (

let pattern_vars1 = (FStar_List.rev pattern_vars)
in (

let kk = (

let uu____13962 = (FStar_Syntax_Util.type_u ())
in (match (uu____13962) with
| (t1, uu____13968) -> begin
(

let uu____13969 = (new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1 t1)
in (FStar_Pervasives_Native.fst uu____13969))
end))
in (

let uu____13974 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk)
in (match (uu____13974) with
| (t', tm_u1) -> begin
(

let uu____13987 = (destruct_flex_t t')
in (match (uu____13987) with
| (uu____14024, u1, k1, uu____14027) -> begin
(

let all_formals = (FStar_List.rev seen_formals)
in (

let k2 = (

let uu____14086 = (FStar_Syntax_Syntax.mk_Total res_t)
in (FStar_Syntax_Util.arrow all_formals uu____14086))
in (

let sol = (

let uu____14090 = (

let uu____14099 = (u_abs k2 all_formals t')
in ((((u), (k2))), (uu____14099)))
in TERM (uu____14090))
in (

let t_app = (FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (((sol), (((t_app), (u1), (k1), (pat_args1)))))))))
end))
end)))))
end
| ((formal)::formals1, (hd1)::tl1) -> begin
((debug1 (fun uu____14234 -> (

let uu____14235 = (FStar_Syntax_Print.binder_to_string formal)
in (

let uu____14236 = (FStar_Syntax_Print.args_to_string ((hd1)::[]))
in (FStar_Util.print2 "force_quasi_pattern (case 2): formal=%s, hd=%s\n" uu____14235 uu____14236)))));
(

let uu____14249 = (pat_var_opt env pat_args hd1)
in (match (uu____14249) with
| FStar_Pervasives_Native.None -> begin
((debug1 (fun uu____14269 -> (FStar_Util.print_string "not a pattern var\n")));
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun uu____14312 -> (match (uu____14312) with
| (x, uu____14318) -> begin
(FStar_Syntax_Syntax.bv_eq x (FStar_Pervasives_Native.fst y))
end))))
end)
in (match ((not (maybe_pat))) with
| true -> begin
(aux pat_args pat_args_set pattern_vars pattern_var_set ((formal)::seen_formals) formals1 res_t tl1)
end
| uu____14325 -> begin
((debug1 (fun uu____14333 -> (

let uu____14334 = (FStar_Syntax_Print.args_to_string ((hd1)::[]))
in (

let uu____14347 = (FStar_Syntax_Print.binder_to_string y)
in (FStar_Util.print2 "%s (var = %s) maybe pat\n" uu____14334 uu____14347)))));
(

let fvs = (FStar_Syntax_Free.names (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____14351 = (

let uu____14352 = (FStar_Util.set_is_subset_of fvs pat_args_set)
in (not (uu____14352)))
in (match (uu____14351) with
| true -> begin
((debug1 (fun uu____14364 -> (

let uu____14365 = (

let uu____14368 = (FStar_Syntax_Print.args_to_string ((hd1)::[]))
in (

let uu____14381 = (

let uu____14384 = (FStar_Syntax_Print.binder_to_string y)
in (

let uu____14385 = (

let uu____14388 = (FStar_Syntax_Print.term_to_string (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____14389 = (

let uu____14392 = (names_to_string fvs)
in (

let uu____14393 = (

let uu____14396 = (names_to_string pattern_var_set)
in (uu____14396)::[])
in (uu____14392)::uu____14393))
in (uu____14388)::uu____14389))
in (uu____14384)::uu____14385))
in (uu____14368)::uu____14381))
in (FStar_Util.print "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n" uu____14365))));
(aux pat_args pat_args_set pattern_vars pattern_var_set ((formal)::seen_formals) formals1 res_t tl1);
)
end
| uu____14397 -> begin
(

let uu____14398 = (FStar_Util.set_add (FStar_Pervasives_Native.fst y) pat_args_set)
in (

let uu____14401 = (FStar_Util.set_add (FStar_Pervasives_Native.fst formal) pattern_var_set)
in (aux ((y)::pat_args) uu____14398 ((formal)::pattern_vars) uu____14401 ((formal)::seen_formals) formals1 res_t tl1)))
end)));
)
end))
end));
)
end
| ([], (uu____14408)::uu____14409) -> begin
(

let uu____14440 = (

let uu____14453 = (FStar_TypeChecker_Normalize.unfold_whnf env res_t)
in (FStar_Syntax_Util.arrow_formals uu____14453))
in (match (uu____14440) with
| (more_formals, res_t1) -> begin
(match (more_formals) with
| [] -> begin
FStar_Pervasives_Native.None
end
| uu____14492 -> begin
(aux pat_args pat_args_set pattern_vars pattern_var_set seen_formals more_formals res_t1 args1)
end)
end))
end
| ((uu____14499)::uu____14500, []) -> begin
FStar_Pervasives_Native.None
end);
))
in (

let uu____14523 = (

let uu____14536 = (FStar_TypeChecker_Normalize.unfold_whnf env k)
in (FStar_Syntax_Util.arrow_formals uu____14536))
in (match (uu____14523) with
| (all_formals, res_t) -> begin
((debug1 (fun uu____14572 -> (

let uu____14573 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____14574 = (FStar_Syntax_Print.binders_to_string ", " all_formals)
in (

let uu____14575 = (FStar_Syntax_Print.term_to_string res_t)
in (

let uu____14576 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print4 "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n" uu____14573 uu____14574 uu____14575 uu____14576)))))));
(

let uu____14577 = (FStar_Syntax_Syntax.new_bv_set ())
in (

let uu____14580 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] uu____14577 [] uu____14580 [] all_formals res_t args)));
)
end))))
end))
in (

let use_pattern_equality = (fun orig env1 wl1 lhs pat_vars1 rhs -> (

let uu____14626 = lhs
in (match (uu____14626) with
| (t1, uv, k_uv, args_lhs) -> begin
(

let sol = (match (pat_vars1) with
| [] -> begin
rhs
end
| uu____14636 -> begin
(

let uu____14637 = (sn_binders env1 pat_vars1)
in (u_abs k_uv uu____14637 rhs))
end)
in (

let wl2 = (solve_prob orig FStar_Pervasives_Native.None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl1)
in (solve env1 wl2)))
end)))
in (

let imitate = (fun orig env1 wl1 p -> (

let uu____14668 = p
in (match (uu____14668) with
| (((u, k), xs, c), ps, (h, uu____14679, qs)) -> begin
(

let xs1 = (sn_binders env1 xs)
in (

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____14767 = (imitation_sub_probs orig env1 xs1 ps qs)
in (match (uu____14767) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (

let uu____14790 = (h gs_xs)
in (

let uu____14791 = (FStar_All.pipe_right (FStar_Syntax_Util.residual_comp_of_comp c) (fun _0_34 -> FStar_Pervasives_Native.Some (_0_34)))
in (FStar_Syntax_Util.abs xs1 uu____14790 uu____14791)))
in ((

let uu____14797 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____14797) with
| true -> begin
(

let uu____14798 = (

let uu____14801 = (

let uu____14802 = (FStar_List.map tc_to_string gs_xs)
in (FStar_All.pipe_right uu____14802 (FStar_String.concat "\n\t>")))
in (

let uu____14807 = (

let uu____14810 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____14811 = (

let uu____14814 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____14815 = (

let uu____14818 = (FStar_Syntax_Print.term_to_string im)
in (

let uu____14819 = (

let uu____14822 = (FStar_Syntax_Print.tag_of_term im)
in (

let uu____14823 = (

let uu____14826 = (

let uu____14827 = (FStar_List.map (prob_to_string env1) sub_probs)
in (FStar_All.pipe_right uu____14827 (FStar_String.concat ", ")))
in (

let uu____14832 = (

let uu____14835 = (FStar_TypeChecker_Normalize.term_to_string env1 formula)
in (uu____14835)::[])
in (uu____14826)::uu____14832))
in (uu____14822)::uu____14823))
in (uu____14818)::uu____14819))
in (uu____14814)::uu____14815))
in (uu____14810)::uu____14811))
in (uu____14801)::uu____14807))
in (FStar_Util.print "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" uu____14798))
end
| uu____14836 -> begin
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

let imitate' = (fun orig env1 wl1 uu___116_14865 -> (match (uu___116_14865) with
| FStar_Pervasives_Native.None -> begin
(giveup env1 "unable to compute subterms" orig)
end
| FStar_Pervasives_Native.Some (p) -> begin
(imitate orig env1 wl1 p)
end))
in (

let project = (fun orig env1 wl1 i p -> (

let uu____14907 = p
in (match (uu____14907) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____15004 = (FStar_List.nth ps i)
in (match (uu____15004) with
| (pi, uu____15008) -> begin
(

let uu____15013 = (FStar_List.nth xs i)
in (match (uu____15013) with
| (xi, uu____15025) -> begin
(

let rec gs = (fun k -> (

let uu____15040 = (

let uu____15053 = (FStar_TypeChecker_Normalize.unfold_whnf env1 k)
in (FStar_Syntax_Util.arrow_formals uu____15053))
in (match (uu____15040) with
| (bs, k1) -> begin
(

let rec aux = (fun subst1 bs1 -> (match (bs1) with
| [] -> begin
(([]), ([]))
end
| ((a, uu____15132))::tl1 -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst1 a.FStar_Syntax_Syntax.sort)
in (

let uu____15145 = (new_uvar r xs k_a)
in (match (uu____15145) with
| (gi_xs, gi) -> begin
(

let gi_xs1 = (FStar_TypeChecker_Normalize.eta_expand env1 gi_xs)
in (

let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps FStar_Pervasives_Native.None r)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((a), (gi_xs1))))::subst1
in (

let uu____15167 = (aux subst2 tl1)
in (match (uu____15167) with
| (gi_xs', gi_ps') -> begin
(

let uu____15194 = (

let uu____15197 = (FStar_Syntax_Syntax.as_arg gi_xs1)
in (uu____15197)::gi_xs')
in (

let uu____15198 = (

let uu____15201 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (uu____15201)::gi_ps')
in ((uu____15194), (uu____15198))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in (

let uu____15206 = (

let uu____15207 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation uu____15207))
in (match (uu____15206) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____15210 -> begin
(

let uu____15211 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (uu____15211) with
| (g_xs, uu____15223) -> begin
(

let xi1 = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (

let uu____15234 = (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs FStar_Pervasives_Native.None r)
in (

let uu____15235 = (FStar_All.pipe_right (FStar_Syntax_Util.residual_comp_of_comp c) (fun _0_35 -> FStar_Pervasives_Native.Some (_0_35)))
in (FStar_Syntax_Util.abs xs uu____15234 uu____15235)))
in (

let sub1 = (

let uu____15241 = (

let uu____15246 = (p_scope orig)
in (

let uu____15247 = (FStar_Syntax_Syntax.mk_Tm_app proj ps FStar_Pervasives_Native.None r)
in (

let uu____15250 = (

let uu____15253 = (FStar_List.map (fun uu____15268 -> (match (uu____15268) with
| (uu____15277, uu____15278, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h uu____15253))
in (mk_problem uu____15246 orig uu____15247 (p_rel orig) uu____15250 FStar_Pervasives_Native.None "projection"))))
in (FStar_All.pipe_left (fun _0_36 -> FStar_TypeChecker_Common.TProb (_0_36)) uu____15241))
in ((

let uu____15293 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____15293) with
| true -> begin
(

let uu____15294 = (FStar_Syntax_Print.term_to_string proj)
in (

let uu____15295 = (prob_to_string env1 sub1)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" uu____15294 uu____15295)))
end
| uu____15296 -> begin
()
end));
(

let wl2 = (

let uu____15298 = (

let uu____15301 = (FStar_All.pipe_left FStar_Pervasives_Native.fst (p_guard sub1))
in FStar_Pervasives_Native.Some (uu____15301))
in (solve_prob orig uu____15298 ((TERM (((u), (proj))))::[]) wl1))
in (

let uu____15310 = (solve env1 (attempt ((sub1)::[]) wl2))
in (FStar_All.pipe_left (fun _0_37 -> FStar_Pervasives_Native.Some (_0_37)) uu____15310)));
))))
end))
end)))
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl1 -> (

let uu____15351 = lhs
in (match (uu____15351) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let uu____15389 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (uu____15389) with
| (xs, c) -> begin
(match ((Prims.op_Equality (FStar_List.length xs) (FStar_List.length ps))) with
| true -> begin
(

let uu____15422 = (

let uu____15471 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____15471)))
in FStar_Pervasives_Native.Some (uu____15422))
end
| uu____15596 -> begin
(

let rec elim = (fun k args -> (

let k1 = (FStar_TypeChecker_Normalize.unfold_whnf env k)
in (

let uu____15625 = (

let uu____15632 = (

let uu____15633 = (FStar_Syntax_Subst.compress k1)
in uu____15633.FStar_Syntax_Syntax.n)
in ((uu____15632), (args)))
in (match (uu____15625) with
| (uu____15644, []) -> begin
(

let uu____15647 = (

let uu____15658 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____15658)))
in FStar_Pervasives_Native.Some (uu____15647))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____15679), uu____15680) -> begin
(

let uu____15701 = (FStar_Syntax_Util.head_and_args k1)
in (match (uu____15701) with
| (uv1, uv_args) -> begin
(

let uu____15744 = (

let uu____15745 = (FStar_Syntax_Subst.compress uv1)
in uu____15745.FStar_Syntax_Syntax.n)
in (match (uu____15744) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____15755) -> begin
(

let uu____15780 = (pat_vars env [] uv_args)
in (match (uu____15780) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (scope) -> begin
(

let xs1 = (FStar_All.pipe_right args (FStar_List.map (fun uu____15807 -> (

let uu____15808 = (

let uu____15809 = (

let uu____15810 = (

let uu____15815 = (

let uu____15816 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____15816 FStar_Pervasives_Native.fst))
in (new_uvar k1.FStar_Syntax_Syntax.pos scope uu____15815))
in (FStar_Pervasives_Native.fst uu____15810))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (k1.FStar_Syntax_Syntax.pos)) uu____15809))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____15808)))))
in (

let c1 = (

let uu____15826 = (

let uu____15827 = (

let uu____15832 = (

let uu____15833 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____15833 FStar_Pervasives_Native.fst))
in (new_uvar k1.FStar_Syntax_Syntax.pos scope uu____15832))
in (FStar_Pervasives_Native.fst uu____15827))
in (FStar_Syntax_Syntax.mk_Total uu____15826))
in (

let k' = (FStar_Syntax_Util.arrow xs1 c1)
in (

let uv_sol = (

let uu____15846 = (

let uu____15849 = (

let uu____15850 = (

let uu____15853 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____15853 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Util.residual_tot uu____15850))
in FStar_Pervasives_Native.Some (uu____15849))
in (FStar_Syntax_Util.abs scope k' uu____15846))
in ((def_check_closed (p_loc orig) "solve_t_flex_rigid.subterms" uv_sol);
(FStar_Syntax_Util.set_uvar uvar uv_sol);
FStar_Pervasives_Native.Some (((xs1), (c1)));
)))))
end))
end
| uu____15872 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_app (uu____15877), uu____15878) -> begin
(

let uu____15897 = (FStar_Syntax_Util.head_and_args k1)
in (match (uu____15897) with
| (uv1, uv_args) -> begin
(

let uu____15940 = (

let uu____15941 = (FStar_Syntax_Subst.compress uv1)
in uu____15941.FStar_Syntax_Syntax.n)
in (match (uu____15940) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____15951) -> begin
(

let uu____15976 = (pat_vars env [] uv_args)
in (match (uu____15976) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (scope) -> begin
(

let xs1 = (FStar_All.pipe_right args (FStar_List.map (fun uu____16003 -> (

let uu____16004 = (

let uu____16005 = (

let uu____16006 = (

let uu____16011 = (

let uu____16012 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____16012 FStar_Pervasives_Native.fst))
in (new_uvar k1.FStar_Syntax_Syntax.pos scope uu____16011))
in (FStar_Pervasives_Native.fst uu____16006))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (k1.FStar_Syntax_Syntax.pos)) uu____16005))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____16004)))))
in (

let c1 = (

let uu____16022 = (

let uu____16023 = (

let uu____16028 = (

let uu____16029 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____16029 FStar_Pervasives_Native.fst))
in (new_uvar k1.FStar_Syntax_Syntax.pos scope uu____16028))
in (FStar_Pervasives_Native.fst uu____16023))
in (FStar_Syntax_Syntax.mk_Total uu____16022))
in (

let k' = (FStar_Syntax_Util.arrow xs1 c1)
in (

let uv_sol = (

let uu____16042 = (

let uu____16045 = (

let uu____16046 = (

let uu____16049 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____16049 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Util.residual_tot uu____16046))
in FStar_Pervasives_Native.Some (uu____16045))
in (FStar_Syntax_Util.abs scope k' uu____16042))
in ((def_check_closed (p_loc orig) "solve_t_flex_rigid.subterms" uv_sol);
(FStar_Syntax_Util.set_uvar uvar uv_sol);
FStar_Pervasives_Native.Some (((xs1), (c1)));
)))))
end))
end
| uu____16068 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs1, c1), uu____16075) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs1)
in (match ((Prims.op_Equality n_xs n_args)) with
| true -> begin
(

let uu____16116 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (FStar_All.pipe_right uu____16116 (fun _0_38 -> FStar_Pervasives_Native.Some (_0_38))))
end
| uu____16135 -> begin
(match ((n_xs < n_args)) with
| true -> begin
(

let uu____16152 = (FStar_Util.first_N n_xs args)
in (match (uu____16152) with
| (args1, rest) -> begin
(

let uu____16181 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (match (uu____16181) with
| (xs2, c2) -> begin
(

let uu____16194 = (elim (FStar_Syntax_Util.comp_result c2) rest)
in (FStar_Util.bind_opt uu____16194 (fun uu____16218 -> (match (uu____16218) with
| (xs', c3) -> begin
FStar_Pervasives_Native.Some ((((FStar_List.append xs2 xs')), (c3)))
end))))
end))
end))
end
| uu____16257 -> begin
(

let uu____16258 = (FStar_Util.first_N n_args xs1)
in (match (uu____16258) with
| (xs2, rest) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c1)))) FStar_Pervasives_Native.None k1.FStar_Syntax_Syntax.pos)
in (

let uu____16326 = (

let uu____16331 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs2 uu____16331))
in (FStar_All.pipe_right uu____16326 (fun _0_39 -> FStar_Pervasives_Native.Some (_0_39)))))
end))
end)
end)))
end
| uu____16346 -> begin
(

let uu____16353 = (

let uu____16358 = (

let uu____16359 = (FStar_Syntax_Print.uvar_to_string uv)
in (

let uu____16360 = (FStar_Syntax_Print.term_to_string k1)
in (

let uu____16361 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" uu____16359 uu____16360 uu____16361))))
in ((FStar_Errors.Fatal_IllTyped), (uu____16358)))
in (FStar_Errors.raise_error uu____16353 t1.FStar_Syntax_Syntax.pos))
end))))
in (

let uu____16368 = (elim k_uv ps)
in (FStar_Util.bind_opt uu____16368 (fun uu____16425 -> (match (uu____16425) with
| (xs1, c1) -> begin
(

let uu____16476 = (

let uu____16519 = (decompose env t2)
in ((((((uv), (k_uv))), (xs1), (c1))), (ps), (uu____16519)))
in FStar_Pervasives_Native.Some (uu____16476))
end)))))
end)
end)))
in (

let imitate_or_project = (fun n1 lhs1 rhs stopt -> (

let fail1 = (fun uu____16656 -> (giveup env "flex-rigid case failed all backtracking attempts" orig))
in (

let rec try_project = (fun st i -> (match ((i >= n1)) with
| true -> begin
(fail1 ())
end
| uu____16674 -> begin
(

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____16676 = (project orig env wl1 i st)
in (match (uu____16676) with
| FStar_Pervasives_Native.None -> begin
((FStar_Syntax_Unionfind.rollback tx);
(try_project st (i + (Prims.parse_int "1")));
)
end
| FStar_Pervasives_Native.Some (Failed (uu____16690)) -> begin
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

let uu____16705 = (imitate orig env wl1 st)
in (match (uu____16705) with
| Failed (uu____16710) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(try_project st (Prims.parse_int "0"));
)
end
| sol -> begin
sol
end))))
end
| uu____16723 -> begin
(fail1 ())
end))))
in (

let pattern_eq_imitate_or_project = (fun n1 lhs1 rhs stopt -> (

let uu____16749 = (force_quasi_pattern FStar_Pervasives_Native.None lhs1)
in (match (uu____16749) with
| FStar_Pervasives_Native.None -> begin
(imitate_or_project n1 lhs1 rhs stopt)
end
| FStar_Pervasives_Native.Some (sol, forced_lhs_pattern) -> begin
(

let uu____16772 = forced_lhs_pattern
in (match (uu____16772) with
| (lhs_t, uu____16774, uu____16775, uu____16776) -> begin
((

let uu____16778 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____16778) with
| true -> begin
(

let uu____16779 = lhs1
in (match (uu____16779) with
| (t0, uu____16781, uu____16782, uu____16783) -> begin
(

let uu____16784 = forced_lhs_pattern
in (match (uu____16784) with
| (t11, uu____16786, uu____16787, uu____16788) -> begin
(

let uu____16789 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____16790 = (FStar_Syntax_Print.term_to_string t11)
in (FStar_Util.print2 "force_quasi_pattern succeeded, turning %s into %s\n" uu____16789 uu____16790)))
end))
end))
end
| uu____16791 -> begin
()
end));
(

let rhs_vars = (FStar_Syntax_Free.names rhs)
in (

let lhs_vars = (FStar_Syntax_Free.names lhs_t)
in (

let uu____16798 = (FStar_Util.set_is_subset_of rhs_vars lhs_vars)
in (match (uu____16798) with
| true -> begin
((

let uu____16800 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____16800) with
| true -> begin
(

let uu____16801 = (FStar_Syntax_Print.term_to_string rhs)
in (

let uu____16802 = (names_to_string rhs_vars)
in (

let uu____16803 = (names_to_string lhs_vars)
in (FStar_Util.print3 "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n" uu____16801 uu____16802 uu____16803))))
end
| uu____16804 -> begin
()
end));
(

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let wl2 = (extend_solution (p_pid orig) ((sol)::[]) wl1)
in (

let uu____16807 = (

let uu____16808 = (FStar_TypeChecker_Common.as_tprob orig)
in (solve_t env uu____16808 wl2))
in (match (uu____16807) with
| Failed (uu____16809) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(imitate_or_project n1 lhs1 rhs stopt);
)
end
| sol1 -> begin
sol1
end))));
)
end
| uu____16816 -> begin
((

let uu____16818 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____16818) with
| true -> begin
(FStar_Util.print_string "fvar check failed for quasi pattern ... im/proj\n")
end
| uu____16819 -> begin
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

let uu____16835 = (FStar_Syntax_Util.head_and_args t21)
in (match (uu____16835) with
| (hd1, uu____16851) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____16872) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____16885) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____16886) -> begin
true
end
| uu____16903 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd1)
in (

let uu____16907 = (FStar_Util.set_is_subset_of fvs_hd fvs1)
in (match (uu____16907) with
| true -> begin
true
end
| uu____16908 -> begin
((

let uu____16910 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____16910) with
| true -> begin
(

let uu____16911 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s\n" uu____16911))
end
| uu____16912 -> begin
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

let uu____16931 = (occurs_check env wl1 ((uv), (k_uv)) t21)
in (match (uu____16931) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____16944 = (

let uu____16945 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____16945))
in (giveup_or_defer1 orig uu____16944))
end
| uu____16946 -> begin
(

let uu____16947 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____16947) with
| true -> begin
(

let uu____16948 = (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t21)) && (Prims.op_disEquality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____16948) with
| true -> begin
(

let uu____16949 = (subterms args_lhs)
in (imitate' orig env wl1 uu____16949))
end
| uu____16952 -> begin
((

let uu____16954 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____16954) with
| true -> begin
(

let uu____16955 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____16956 = (names_to_string fvs1)
in (

let uu____16957 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" uu____16955 uu____16956 uu____16957))))
end
| uu____16958 -> begin
()
end));
(use_pattern_equality orig env wl1 lhs1 vars t21);
)
end))
end
| uu____16959 -> begin
(match ((((not (patterns_only)) && wl1.defer_ok) && (Prims.op_disEquality (p_rel orig) FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl1))
end
| uu____16960 -> begin
(

let uu____16961 = ((not (patterns_only)) && (check_head fvs1 t21))
in (match (uu____16961) with
| true -> begin
((

let uu____16963 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____16963) with
| true -> begin
(

let uu____16964 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____16965 = (names_to_string fvs1)
in (

let uu____16966 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n" uu____16964 uu____16965 uu____16966))))
end
| uu____16967 -> begin
()
end));
(

let uu____16968 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) lhs1 t21 uu____16968));
)
end
| uu____16977 -> begin
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
| uu____16978 -> begin
(

let uu____16979 = (

let uu____16980 = (FStar_Syntax_Free.names t1)
in (check_head uu____16980 t2))
in (match (uu____16979) with
| true -> begin
(

let n_args_lhs = (FStar_List.length args_lhs)
in ((

let uu____16991 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____16991) with
| true -> begin
(

let uu____16992 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____16993 = (FStar_Util.string_of_int n_args_lhs)
in (FStar_Util.print2 "Not a pattern (%s) ... (lhs has %s args)\n" uu____16992 uu____16993)))
end
| uu____17000 -> begin
()
end));
(

let uu____17001 = (subterms args_lhs)
in (pattern_eq_imitate_or_project n_args_lhs (FStar_Pervasives_Native.fst lhs) t2 uu____17001));
))
end
| uu____17012 -> begin
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
| uu____17029 -> begin
(

let solve_both_pats = (fun wl1 uu____17092 uu____17093 r -> (match (((uu____17092), (uu____17093))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
(

let uu____17291 = ((FStar_Syntax_Unionfind.equiv u1 u2) && (binders_eq xs ys))
in (match (uu____17291) with
| true -> begin
(

let uu____17292 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____17292))
end
| uu____17293 -> begin
(

let xs1 = (sn_binders env xs)
in (

let ys1 = (sn_binders env ys)
in (

let zs = (intersect_vars xs1 ys1)
in ((

let uu____17316 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____17316) with
| true -> begin
(

let uu____17317 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____17318 = (FStar_Syntax_Print.binders_to_string ", " ys1)
in (

let uu____17319 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (

let uu____17320 = (FStar_Syntax_Print.term_to_string k1)
in (

let uu____17321 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" uu____17317 uu____17318 uu____17319 uu____17320 uu____17321))))))
end
| uu____17322 -> begin
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

let uu____17387 = (FStar_Syntax_Util.subst_of_list xs2 args)
in (FStar_Syntax_Subst.subst uu____17387 k))
end
| uu____17390 -> begin
(match ((args_len < xs_len)) with
| true -> begin
(

let uu____17401 = (FStar_Util.first_N args_len xs2)
in (match (uu____17401) with
| (xs3, xs_rest) -> begin
(

let k3 = (

let uu____17455 = (FStar_Syntax_Syntax.mk_GTotal k)
in (FStar_Syntax_Util.arrow xs_rest uu____17455))
in (

let uu____17458 = (FStar_Syntax_Util.subst_of_list xs3 args)
in (FStar_Syntax_Subst.subst uu____17458 k3)))
end))
end
| uu____17461 -> begin
(

let uu____17462 = (

let uu____17463 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____17464 = (FStar_Syntax_Print.binders_to_string ", " xs2)
in (

let uu____17465 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" uu____17463 uu____17464 uu____17465))))
in (failwith uu____17462))
end)
end))))
in (

let uu____17466 = (

let uu____17473 = (

let uu____17486 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals uu____17486))
in (match (uu____17473) with
| (bs, k1') -> begin
(

let uu____17511 = (

let uu____17524 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals uu____17524))
in (match (uu____17511) with
| (cs, k2') -> begin
(

let k1'_xs = (subst_k k1' bs args1)
in (

let k2'_ys = (subst_k k2' cs args2)
in (

let sub_prob = (

let uu____17552 = (

let uu____17557 = (p_scope orig)
in (mk_problem uu____17557 orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys FStar_Pervasives_Native.None "flex-flex kinding"))
in (FStar_All.pipe_left (fun _0_40 -> FStar_TypeChecker_Common.TProb (_0_40)) uu____17552))
in (

let uu____17562 = (

let uu____17567 = (

let uu____17568 = (FStar_Syntax_Subst.compress k1')
in uu____17568.FStar_Syntax_Syntax.n)
in (

let uu____17571 = (

let uu____17572 = (FStar_Syntax_Subst.compress k2')
in uu____17572.FStar_Syntax_Syntax.n)
in ((uu____17567), (uu____17571))))
in (match (uu____17562) with
| (FStar_Syntax_Syntax.Tm_type (uu____17581), uu____17582) -> begin
((k1'_xs), ((sub_prob)::[]))
end
| (uu____17585, FStar_Syntax_Syntax.Tm_type (uu____17586)) -> begin
((k2'_ys), ((sub_prob)::[]))
end
| uu____17589 -> begin
(

let uu____17594 = (FStar_Syntax_Util.type_u ())
in (match (uu____17594) with
| (t, uu____17606) -> begin
(

let uu____17607 = (new_uvar r zs t)
in (match (uu____17607) with
| (k_zs, uu____17619) -> begin
(

let kprob = (

let uu____17621 = (

let uu____17626 = (p_scope orig)
in (mk_problem uu____17626 orig k1'_xs FStar_TypeChecker_Common.EQ k_zs FStar_Pervasives_Native.None "flex-flex kinding"))
in (FStar_All.pipe_left (fun _0_41 -> FStar_TypeChecker_Common.TProb (_0_41)) uu____17621))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end)))))
end))
end))
in (match (uu____17466) with
| (k_u', sub_probs) -> begin
(

let uu____17639 = (

let uu____17650 = (

let uu____17651 = (new_uvar r zs k_u')
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____17651))
in (

let uu____17660 = (

let uu____17663 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs1 uu____17663))
in (

let uu____17666 = (

let uu____17669 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys1 uu____17669))
in ((uu____17650), (uu____17660), (uu____17666)))))
in (match (uu____17639) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs1 u_zs)
in (

let uu____17688 = (occurs_check env wl1 ((u1), (k1)) sub1)
in (match (uu____17688) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occcurs check")
end
| uu____17701 -> begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in (

let uu____17707 = (FStar_Syntax_Unionfind.equiv u1 u2)
in (match (uu____17707) with
| true -> begin
(

let wl2 = (solve_prob orig FStar_Pervasives_Native.None ((sol1)::[]) wl1)
in (solve env wl2))
end
| uu____17709 -> begin
(

let sub2 = (u_abs knew2 ys1 u_zs)
in (

let uu____17711 = (occurs_check env wl1 ((u2), (k2)) sub2)
in (match (uu____17711) with
| (occurs_ok1, msg1) -> begin
(match ((not (occurs_ok1))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occurs check")
end
| uu____17724 -> begin
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

let solve_one_pat = (fun uu____17768 uu____17769 -> (match (((uu____17768), (uu____17769))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
((

let uu____17887 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____17887) with
| true -> begin
(

let uu____17888 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____17889 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" uu____17888 uu____17889)))
end
| uu____17890 -> begin
()
end));
(

let uu____17891 = (FStar_Syntax_Unionfind.equiv u1 u2)
in (match (uu____17891) with
| true -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____17910 uu____17911 -> (match (((uu____17910), (uu____17911))) with
| ((a, uu____17929), (t21, uu____17931)) -> begin
(

let uu____17940 = (

let uu____17945 = (p_scope orig)
in (

let uu____17946 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem uu____17945 orig uu____17946 FStar_TypeChecker_Common.EQ t21 FStar_Pervasives_Native.None "flex-flex index")))
in (FStar_All.pipe_right uu____17940 (fun _0_42 -> FStar_TypeChecker_Common.TProb (_0_42))))
end)) xs args2)
in (

let guard = (

let uu____17952 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) FStar_Pervasives_Native.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____17952))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))))
end
| uu____17962 -> begin
(

let t21 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t21)
in (

let uu____17967 = (occurs_check env wl ((u1), (k1)) t21)
in (match (uu____17967) with
| (occurs_ok, uu____17975) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in (

let uu____17983 = (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars))
in (match (uu____17983) with
| true -> begin
(

let sol = (

let uu____17985 = (

let uu____17994 = (u_abs k1 xs t21)
in ((((u1), (k1))), (uu____17994)))
in TERM (uu____17985))
in (

let wl1 = (solve_prob orig FStar_Pervasives_Native.None ((sol)::[]) wl)
in (solve env wl1)))
end
| uu____18000 -> begin
(

let uu____18001 = (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok))
in (match (uu____18001) with
| true -> begin
(

let uu____18002 = (force_quasi_pattern (FStar_Pervasives_Native.Some (xs)) ((t21), (u2), (k2), (args2)))
in (match (uu____18002) with
| FStar_Pervasives_Native.None -> begin
(giveup_or_defer1 orig "flex-flex constraint")
end
| FStar_Pervasives_Native.Some (sol, (uu____18026, u21, k21, ys)) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____18052 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____18052) with
| true -> begin
(

let uu____18053 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" uu____18053))
end
| uu____18054 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____18060 -> begin
(giveup env "impossible" orig)
end);
))
end))
end
| uu____18061 -> begin
(giveup_or_defer1 orig "flex-flex constraint")
end))
end)))
end))))
end));
)
end))
in (

let uu____18062 = lhs
in (match (uu____18062) with
| (t1, u1, k1, args1) -> begin
(

let uu____18067 = rhs
in (match (uu____18067) with
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
| uu____18107 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: neither side is a pattern")
end
| uu____18116 -> begin
(

let uu____18117 = (force_quasi_pattern FStar_Pervasives_Native.None ((t1), (u1), (k1), (args1)))
in (match (uu____18117) with
| FStar_Pervasives_Native.None -> begin
(giveup env "flex-flex: neither side is a pattern, nor is coercible to a pattern" orig)
end
| FStar_Pervasives_Native.Some (sol, uu____18135) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____18142 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____18142) with
| true -> begin
(

let uu____18143 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" uu____18143))
end
| uu____18144 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____18150 -> begin
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

let uu____18153 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____18153) with
| true -> begin
(

let uu____18154 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____18154))
end
| uu____18155 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in (

let uu____18158 = (FStar_Util.physical_equality t1 t2)
in (match (uu____18158) with
| true -> begin
(

let uu____18159 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____18159))
end
| uu____18160 -> begin
((

let uu____18162 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____18162) with
| true -> begin
(

let uu____18163 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____18164 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____18165 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print3 "Attempting %s (%s - %s)\n" uu____18163 uu____18164 uu____18165))))
end
| uu____18166 -> begin
()
end));
(

let r = (FStar_TypeChecker_Env.get_range env)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_delayed (uu____18168), uu____18169) -> begin
(failwith "Impossible: terms were not compressed")
end
| (uu____18194, FStar_Syntax_Syntax.Tm_delayed (uu____18195)) -> begin
(failwith "Impossible: terms were not compressed")
end
| (FStar_Syntax_Syntax.Tm_ascribed (uu____18220), uu____18221) -> begin
(

let uu____18248 = (

let uu___153_18249 = problem
in (

let uu____18250 = (FStar_Syntax_Util.unascribe t1)
in {FStar_TypeChecker_Common.pid = uu___153_18249.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____18250; FStar_TypeChecker_Common.relation = uu___153_18249.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___153_18249.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___153_18249.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___153_18249.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___153_18249.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___153_18249.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___153_18249.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___153_18249.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____18248 wl))
end
| (FStar_Syntax_Syntax.Tm_meta (uu____18251), uu____18252) -> begin
(

let uu____18259 = (

let uu___154_18260 = problem
in (

let uu____18261 = (FStar_Syntax_Util.unmeta t1)
in {FStar_TypeChecker_Common.pid = uu___154_18260.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____18261; FStar_TypeChecker_Common.relation = uu___154_18260.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___154_18260.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___154_18260.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___154_18260.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___154_18260.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___154_18260.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___154_18260.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___154_18260.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____18259 wl))
end
| (uu____18262, FStar_Syntax_Syntax.Tm_ascribed (uu____18263)) -> begin
(

let uu____18290 = (

let uu___155_18291 = problem
in (

let uu____18292 = (FStar_Syntax_Util.unascribe t2)
in {FStar_TypeChecker_Common.pid = uu___155_18291.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___155_18291.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___155_18291.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____18292; FStar_TypeChecker_Common.element = uu___155_18291.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___155_18291.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___155_18291.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___155_18291.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___155_18291.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___155_18291.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____18290 wl))
end
| (uu____18293, FStar_Syntax_Syntax.Tm_meta (uu____18294)) -> begin
(

let uu____18301 = (

let uu___156_18302 = problem
in (

let uu____18303 = (FStar_Syntax_Util.unmeta t2)
in {FStar_TypeChecker_Common.pid = uu___156_18302.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___156_18302.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___156_18302.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____18303; FStar_TypeChecker_Common.element = uu___156_18302.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___156_18302.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___156_18302.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___156_18302.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___156_18302.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___156_18302.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____18301 wl))
end
| (FStar_Syntax_Syntax.Tm_quoted (t11, uu____18305), FStar_Syntax_Syntax.Tm_quoted (t21, uu____18307)) -> begin
(

let uu____18316 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____18316))
end
| (FStar_Syntax_Syntax.Tm_bvar (uu____18317), uu____18318) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (uu____18319, FStar_Syntax_Syntax.Tm_bvar (uu____18320)) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (FStar_Syntax_Syntax.Tm_type (u1), FStar_Syntax_Syntax.Tm_type (u2)) -> begin
(solve_one_universe_eq env orig u1 u2 wl)
end
| (FStar_Syntax_Syntax.Tm_arrow (bs1, c1), FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) -> begin
(

let mk_c = (fun c uu___117_18379 -> (match (uu___117_18379) with
| [] -> begin
c
end
| bs -> begin
(

let uu____18401 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____18401))
end))
in (

let uu____18410 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____18410) with
| ((bs11, c11), (bs21, c21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let c12 = (FStar_Syntax_Subst.subst_comp subst1 c11)
in (

let c22 = (FStar_Syntax_Subst.subst_comp subst1 c21)
in (

let rel = (

let uu____18554 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____18554) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____18555 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (

let uu____18556 = (mk_problem scope orig c12 rel c22 FStar_Pervasives_Native.None "function co-domain")
in (FStar_All.pipe_left (fun _0_43 -> FStar_TypeChecker_Common.CProb (_0_43)) uu____18556)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___118_18638 -> (match (uu___118_18638) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____18672 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____18672) with
| ((bs11, tbody11), (bs21, tbody21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let uu____18810 = (

let uu____18815 = (FStar_Syntax_Subst.subst subst1 tbody11)
in (

let uu____18816 = (FStar_Syntax_Subst.subst subst1 tbody21)
in (mk_problem scope orig uu____18815 problem.FStar_TypeChecker_Common.relation uu____18816 FStar_Pervasives_Native.None "lambda co-domain")))
in (FStar_All.pipe_left (fun _0_44 -> FStar_TypeChecker_Common.TProb (_0_44)) uu____18810))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (uu____18821), uu____18822) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____18849) -> begin
true
end
| uu____18866 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____18891 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____18899 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let force_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
t
end
| uu____18916 -> begin
(

let uu____18917 = (env.FStar_TypeChecker_Env.type_of (

let uu___157_18925 = env
in {FStar_TypeChecker_Env.solver = uu___157_18925.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___157_18925.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___157_18925.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___157_18925.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___157_18925.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___157_18925.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___157_18925.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___157_18925.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___157_18925.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___157_18925.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___157_18925.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___157_18925.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___157_18925.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___157_18925.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___157_18925.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___157_18925.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___157_18925.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___157_18925.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___157_18925.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___157_18925.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___157_18925.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___157_18925.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___157_18925.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___157_18925.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___157_18925.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___157_18925.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___157_18925.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___157_18925.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___157_18925.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___157_18925.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___157_18925.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___157_18925.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___157_18925.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___157_18925.FStar_TypeChecker_Env.dep_graph}) t)
in (match (uu____18917) with
| (uu____18928, ty, uu____18930) -> begin
(

let uu____18931 = (FStar_TypeChecker_Normalize.unfold_whnf env ty)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env t uu____18931))
end))
end))
in (

let uu____18932 = (

let uu____18949 = (maybe_eta t1)
in (

let uu____18956 = (maybe_eta t2)
in ((uu____18949), (uu____18956))))
in (match (uu____18932) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___158_18998 = problem
in {FStar_TypeChecker_Common.pid = uu___158_18998.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___158_18998.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___158_18998.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___158_18998.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___158_18998.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___158_18998.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___158_18998.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___158_18998.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____19021 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____19021) with
| true -> begin
(

let uu____19022 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____19022 t_abs wl))
end
| uu____19029 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___159_19037 = problem
in {FStar_TypeChecker_Common.pid = uu___159_19037.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___159_19037.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___159_19037.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___159_19037.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___159_19037.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___159_19037.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___159_19037.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___159_19037.FStar_TypeChecker_Common.rank}) wl)
end
| uu____19040 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____19061 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____19061) with
| true -> begin
(

let uu____19062 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____19062 t_abs wl))
end
| uu____19069 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___159_19077 = problem
in {FStar_TypeChecker_Common.pid = uu___159_19077.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___159_19077.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___159_19077.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___159_19077.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___159_19077.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___159_19077.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___159_19077.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___159_19077.FStar_TypeChecker_Common.rank}) wl)
end
| uu____19080 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| uu____19081 -> begin
(failwith "Impossible: at least one side is an abstraction")
end)))))
end
| (uu____19098, FStar_Syntax_Syntax.Tm_abs (uu____19099)) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____19126) -> begin
true
end
| uu____19143 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____19168 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____19176 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let force_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
t
end
| uu____19193 -> begin
(

let uu____19194 = (env.FStar_TypeChecker_Env.type_of (

let uu___157_19202 = env
in {FStar_TypeChecker_Env.solver = uu___157_19202.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___157_19202.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___157_19202.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___157_19202.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___157_19202.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___157_19202.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___157_19202.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___157_19202.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___157_19202.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___157_19202.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___157_19202.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___157_19202.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___157_19202.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___157_19202.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___157_19202.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___157_19202.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___157_19202.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___157_19202.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___157_19202.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___157_19202.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___157_19202.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___157_19202.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___157_19202.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___157_19202.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___157_19202.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___157_19202.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___157_19202.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___157_19202.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___157_19202.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___157_19202.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___157_19202.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___157_19202.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___157_19202.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___157_19202.FStar_TypeChecker_Env.dep_graph}) t)
in (match (uu____19194) with
| (uu____19205, ty, uu____19207) -> begin
(

let uu____19208 = (FStar_TypeChecker_Normalize.unfold_whnf env ty)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env t uu____19208))
end))
end))
in (

let uu____19209 = (

let uu____19226 = (maybe_eta t1)
in (

let uu____19233 = (maybe_eta t2)
in ((uu____19226), (uu____19233))))
in (match (uu____19209) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___158_19275 = problem
in {FStar_TypeChecker_Common.pid = uu___158_19275.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___158_19275.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___158_19275.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___158_19275.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___158_19275.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___158_19275.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___158_19275.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___158_19275.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____19298 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____19298) with
| true -> begin
(

let uu____19299 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____19299 t_abs wl))
end
| uu____19306 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___159_19314 = problem
in {FStar_TypeChecker_Common.pid = uu___159_19314.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___159_19314.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___159_19314.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___159_19314.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___159_19314.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___159_19314.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___159_19314.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___159_19314.FStar_TypeChecker_Common.rank}) wl)
end
| uu____19317 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____19338 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____19338) with
| true -> begin
(

let uu____19339 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____19339 t_abs wl))
end
| uu____19346 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___159_19354 = problem
in {FStar_TypeChecker_Common.pid = uu___159_19354.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___159_19354.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___159_19354.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___159_19354.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___159_19354.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___159_19354.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___159_19354.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___159_19354.FStar_TypeChecker_Common.rank}) wl)
end
| uu____19357 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| uu____19358 -> begin
(failwith "Impossible: at least one side is an abstraction")
end)))))
end
| (FStar_Syntax_Syntax.Tm_refine (x1, ph1), FStar_Syntax_Syntax.Tm_refine (x2, phi2)) -> begin
(

let should_delta = (((

let uu____19390 = (FStar_Syntax_Free.uvars t1)
in (FStar_Util.set_is_empty uu____19390)) && (

let uu____19402 = (FStar_Syntax_Free.uvars t2)
in (FStar_Util.set_is_empty uu____19402))) && (

let uu____19417 = (head_matches env x1.FStar_Syntax_Syntax.sort x2.FStar_Syntax_Syntax.sort)
in (match (uu____19417) with
| MisMatch (FStar_Pervasives_Native.Some (d1), FStar_Pervasives_Native.Some (d2)) -> begin
(

let is_unfoldable = (fun uu___119_19429 -> (match (uu___119_19429) with
| FStar_Syntax_Syntax.Delta_constant_at_level (uu____19430) -> begin
true
end
| uu____19431 -> begin
false
end))
in ((is_unfoldable d1) && (is_unfoldable d2)))
end
| uu____19432 -> begin
false
end)))
in (

let uu____19433 = (as_refinement should_delta env wl t1)
in (match (uu____19433) with
| (x11, phi1) -> begin
(

let uu____19440 = (as_refinement should_delta env wl t2)
in (match (uu____19440) with
| (x21, phi21) -> begin
(

let base_prob = (

let uu____19448 = (

let uu____19453 = (p_scope orig)
in (mk_problem uu____19453 orig x11.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x21.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type"))
in (FStar_All.pipe_left (fun _0_45 -> FStar_TypeChecker_Common.TProb (_0_45)) uu____19448))
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

let uu____19493 = (imp phi12 phi23)
in (FStar_All.pipe_right uu____19493 (guard_on_element wl problem x12))))
in (

let fallback = (fun uu____19499 -> (

let impl = (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp1 FStar_Syntax_Util.mk_iff phi11 phi22)
end
| uu____19501 -> begin
(mk_imp1 FStar_Syntax_Util.mk_imp phi11 phi22)
end)
in (

let guard = (

let uu____19505 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____19505 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env1 (attempt ((base_prob)::[]) wl1))))))
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let ref_prob = (

let uu____19514 = (

let uu____19519 = (

let uu____19520 = (p_scope orig)
in (

let uu____19527 = (

let uu____19534 = (FStar_Syntax_Syntax.mk_binder x12)
in (uu____19534)::[])
in (FStar_List.append uu____19520 uu____19527)))
in (mk_problem uu____19519 orig phi11 FStar_TypeChecker_Common.EQ phi22 FStar_Pervasives_Native.None "refinement formula"))
in (FStar_All.pipe_left (fun _0_46 -> FStar_TypeChecker_Common.TProb (_0_46)) uu____19514))
in (

let uu____19543 = (solve env1 (

let uu___160_19545 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___160_19545.ctr; defer_ok = false; smt_ok = uu___160_19545.smt_ok; tcenv = uu___160_19545.tcenv}))
in (match (uu____19543) with
| Failed (uu____19552) -> begin
(fallback ())
end
| Success (uu____19557) -> begin
(

let guard = (

let uu____19561 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (

let uu____19566 = (

let uu____19567 = (FStar_All.pipe_right (p_guard ref_prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____19567 (guard_on_element wl problem x12)))
in (FStar_Syntax_Util.mk_conj uu____19561 uu____19566)))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (

let wl2 = (

let uu___161_19576 = wl1
in {attempting = uu___161_19576.attempting; wl_deferred = uu___161_19576.wl_deferred; ctr = (wl1.ctr + (Prims.parse_int "1")); defer_ok = uu___161_19576.defer_ok; smt_ok = uu___161_19576.smt_ok; tcenv = uu___161_19576.tcenv})
in (solve env1 (attempt ((base_prob)::[]) wl2)))))
end)))
end
| uu____19577 -> begin
(fallback ())
end)))))))))
end))
end)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____19578), FStar_Syntax_Syntax.Tm_uvar (uu____19579)) -> begin
(

let uu____19612 = (destruct_flex_t t1)
in (

let uu____19613 = (destruct_flex_t t2)
in (flex_flex1 orig uu____19612 uu____19613)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19614); FStar_Syntax_Syntax.pos = uu____19615; FStar_Syntax_Syntax.vars = uu____19616}, uu____19617), FStar_Syntax_Syntax.Tm_uvar (uu____19618)) -> begin
(

let uu____19671 = (destruct_flex_t t1)
in (

let uu____19672 = (destruct_flex_t t2)
in (flex_flex1 orig uu____19671 uu____19672)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____19673), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19674); FStar_Syntax_Syntax.pos = uu____19675; FStar_Syntax_Syntax.vars = uu____19676}, uu____19677)) -> begin
(

let uu____19730 = (destruct_flex_t t1)
in (

let uu____19731 = (destruct_flex_t t2)
in (flex_flex1 orig uu____19730 uu____19731)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19732); FStar_Syntax_Syntax.pos = uu____19733; FStar_Syntax_Syntax.vars = uu____19734}, uu____19735), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19736); FStar_Syntax_Syntax.pos = uu____19737; FStar_Syntax_Syntax.vars = uu____19738}, uu____19739)) -> begin
(

let uu____19812 = (destruct_flex_t t1)
in (

let uu____19813 = (destruct_flex_t t2)
in (flex_flex1 orig uu____19812 uu____19813)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____19814), uu____19815) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(

let uu____19832 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____19832 t2 wl))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19839); FStar_Syntax_Syntax.pos = uu____19840; FStar_Syntax_Syntax.vars = uu____19841}, uu____19842), uu____19843) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(

let uu____19880 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____19880 t2 wl))
end
| (uu____19887, FStar_Syntax_Syntax.Tm_uvar (uu____19888)) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (uu____19905, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19906); FStar_Syntax_Syntax.pos = uu____19907; FStar_Syntax_Syntax.vars = uu____19908}, uu____19909)) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____19946), FStar_Syntax_Syntax.Tm_type (uu____19947)) -> begin
(solve_t' env (

let uu___162_19965 = problem
in {FStar_TypeChecker_Common.pid = uu___162_19965.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___162_19965.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___162_19965.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___162_19965.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_19965.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_19965.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_19965.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_19965.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_19965.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19966); FStar_Syntax_Syntax.pos = uu____19967; FStar_Syntax_Syntax.vars = uu____19968}, uu____19969), FStar_Syntax_Syntax.Tm_type (uu____19970)) -> begin
(solve_t' env (

let uu___162_20008 = problem
in {FStar_TypeChecker_Common.pid = uu___162_20008.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___162_20008.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___162_20008.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___162_20008.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_20008.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_20008.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_20008.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_20008.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_20008.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____20009), FStar_Syntax_Syntax.Tm_arrow (uu____20010)) -> begin
(solve_t' env (

let uu___162_20040 = problem
in {FStar_TypeChecker_Common.pid = uu___162_20040.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___162_20040.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___162_20040.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___162_20040.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_20040.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_20040.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_20040.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_20040.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_20040.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____20041); FStar_Syntax_Syntax.pos = uu____20042; FStar_Syntax_Syntax.vars = uu____20043}, uu____20044), FStar_Syntax_Syntax.Tm_arrow (uu____20045)) -> begin
(solve_t' env (

let uu___162_20095 = problem
in {FStar_TypeChecker_Common.pid = uu___162_20095.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___162_20095.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___162_20095.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___162_20095.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_20095.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_20095.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_20095.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_20095.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_20095.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____20096), uu____20097) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____20114 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____20116 = (

let uu____20117 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____20117))
in (match (uu____20116) with
| true -> begin
(

let uu____20118 = (FStar_All.pipe_left (fun _0_47 -> FStar_TypeChecker_Common.TProb (_0_47)) (

let uu___163_20124 = problem
in {FStar_TypeChecker_Common.pid = uu___163_20124.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___163_20124.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___163_20124.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___163_20124.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___163_20124.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___163_20124.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___163_20124.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___163_20124.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___163_20124.FStar_TypeChecker_Common.rank}))
in (

let uu____20125 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____20118 uu____20125 t2 wl)))
end
| uu____20132 -> begin
(

let uu____20133 = (base_and_refinement env t2)
in (match (uu____20133) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____20162 = (FStar_All.pipe_left (fun _0_48 -> FStar_TypeChecker_Common.TProb (_0_48)) (

let uu___164_20168 = problem
in {FStar_TypeChecker_Common.pid = uu___164_20168.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___164_20168.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___164_20168.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___164_20168.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_20168.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_20168.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_20168.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_20168.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_20168.FStar_TypeChecker_Common.rank}))
in (

let uu____20169 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____20162 uu____20169 t_base wl)))
end
| FStar_Pervasives_Native.Some (y, phi) -> begin
(

let y' = (

let uu___165_20183 = y
in {FStar_Syntax_Syntax.ppname = uu___165_20183.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___165_20183.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let base_prob = (

let uu____20186 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_49 -> FStar_TypeChecker_Common.TProb (_0_49)) uu____20186))
in (

let guard = (

let uu____20198 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____20198 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl1)))))))
end)
end))
end)))
end)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____20206); FStar_Syntax_Syntax.pos = uu____20207; FStar_Syntax_Syntax.vars = uu____20208}, uu____20209), uu____20210) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____20247 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____20249 = (

let uu____20250 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____20250))
in (match (uu____20249) with
| true -> begin
(

let uu____20251 = (FStar_All.pipe_left (fun _0_50 -> FStar_TypeChecker_Common.TProb (_0_50)) (

let uu___163_20257 = problem
in {FStar_TypeChecker_Common.pid = uu___163_20257.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___163_20257.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___163_20257.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___163_20257.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___163_20257.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___163_20257.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___163_20257.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___163_20257.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___163_20257.FStar_TypeChecker_Common.rank}))
in (

let uu____20258 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____20251 uu____20258 t2 wl)))
end
| uu____20265 -> begin
(

let uu____20266 = (base_and_refinement env t2)
in (match (uu____20266) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____20295 = (FStar_All.pipe_left (fun _0_51 -> FStar_TypeChecker_Common.TProb (_0_51)) (

let uu___164_20301 = problem
in {FStar_TypeChecker_Common.pid = uu___164_20301.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___164_20301.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___164_20301.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___164_20301.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_20301.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_20301.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_20301.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_20301.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_20301.FStar_TypeChecker_Common.rank}))
in (

let uu____20302 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____20295 uu____20302 t_base wl)))
end
| FStar_Pervasives_Native.Some (y, phi) -> begin
(

let y' = (

let uu___165_20316 = y
in {FStar_Syntax_Syntax.ppname = uu___165_20316.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___165_20316.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let base_prob = (

let uu____20319 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_52 -> FStar_TypeChecker_Common.TProb (_0_52)) uu____20319))
in (

let guard = (

let uu____20331 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____20331 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl1)))))))
end)
end))
end)))
end)
end
| (uu____20339, FStar_Syntax_Syntax.Tm_uvar (uu____20340)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| uu____20357 -> begin
(

let uu____20358 = (base_and_refinement env t1)
in (match (uu____20358) with
| (t_base, uu____20370) -> begin
(solve_t env (

let uu___166_20384 = problem
in {FStar_TypeChecker_Common.pid = uu___166_20384.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___166_20384.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___166_20384.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_20384.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___166_20384.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___166_20384.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_20384.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_20384.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (uu____20385, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____20386); FStar_Syntax_Syntax.pos = uu____20387; FStar_Syntax_Syntax.vars = uu____20388}, uu____20389)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| uu____20426 -> begin
(

let uu____20427 = (base_and_refinement env t1)
in (match (uu____20427) with
| (t_base, uu____20439) -> begin
(solve_t env (

let uu___166_20453 = problem
in {FStar_TypeChecker_Common.pid = uu___166_20453.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___166_20453.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___166_20453.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_20453.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___166_20453.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___166_20453.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_20453.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_20453.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____20455; FStar_Syntax_Syntax.vars = uu____20456}, uu____20457); FStar_Syntax_Syntax.pos = uu____20458; FStar_Syntax_Syntax.vars = uu____20459}, uu____20460), uu____20461) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.t_refine_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.p_refine_lid)) -> begin
(

let t11 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t1)
in (solve_t env (

let uu___167_20488 = problem
in {FStar_TypeChecker_Common.pid = uu___167_20488.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___167_20488.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___167_20488.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___167_20488.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___167_20488.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___167_20488.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___167_20488.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___167_20488.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___167_20488.FStar_TypeChecker_Common.rank}) wl))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____20490; FStar_Syntax_Syntax.vars = uu____20491}, uu____20492), uu____20493) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.t_refine_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.p_refine_lid)) -> begin
(

let t11 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t1)
in (solve_t env (

let uu___167_20516 = problem
in {FStar_TypeChecker_Common.pid = uu___167_20516.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___167_20516.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___167_20516.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___167_20516.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___167_20516.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___167_20516.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___167_20516.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___167_20516.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___167_20516.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____20517, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____20519; FStar_Syntax_Syntax.vars = uu____20520}, uu____20521); FStar_Syntax_Syntax.pos = uu____20522; FStar_Syntax_Syntax.vars = uu____20523}, uu____20524)) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.t_refine_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.p_refine_lid)) -> begin
(

let t21 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t2)
in (solve_t env (

let uu___168_20551 = problem
in {FStar_TypeChecker_Common.pid = uu___168_20551.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___168_20551.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___168_20551.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___168_20551.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___168_20551.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___168_20551.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___168_20551.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___168_20551.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___168_20551.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____20552, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____20554; FStar_Syntax_Syntax.vars = uu____20555}, uu____20556)) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.t_refine_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.p_refine_lid)) -> begin
(

let t21 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t2)
in (solve_t env (

let uu___168_20579 = problem
in {FStar_TypeChecker_Common.pid = uu___168_20579.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___168_20579.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___168_20579.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___168_20579.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___168_20579.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___168_20579.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___168_20579.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___168_20579.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___168_20579.FStar_TypeChecker_Common.rank}) wl))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____20580), uu____20581) -> begin
(

let t21 = (

let uu____20591 = (base_and_refinement env t2)
in (FStar_All.pipe_left force_refinement uu____20591))
in (solve_t env (

let uu___169_20615 = problem
in {FStar_TypeChecker_Common.pid = uu___169_20615.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___169_20615.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___169_20615.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___169_20615.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___169_20615.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___169_20615.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___169_20615.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___169_20615.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___169_20615.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____20616, FStar_Syntax_Syntax.Tm_refine (uu____20617)) -> begin
(

let t11 = (

let uu____20627 = (base_and_refinement env t1)
in (FStar_All.pipe_left force_refinement uu____20627))
in (solve_t env (

let uu___170_20651 = problem
in {FStar_TypeChecker_Common.pid = uu___170_20651.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___170_20651.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___170_20651.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___170_20651.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___170_20651.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___170_20651.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___170_20651.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___170_20651.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___170_20651.FStar_TypeChecker_Common.rank}) wl))
end
| (FStar_Syntax_Syntax.Tm_match (t11, brs1), FStar_Syntax_Syntax.Tm_match (t21, brs2)) -> begin
(

let sc_prob = (

let uu____20731 = (

let uu____20736 = (p_scope orig)
in (mk_problem uu____20736 orig t11 FStar_TypeChecker_Common.EQ t21 FStar_Pervasives_Native.None "match scrutinee"))
in (FStar_All.pipe_left (fun _0_53 -> FStar_TypeChecker_Common.TProb (_0_53)) uu____20731))
in (

let rec solve_branches = (fun brs11 brs21 -> (match (((brs11), (brs21))) with
| ((br1)::rs1, (br2)::rs2) -> begin
(

let uu____20926 = br1
in (match (uu____20926) with
| (p1, w1, uu____20945) -> begin
(

let uu____20958 = br2
in (match (uu____20958) with
| (p2, w2, uu____20973) -> begin
(

let uu____20978 = (

let uu____20979 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (not (uu____20979)))
in (match (uu____20978) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____20986 -> begin
(

let uu____20987 = (FStar_Syntax_Subst.open_branch' br1)
in (match (uu____20987) with
| ((p11, w11, e1), s) -> begin
(

let uu____21030 = br2
in (match (uu____21030) with
| (p21, w21, e2) -> begin
(

let w22 = (FStar_Util.map_opt w21 (FStar_Syntax_Subst.subst s))
in (

let e21 = (FStar_Syntax_Subst.subst s e2)
in (

let scope = (

let uu____21061 = (p_scope orig)
in (

let uu____21068 = (

let uu____21075 = (FStar_Syntax_Syntax.pat_bvs p11)
in (FStar_All.pipe_left (FStar_List.map FStar_Syntax_Syntax.mk_binder) uu____21075))
in (FStar_List.append uu____21061 uu____21068)))
in (

let uu____21086 = (match (((w11), (w22))) with
| (FStar_Pervasives_Native.Some (uu____21101), FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (uu____21114)) -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Pervasives_Native.Some (w12), FStar_Pervasives_Native.Some (w23)) -> begin
(

let uu____21147 = (

let uu____21150 = (

let uu____21151 = (mk_problem scope orig w12 FStar_TypeChecker_Common.EQ w23 FStar_Pervasives_Native.None "when clause")
in (FStar_All.pipe_left (fun _0_54 -> FStar_TypeChecker_Common.TProb (_0_54)) uu____21151))
in (uu____21150)::[])
in FStar_Pervasives_Native.Some (uu____21147))
end)
in (FStar_Util.bind_opt uu____21086 (fun wprobs -> (

let prob = (

let uu____21175 = (mk_problem scope orig e1 FStar_TypeChecker_Common.EQ e21 FStar_Pervasives_Native.None "branch body")
in (FStar_All.pipe_left (fun _0_55 -> FStar_TypeChecker_Common.TProb (_0_55)) uu____21175))
in (

let uu____21186 = (solve_branches rs1 rs2)
in (FStar_Util.bind_opt uu____21186 (fun r1 -> FStar_Pervasives_Native.Some ((prob)::(FStar_List.append wprobs r1))))))))))))
end))
end))
end))
end))
end))
end
| ([], []) -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____21247 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____21278 = (solve_branches brs1 brs2)
in (match (uu____21278) with
| FStar_Pervasives_Native.None -> begin
(giveup env "Tm_match branches don\'t match" orig)
end
| FStar_Pervasives_Native.Some (sub_probs) -> begin
(

let sub_probs1 = (sc_prob)::sub_probs
in (

let wl1 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env (attempt sub_probs1 wl1))))
end))))
end
| (FStar_Syntax_Syntax.Tm_match (uu____21294), uu____21295) -> begin
(

let head1 = (

let uu____21321 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____21321 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____21365 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____21365 FStar_Pervasives_Native.fst))
in ((

let uu____21407 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____21407) with
| true -> begin
(

let uu____21408 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____21409 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____21410 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____21408 uu____21409 uu____21410))))
end
| uu____21411 -> begin
()
end));
(

let uu____21412 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____21412) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____21427 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____21427) with
| true -> begin
(

let guard = (

let uu____21439 = (

let uu____21440 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____21440 FStar_Syntax_Util.Equal))
in (match (uu____21439) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____21443 -> begin
(

let uu____21444 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_56 -> FStar_Pervasives_Native.Some (_0_56)) uu____21444))
end))
in (

let uu____21447 = (solve_prob orig guard [] wl)
in (solve env uu____21447)))
end
| uu____21448 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____21449 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____21450), uu____21451) -> begin
(

let head1 = (

let uu____21461 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____21461 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____21505 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____21505 FStar_Pervasives_Native.fst))
in ((

let uu____21547 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____21547) with
| true -> begin
(

let uu____21548 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____21549 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____21550 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____21548 uu____21549 uu____21550))))
end
| uu____21551 -> begin
()
end));
(

let uu____21552 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____21552) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____21567 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____21567) with
| true -> begin
(

let guard = (

let uu____21579 = (

let uu____21580 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____21580 FStar_Syntax_Util.Equal))
in (match (uu____21579) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____21583 -> begin
(

let uu____21584 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_57 -> FStar_Pervasives_Native.Some (_0_57)) uu____21584))
end))
in (

let uu____21587 = (solve_prob orig guard [] wl)
in (solve env uu____21587)))
end
| uu____21588 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____21589 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_name (uu____21590), uu____21591) -> begin
(

let head1 = (

let uu____21595 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____21595 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____21639 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____21639 FStar_Pervasives_Native.fst))
in ((

let uu____21681 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____21681) with
| true -> begin
(

let uu____21682 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____21683 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____21684 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____21682 uu____21683 uu____21684))))
end
| uu____21685 -> begin
()
end));
(

let uu____21686 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____21686) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____21701 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____21701) with
| true -> begin
(

let guard = (

let uu____21713 = (

let uu____21714 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____21714 FStar_Syntax_Util.Equal))
in (match (uu____21713) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____21717 -> begin
(

let uu____21718 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_58 -> FStar_Pervasives_Native.Some (_0_58)) uu____21718))
end))
in (

let uu____21721 = (solve_prob orig guard [] wl)
in (solve env uu____21721)))
end
| uu____21722 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____21723 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_constant (uu____21724), uu____21725) -> begin
(

let head1 = (

let uu____21729 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____21729 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____21773 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____21773 FStar_Pervasives_Native.fst))
in ((

let uu____21815 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
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

let uu____21820 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____21820) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____21835 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____21835) with
| true -> begin
(

let guard = (

let uu____21847 = (

let uu____21848 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____21848 FStar_Syntax_Util.Equal))
in (match (uu____21847) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____21851 -> begin
(

let uu____21852 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_59 -> FStar_Pervasives_Native.Some (_0_59)) uu____21852))
end))
in (

let uu____21855 = (solve_prob orig guard [] wl)
in (solve env uu____21855)))
end
| uu____21856 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____21857 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____21858), uu____21859) -> begin
(

let head1 = (

let uu____21863 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____21863 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____21907 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____21907 FStar_Pervasives_Native.fst))
in ((

let uu____21949 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____21949) with
| true -> begin
(

let uu____21950 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____21951 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____21952 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____21950 uu____21951 uu____21952))))
end
| uu____21953 -> begin
()
end));
(

let uu____21954 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____21954) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____21969 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____21969) with
| true -> begin
(

let guard = (

let uu____21981 = (

let uu____21982 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____21982 FStar_Syntax_Util.Equal))
in (match (uu____21981) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____21985 -> begin
(

let uu____21986 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_60 -> FStar_Pervasives_Native.Some (_0_60)) uu____21986))
end))
in (

let uu____21989 = (solve_prob orig guard [] wl)
in (solve env uu____21989)))
end
| uu____21990 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____21991 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_app (uu____21992), uu____21993) -> begin
(

let head1 = (

let uu____22011 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22011 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22055 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22055 FStar_Pervasives_Native.fst))
in ((

let uu____22097 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____22097) with
| true -> begin
(

let uu____22098 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22099 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22100 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22098 uu____22099 uu____22100))))
end
| uu____22101 -> begin
()
end));
(

let uu____22102 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____22102) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____22117 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____22117) with
| true -> begin
(

let guard = (

let uu____22129 = (

let uu____22130 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____22130 FStar_Syntax_Util.Equal))
in (match (uu____22129) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____22133 -> begin
(

let uu____22134 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_61 -> FStar_Pervasives_Native.Some (_0_61)) uu____22134))
end))
in (

let uu____22137 = (solve_prob orig guard [] wl)
in (solve env uu____22137)))
end
| uu____22138 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____22139 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____22140, FStar_Syntax_Syntax.Tm_match (uu____22141)) -> begin
(

let head1 = (

let uu____22167 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22167 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22211 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22211 FStar_Pervasives_Native.fst))
in ((

let uu____22253 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____22253) with
| true -> begin
(

let uu____22254 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22255 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22256 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22254 uu____22255 uu____22256))))
end
| uu____22257 -> begin
()
end));
(

let uu____22258 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____22258) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____22273 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____22273) with
| true -> begin
(

let guard = (

let uu____22285 = (

let uu____22286 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____22286 FStar_Syntax_Util.Equal))
in (match (uu____22285) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____22289 -> begin
(

let uu____22290 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_62 -> FStar_Pervasives_Native.Some (_0_62)) uu____22290))
end))
in (

let uu____22293 = (solve_prob orig guard [] wl)
in (solve env uu____22293)))
end
| uu____22294 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____22295 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____22296, FStar_Syntax_Syntax.Tm_uinst (uu____22297)) -> begin
(

let head1 = (

let uu____22307 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22307 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22351 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22351 FStar_Pervasives_Native.fst))
in ((

let uu____22393 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____22393) with
| true -> begin
(

let uu____22394 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22395 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22396 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22394 uu____22395 uu____22396))))
end
| uu____22397 -> begin
()
end));
(

let uu____22398 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____22398) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____22413 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____22413) with
| true -> begin
(

let guard = (

let uu____22425 = (

let uu____22426 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____22426 FStar_Syntax_Util.Equal))
in (match (uu____22425) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____22429 -> begin
(

let uu____22430 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_63 -> FStar_Pervasives_Native.Some (_0_63)) uu____22430))
end))
in (

let uu____22433 = (solve_prob orig guard [] wl)
in (solve env uu____22433)))
end
| uu____22434 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____22435 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____22436, FStar_Syntax_Syntax.Tm_name (uu____22437)) -> begin
(

let head1 = (

let uu____22441 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22441 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22485 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22485 FStar_Pervasives_Native.fst))
in ((

let uu____22527 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____22527) with
| true -> begin
(

let uu____22528 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22529 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22530 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22528 uu____22529 uu____22530))))
end
| uu____22531 -> begin
()
end));
(

let uu____22532 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____22532) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____22547 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____22547) with
| true -> begin
(

let guard = (

let uu____22559 = (

let uu____22560 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____22560 FStar_Syntax_Util.Equal))
in (match (uu____22559) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____22563 -> begin
(

let uu____22564 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_64 -> FStar_Pervasives_Native.Some (_0_64)) uu____22564))
end))
in (

let uu____22567 = (solve_prob orig guard [] wl)
in (solve env uu____22567)))
end
| uu____22568 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____22569 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____22570, FStar_Syntax_Syntax.Tm_constant (uu____22571)) -> begin
(

let head1 = (

let uu____22575 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22575 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22619 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22619 FStar_Pervasives_Native.fst))
in ((

let uu____22661 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____22661) with
| true -> begin
(

let uu____22662 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22663 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22664 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22662 uu____22663 uu____22664))))
end
| uu____22665 -> begin
()
end));
(

let uu____22666 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____22666) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____22681 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____22681) with
| true -> begin
(

let guard = (

let uu____22693 = (

let uu____22694 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____22694 FStar_Syntax_Util.Equal))
in (match (uu____22693) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____22697 -> begin
(

let uu____22698 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_65 -> FStar_Pervasives_Native.Some (_0_65)) uu____22698))
end))
in (

let uu____22701 = (solve_prob orig guard [] wl)
in (solve env uu____22701)))
end
| uu____22702 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____22703 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____22704, FStar_Syntax_Syntax.Tm_fvar (uu____22705)) -> begin
(

let head1 = (

let uu____22709 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22709 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22753 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22753 FStar_Pervasives_Native.fst))
in ((

let uu____22795 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____22795) with
| true -> begin
(

let uu____22796 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22797 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22798 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22796 uu____22797 uu____22798))))
end
| uu____22799 -> begin
()
end));
(

let uu____22800 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____22800) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____22815 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____22815) with
| true -> begin
(

let guard = (

let uu____22827 = (

let uu____22828 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____22828 FStar_Syntax_Util.Equal))
in (match (uu____22827) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____22831 -> begin
(

let uu____22832 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_66 -> FStar_Pervasives_Native.Some (_0_66)) uu____22832))
end))
in (

let uu____22835 = (solve_prob orig guard [] wl)
in (solve env uu____22835)))
end
| uu____22836 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____22837 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____22838, FStar_Syntax_Syntax.Tm_app (uu____22839)) -> begin
(

let head1 = (

let uu____22857 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22857 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22901 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22901 FStar_Pervasives_Native.fst))
in ((

let uu____22943 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____22943) with
| true -> begin
(

let uu____22944 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22945 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22946 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22944 uu____22945 uu____22946))))
end
| uu____22947 -> begin
()
end));
(

let uu____22948 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____22948) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____22963 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____22963) with
| true -> begin
(

let guard = (

let uu____22975 = (

let uu____22976 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____22976 FStar_Syntax_Util.Equal))
in (match (uu____22975) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____22979 -> begin
(

let uu____22980 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_67 -> FStar_Pervasives_Native.Some (_0_67)) uu____22980))
end))
in (

let uu____22983 = (solve_prob orig guard [] wl)
in (solve env uu____22983)))
end
| uu____22984 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____22985 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_let (uu____22986), FStar_Syntax_Syntax.Tm_let (uu____22987)) -> begin
(

let uu____23012 = (FStar_Syntax_Util.term_eq t1 t2)
in (match (uu____23012) with
| true -> begin
(

let uu____23013 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____23013))
end
| uu____23014 -> begin
(giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig)
end))
end
| (FStar_Syntax_Syntax.Tm_let (uu____23015), uu____23016) -> begin
(

let uu____23029 = (

let uu____23034 = (

let uu____23035 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____23036 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____23037 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____23038 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)" uu____23035 uu____23036 uu____23037 uu____23038)))))
in ((FStar_Errors.Fatal_UnificationNotWellFormed), (uu____23034)))
in (FStar_Errors.raise_error uu____23029 t1.FStar_Syntax_Syntax.pos))
end
| (uu____23039, FStar_Syntax_Syntax.Tm_let (uu____23040)) -> begin
(

let uu____23053 = (

let uu____23058 = (

let uu____23059 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____23060 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____23061 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____23062 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)" uu____23059 uu____23060 uu____23061 uu____23062)))))
in ((FStar_Errors.Fatal_UnificationNotWellFormed), (uu____23058)))
in (FStar_Errors.raise_error uu____23053 t1.FStar_Syntax_Syntax.pos))
end
| uu____23063 -> begin
(giveup env "head tag mismatch" orig)
end));
)
end))))
end));
)))))))))));
))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (

let c1 = problem.FStar_TypeChecker_Common.lhs
in (

let c2 = problem.FStar_TypeChecker_Common.rhs
in (

let orig = FStar_TypeChecker_Common.CProb (problem)
in (

let sub_prob = (fun t1 rel t2 reason -> (

let uu____23099 = (p_scope orig)
in (mk_problem uu____23099 orig t1 rel t2 FStar_Pervasives_Native.None reason)))
in (

let solve_eq = (fun c1_comp c2_comp -> ((

let uu____23112 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____23112) with
| true -> begin
(

let uu____23113 = (

let uu____23114 = (FStar_Syntax_Syntax.mk_Comp c1_comp)
in (FStar_Syntax_Print.comp_to_string uu____23114))
in (

let uu____23115 = (

let uu____23116 = (FStar_Syntax_Syntax.mk_Comp c2_comp)
in (FStar_Syntax_Print.comp_to_string uu____23116))
in (FStar_Util.print2 "solve_c is using an equality constraint (%s vs %s)\n" uu____23113 uu____23115)))
end
| uu____23117 -> begin
()
end));
(

let uu____23118 = (

let uu____23119 = (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)
in (not (uu____23119)))
in (match (uu____23118) with
| true -> begin
(

let uu____23120 = (

let uu____23121 = (FStar_Syntax_Print.lid_to_string c1_comp.FStar_Syntax_Syntax.effect_name)
in (

let uu____23122 = (FStar_Syntax_Print.lid_to_string c2_comp.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible effects: %s <> %s" uu____23121 uu____23122)))
in (giveup env uu____23120 orig))
end
| uu____23123 -> begin
(

let ret_sub_prob = (

let uu____23125 = (sub_prob c1_comp.FStar_Syntax_Syntax.result_typ FStar_TypeChecker_Common.EQ c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type")
in (FStar_All.pipe_left (fun _0_68 -> FStar_TypeChecker_Common.TProb (_0_68)) uu____23125))
in (

let arg_sub_probs = (FStar_List.map2 (fun uu____23152 uu____23153 -> (match (((uu____23152), (uu____23153))) with
| ((a1, uu____23171), (a2, uu____23173)) -> begin
(

let uu____23182 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _0_69 -> FStar_TypeChecker_Common.TProb (_0_69)) uu____23182))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let sub_probs = (ret_sub_prob)::arg_sub_probs
in (

let guard = (

let uu____23195 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) FStar_Pervasives_Native.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____23195))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))))))
end));
))
in (

let solve_sub = (fun c11 edge c21 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let lift_c1 = (fun uu____23227 -> (

let wp = (match (c11.FStar_Syntax_Syntax.effect_args) with
| ((wp1, uu____23234))::[] -> begin
wp1
end
| uu____23251 -> begin
(

let uu____23260 = (

let uu____23261 = (

let uu____23262 = (FStar_Ident.range_of_lid c11.FStar_Syntax_Syntax.effect_name)
in (FStar_Range.string_of_range uu____23262))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" uu____23261))
in (failwith uu____23260))
end)
in (

let univs1 = (match (c11.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
(

let uu____23270 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (uu____23270)::[])
end
| x -> begin
x
end)
in (

let uu____23272 = (

let uu____23281 = (

let uu____23282 = (

let uu____23283 = (FStar_List.hd univs1)
in (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp uu____23283 c11.FStar_Syntax_Syntax.result_typ wp))
in (FStar_Syntax_Syntax.as_arg uu____23282))
in (uu____23281)::[])
in {FStar_Syntax_Syntax.comp_univs = univs1; FStar_Syntax_Syntax.effect_name = c21.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c11.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____23272; FStar_Syntax_Syntax.flags = c11.FStar_Syntax_Syntax.flags}))))
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____23284 = (lift_c1 ())
in (solve_eq uu____23284 c21))
end
| uu____23285 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___120_23290 -> (match (uu___120_23290) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| uu____23291 -> begin
false
end))))
in (

let uu____23292 = (match (((c11.FStar_Syntax_Syntax.effect_args), (c21.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____23326))::uu____23327, ((wp2, uu____23329))::uu____23330) -> begin
((wp1), (wp2))
end
| uu____23387 -> begin
(

let uu____23408 = (

let uu____23413 = (

let uu____23414 = (FStar_Syntax_Print.lid_to_string c11.FStar_Syntax_Syntax.effect_name)
in (

let uu____23415 = (FStar_Syntax_Print.lid_to_string c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____23414 uu____23415)))
in ((FStar_Errors.Fatal_ExpectNormalizedEffect), (uu____23413)))
in (FStar_Errors.raise_error uu____23408 env.FStar_TypeChecker_Env.range))
end)
in (match (uu____23292) with
| (wpc1, wpc2) -> begin
(

let uu____23434 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____23434) with
| true -> begin
(

let uu____23437 = (problem_using_guard orig c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ FStar_Pervasives_Native.None "result type")
in (solve_t env uu____23437 wl))
end
| uu____23440 -> begin
(

let uu____23441 = (

let uu____23448 = (FStar_TypeChecker_Env.effect_decl_opt env c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.must uu____23448))
in (match (uu____23441) with
| (c2_decl, qualifiers) -> begin
(

let uu____23469 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____23469) with
| true -> begin
(

let c1_repr = (

let uu____23473 = (

let uu____23474 = (

let uu____23475 = (lift_c1 ())
in (FStar_Syntax_Syntax.mk_Comp uu____23475))
in (

let uu____23476 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____23474 uu____23476)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env uu____23473))
in (

let c2_repr = (

let uu____23478 = (

let uu____23479 = (FStar_Syntax_Syntax.mk_Comp c21)
in (

let uu____23480 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____23479 uu____23480)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env uu____23478))
in (

let prob = (

let uu____23482 = (

let uu____23487 = (

let uu____23488 = (FStar_Syntax_Print.term_to_string c1_repr)
in (

let uu____23489 = (FStar_Syntax_Print.term_to_string c2_repr)
in (FStar_Util.format2 "sub effect repr: %s <: %s" uu____23488 uu____23489)))
in (sub_prob c1_repr problem.FStar_TypeChecker_Common.relation c2_repr uu____23487))
in FStar_TypeChecker_Common.TProb (uu____23482))
in (

let wl1 = (

let uu____23491 = (

let uu____23494 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in FStar_Pervasives_Native.Some (uu____23494))
in (solve_prob orig uu____23491 [] wl))
in (solve env (attempt ((prob)::[]) wl1))))))
end
| uu____23499 -> begin
(

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____23501 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____23503 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____23503) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____23504 -> begin
()
end));
(

let c1_univ = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____23506 = (

let uu____23513 = (

let uu____23514 = (

let uu____23529 = (FStar_TypeChecker_Env.inst_effect_fun_with ((c1_univ)::[]) env c2_decl c2_decl.FStar_Syntax_Syntax.trivial)
in (

let uu____23530 = (

let uu____23533 = (FStar_Syntax_Syntax.as_arg c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____23534 = (

let uu____23537 = (

let uu____23538 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c1_univ c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____23538))
in (uu____23537)::[])
in (uu____23533)::uu____23534))
in ((uu____23529), (uu____23530))))
in FStar_Syntax_Syntax.Tm_app (uu____23514))
in (FStar_Syntax_Syntax.mk uu____23513))
in (uu____23506 FStar_Pervasives_Native.None r)));
)
end
| uu____23544 -> begin
(

let c1_univ = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (

let c2_univ = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____23547 = (

let uu____23554 = (

let uu____23555 = (

let uu____23570 = (FStar_TypeChecker_Env.inst_effect_fun_with ((c2_univ)::[]) env c2_decl c2_decl.FStar_Syntax_Syntax.stronger)
in (

let uu____23571 = (

let uu____23574 = (FStar_Syntax_Syntax.as_arg c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____23575 = (

let uu____23578 = (FStar_Syntax_Syntax.as_arg wpc2)
in (

let uu____23579 = (

let uu____23582 = (

let uu____23583 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c1_univ c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____23583))
in (uu____23582)::[])
in (uu____23578)::uu____23579))
in (uu____23574)::uu____23575))
in ((uu____23570), (uu____23571))))
in FStar_Syntax_Syntax.Tm_app (uu____23555))
in (FStar_Syntax_Syntax.mk uu____23554))
in (uu____23547 FStar_Pervasives_Native.None r))))
end)
end)
in (

let base_prob = (

let uu____23590 = (sub_prob c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _0_70 -> FStar_TypeChecker_Common.TProb (_0_70)) uu____23590))
in (

let wl1 = (

let uu____23600 = (

let uu____23603 = (

let uu____23606 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____23606 g))
in (FStar_All.pipe_left (fun _0_71 -> FStar_Pervasives_Native.Some (_0_71)) uu____23603))
in (solve_prob orig uu____23600 [] wl))
in (solve env (attempt ((base_prob)::[]) wl1)))))
end))
end))
end))
end)))
end))))
in (

let uu____23619 = (FStar_Util.physical_equality c1 c2)
in (match (uu____23619) with
| true -> begin
(

let uu____23620 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____23620))
end
| uu____23621 -> begin
((

let uu____23623 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____23623) with
| true -> begin
(

let uu____23624 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____23625 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____23624 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____23625)))
end
| uu____23626 -> begin
()
end));
(

let uu____23627 = (

let uu____23632 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____23633 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____23632), (uu____23633))))
in (match (uu____23627) with
| (c11, c21) -> begin
(match (((c11.FStar_Syntax_Syntax.n), (c21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____23637), FStar_Syntax_Syntax.Total (t2, uu____23639)) when (FStar_Syntax_Util.non_informative t2) -> begin
(

let uu____23656 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____23656 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____23659), FStar_Syntax_Syntax.Total (uu____23660)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| (FStar_Syntax_Syntax.Total (t1, uu____23678), FStar_Syntax_Syntax.Total (t2, uu____23680)) -> begin
(

let uu____23697 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____23697 wl))
end
| (FStar_Syntax_Syntax.GTotal (t1, uu____23701), FStar_Syntax_Syntax.GTotal (t2, uu____23703)) -> begin
(

let uu____23720 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____23720 wl))
end
| (FStar_Syntax_Syntax.Total (t1, uu____23724), FStar_Syntax_Syntax.GTotal (t2, uu____23726)) -> begin
(

let uu____23743 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____23743 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____23746), FStar_Syntax_Syntax.Comp (uu____23747)) -> begin
(

let uu____23756 = (

let uu___171_23761 = problem
in (

let uu____23766 = (

let uu____23767 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____23767))
in {FStar_TypeChecker_Common.pid = uu___171_23761.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____23766; FStar_TypeChecker_Common.relation = uu___171_23761.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___171_23761.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___171_23761.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___171_23761.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___171_23761.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___171_23761.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___171_23761.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___171_23761.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____23756 wl))
end
| (FStar_Syntax_Syntax.Total (uu____23768), FStar_Syntax_Syntax.Comp (uu____23769)) -> begin
(

let uu____23778 = (

let uu___171_23783 = problem
in (

let uu____23788 = (

let uu____23789 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____23789))
in {FStar_TypeChecker_Common.pid = uu___171_23783.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____23788; FStar_TypeChecker_Common.relation = uu___171_23783.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___171_23783.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___171_23783.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___171_23783.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___171_23783.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___171_23783.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___171_23783.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___171_23783.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____23778 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____23790), FStar_Syntax_Syntax.GTotal (uu____23791)) -> begin
(

let uu____23800 = (

let uu___172_23805 = problem
in (

let uu____23810 = (

let uu____23811 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____23811))
in {FStar_TypeChecker_Common.pid = uu___172_23805.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___172_23805.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___172_23805.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____23810; FStar_TypeChecker_Common.element = uu___172_23805.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___172_23805.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___172_23805.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___172_23805.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___172_23805.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___172_23805.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____23800 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____23812), FStar_Syntax_Syntax.Total (uu____23813)) -> begin
(

let uu____23822 = (

let uu___172_23827 = problem
in (

let uu____23832 = (

let uu____23833 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____23833))
in {FStar_TypeChecker_Common.pid = uu___172_23827.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___172_23827.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___172_23827.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____23832; FStar_TypeChecker_Common.element = uu___172_23827.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___172_23827.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___172_23827.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___172_23827.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___172_23827.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___172_23827.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____23822 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____23834), FStar_Syntax_Syntax.Comp (uu____23835)) -> begin
(

let uu____23836 = ((((FStar_Syntax_Util.is_ml_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) || ((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_total_comp c21))) || (((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB)))
in (match (uu____23836) with
| true -> begin
(

let uu____23837 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c11) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c21) FStar_Pervasives_Native.None "result type")
in (solve_t env uu____23837 wl))
end
| uu____23840 -> begin
(

let c1_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (

let c2_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____23843 = (

let uu____23848 = (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)
in (match (uu____23848) with
| true -> begin
((c1_comp), (c2_comp))
end
| uu____23853 -> begin
(

let uu____23854 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let uu____23855 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((uu____23854), (uu____23855))))
end))
in (match (uu____23843) with
| (c1_comp1, c2_comp1) -> begin
(solve_eq c1_comp1 c2_comp1)
end))
end
| uu____23858 -> begin
(

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((

let uu____23862 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____23862) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c12.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c22.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____23863 -> begin
()
end));
(

let uu____23864 = (FStar_TypeChecker_Env.monad_leq env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____23864) with
| FStar_Pervasives_Native.None -> begin
(

let uu____23867 = (

let uu____23868 = (FStar_Syntax_Print.lid_to_string c12.FStar_Syntax_Syntax.effect_name)
in (

let uu____23869 = (FStar_Syntax_Print.lid_to_string c22.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____23868 uu____23869)))
in (giveup env uu____23867 orig))
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

let uu____23876 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____23914 -> (match (uu____23914) with
| (uu____23927, uu____23928, u, uu____23930, uu____23931, uu____23932) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____23876 (FStar_String.concat ", "))))


let ineqs_to_string : (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.string = (fun ineqs -> (

let vars = (

let uu____23965 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs) (FStar_List.map FStar_Syntax_Print.univ_to_string))
in (FStar_All.pipe_right uu____23965 (FStar_String.concat ", ")))
in (

let ineqs1 = (

let uu____23983 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs) (FStar_List.map (fun uu____24011 -> (match (uu____24011) with
| (u1, u2) -> begin
(

let uu____24018 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____24019 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "%s < %s" uu____24018 uu____24019)))
end))))
in (FStar_All.pipe_right uu____23983 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred), (g.FStar_TypeChecker_Env.univ_ineqs))) with
| (FStar_TypeChecker_Common.Trivial, [], (uu____24040, [])) -> begin
"{}"
end
| uu____24065 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____24082 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____24082) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____24083 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____24085 = (FStar_List.map (fun uu____24095 -> (match (uu____24095) with
| (uu____24100, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right uu____24085 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (

let uu____24105 = (ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs)
in (FStar_Util.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n" form carry uu____24105 imps)))))
end))


let new_t_problem : 'Auu____24120 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  'Auu____24120 FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term, 'Auu____24120) FStar_TypeChecker_Common.problem = (fun env lhs rel rhs elt loc -> (

let reason = (

let uu____24160 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____24160) with
| true -> begin
(

let uu____24161 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____24162 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____24161 (rel_to_string rel) uu____24162)))
end
| uu____24163 -> begin
"TOP"
end))
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (

let uu____24194 = (

let uu____24197 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_72 -> FStar_Pervasives_Native.Some (_0_72)) uu____24197))
in (FStar_Syntax_Syntax.new_bv uu____24194 t1))
in (

let env1 = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (

let uu____24206 = (

let uu____24209 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _0_73 -> FStar_Pervasives_Native.Some (_0_73)) uu____24209))
in (

let uu____24212 = (FStar_TypeChecker_Env.get_range env1)
in (new_t_problem env1 t1 rel t2 uu____24206 uu____24212)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option = (fun env probs err -> (

let probs1 = (

let uu____24248 = (FStar_Options.eager_inference ())
in (match (uu____24248) with
| true -> begin
(

let uu___173_24249 = probs
in {attempting = uu___173_24249.attempting; wl_deferred = uu___173_24249.wl_deferred; ctr = uu___173_24249.ctr; defer_ok = false; smt_ok = uu___173_24249.smt_ok; tcenv = uu___173_24249.tcenv})
end
| uu____24250 -> begin
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

let uu____24260 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____24260) with
| true -> begin
(

let uu____24261 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____24261))
end
| uu____24262 -> begin
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

let uu____24279 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____24279) with
| true -> begin
(

let uu____24280 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____24280))
end
| uu____24281 -> begin
()
end));
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env f)
in ((

let uu____24284 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____24284) with
| true -> begin
(

let uu____24285 = (FStar_Syntax_Print.term_to_string f1)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____24285))
end
| uu____24286 -> begin
()
end));
(

let f2 = (

let uu____24288 = (

let uu____24289 = (FStar_Syntax_Util.unmeta f1)
in uu____24289.FStar_Syntax_Syntax.n)
in (match (uu____24288) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____24293 -> begin
FStar_TypeChecker_Common.NonTrivial (f1)
end))
in (

let uu___174_24294 = g
in {FStar_TypeChecker_Env.guard_f = f2; FStar_TypeChecker_Env.deferred = uu___174_24294.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___174_24294.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___174_24294.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____24319 = (

let uu____24320 = (

let uu____24321 = (

let uu____24322 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____24322 (fun _0_74 -> FStar_TypeChecker_Common.NonTrivial (_0_74))))
in {FStar_TypeChecker_Env.guard_f = uu____24321; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env uu____24320))
in (FStar_All.pipe_left (fun _0_75 -> FStar_Pervasives_Native.Some (_0_75)) uu____24319))
end))


let with_guard_no_simp : 'Auu____24353 . 'Auu____24353  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____24376 = (

let uu____24377 = (

let uu____24378 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____24378 (fun _0_76 -> FStar_TypeChecker_Common.NonTrivial (_0_76))))
in {FStar_TypeChecker_Env.guard_f = uu____24377; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in FStar_Pervasives_Native.Some (uu____24376))
end))


let try_teq : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun smt_ok env t1 t2 -> ((

let uu____24424 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____24424) with
| true -> begin
(

let uu____24425 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____24426 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" uu____24425 uu____24426)))
end
| uu____24427 -> begin
()
end));
(

let prob = (

let uu____24429 = (

let uu____24434 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None uu____24434))
in (FStar_All.pipe_left (fun _0_77 -> FStar_TypeChecker_Common.TProb (_0_77)) uu____24429))
in (

let g = (

let uu____24442 = (

let uu____24445 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____24445 (fun uu____24447 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____24442))
in g));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____24471 = (try_teq true env t1 t2)
in (match (uu____24471) with
| FStar_Pervasives_Native.None -> begin
((

let uu____24475 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____24476 = (FStar_TypeChecker_Err.basic_type_error env FStar_Pervasives_Native.None t2 t1)
in (FStar_Errors.log_issue uu____24475 uu____24476)));
trivial_guard;
)
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____24483 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____24483) with
| true -> begin
(

let uu____24484 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____24485 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____24486 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____24484 uu____24485 uu____24486))))
end
| uu____24487 -> begin
()
end));
g;
)
end)))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun env e t1 t2 -> (

let uu____24508 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____24509 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t2 t1)
in (FStar_Errors.log_issue uu____24508 uu____24509))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env c1 c2 -> (

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____24532 -> begin
FStar_TypeChecker_Common.SUB
end)
in ((

let uu____24534 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____24534) with
| true -> begin
(

let uu____24535 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____24536 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n" uu____24535 uu____24536 (match ((Prims.op_Equality rel FStar_TypeChecker_Common.EQ)) with
| true -> begin
"EQ"
end
| uu____24537 -> begin
"SUB"
end))))
end
| uu____24538 -> begin
()
end));
(

let prob = (

let uu____24540 = (

let uu____24545 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 FStar_Pervasives_Native.None uu____24545 "sub_comp"))
in (FStar_All.pipe_left (fun _0_78 -> FStar_TypeChecker_Common.CProb (_0_78)) uu____24540))
in (

let uu____24550 = (

let uu____24553 = (singleton env prob)
in (solve_and_commit env uu____24553 (fun uu____24555 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____24550)));
)))


let solve_universe_inequalities' : FStar_Syntax_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  unit = (fun tx env uu____24590 -> (match (uu____24590) with
| (variables, ineqs) -> begin
(

let fail1 = (fun u1 u2 -> ((FStar_Syntax_Unionfind.rollback tx);
(

let uu____24633 = (

let uu____24638 = (

let uu____24639 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____24640 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Universe %s and %s are incompatible" uu____24639 uu____24640)))
in ((FStar_Errors.Fatal_IncompatibleUniverse), (uu____24638)))
in (

let uu____24641 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____24633 uu____24641)));
))
in (

let equiv1 = (fun v1 v' -> (

let uu____24653 = (

let uu____24658 = (FStar_Syntax_Subst.compress_univ v1)
in (

let uu____24659 = (FStar_Syntax_Subst.compress_univ v')
in ((uu____24658), (uu____24659))))
in (match (uu____24653) with
| (FStar_Syntax_Syntax.U_unif (v0), FStar_Syntax_Syntax.U_unif (v0')) -> begin
(FStar_Syntax_Unionfind.univ_equiv v0 v0')
end
| uu____24678 -> begin
false
end)))
in (

let sols = (FStar_All.pipe_right variables (FStar_List.collect (fun v1 -> (

let uu____24708 = (FStar_Syntax_Subst.compress_univ v1)
in (match (uu____24708) with
| FStar_Syntax_Syntax.U_unif (uu____24715) -> begin
(

let lower_bounds_of_v = (FStar_All.pipe_right ineqs (FStar_List.collect (fun uu____24744 -> (match (uu____24744) with
| (u, v') -> begin
(

let uu____24753 = (equiv1 v1 v')
in (match (uu____24753) with
| true -> begin
(

let uu____24756 = (FStar_All.pipe_right variables (FStar_Util.for_some (equiv1 u)))
in (match (uu____24756) with
| true -> begin
[]
end
| uu____24761 -> begin
(u)::[]
end))
end
| uu____24762 -> begin
[]
end))
end))))
in (

let lb = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max (lower_bounds_of_v)))
in (((lb), (v1)))::[]))
end
| uu____24772 -> begin
[]
end)))))
in (

let uu____24777 = (

let wl = (

let uu___175_24781 = (empty_worklist env)
in {attempting = uu___175_24781.attempting; wl_deferred = uu___175_24781.wl_deferred; ctr = uu___175_24781.ctr; defer_ok = false; smt_ok = uu___175_24781.smt_ok; tcenv = uu___175_24781.tcenv})
in (FStar_All.pipe_right sols (FStar_List.map (fun uu____24799 -> (match (uu____24799) with
| (lb, v1) -> begin
(

let uu____24806 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl lb v1)
in (match (uu____24806) with
| USolved (wl1) -> begin
()
end
| uu____24808 -> begin
(fail1 lb v1)
end))
end)))))
in (

let rec check_ineq = (fun uu____24818 -> (match (uu____24818) with
| (u, v1) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u)
in (

let v2 = (FStar_TypeChecker_Normalize.normalize_universe env v1)
in (match (((u1), (v2))) with
| (FStar_Syntax_Syntax.U_zero, uu____24827) -> begin
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
| (FStar_Syntax_Syntax.U_name (uu____24850), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_unif (uu____24852), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_max (us), uu____24863) -> begin
(FStar_All.pipe_right us (FStar_Util.for_all (fun u2 -> (check_ineq ((u2), (v2))))))
end
| (uu____24870, FStar_Syntax_Syntax.U_max (vs)) -> begin
(FStar_All.pipe_right vs (FStar_Util.for_some (fun v3 -> (check_ineq ((u1), (v3))))))
end
| uu____24878 -> begin
false
end)))
end))
in (

let uu____24883 = (FStar_All.pipe_right ineqs (FStar_Util.for_all (fun uu____24898 -> (match (uu____24898) with
| (u, v1) -> begin
(

let uu____24905 = (check_ineq ((u), (v1)))
in (match (uu____24905) with
| true -> begin
true
end
| uu____24906 -> begin
((

let uu____24908 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____24908) with
| true -> begin
(

let uu____24909 = (FStar_Syntax_Print.univ_to_string u)
in (

let uu____24910 = (FStar_Syntax_Print.univ_to_string v1)
in (FStar_Util.print2 "%s </= %s" uu____24909 uu____24910)))
end
| uu____24911 -> begin
()
end));
false;
)
end))
end))))
in (match (uu____24883) with
| true -> begin
()
end
| uu____24912 -> begin
((

let uu____24914 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____24914) with
| true -> begin
((

let uu____24916 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Partially solved inequality constraints are: %s\n" uu____24916));
(FStar_Syntax_Unionfind.rollback tx);
(

let uu____24926 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Original solved inequality constraints are: %s\n" uu____24926));
)
end
| uu____24935 -> begin
()
end));
(

let uu____24936 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_FailToSolveUniverseInEquality), ("Failed to solve universe inequalities for inductives")) uu____24936));
)
end)))))))
end))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  unit = (fun env ineqs -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Syntax_Unionfind.commit tx);
)))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail1 = (fun uu____24994 -> (match (uu____24994) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ErrorInSolveDeferredConstraints), (msg)) (p_loc d)))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in ((

let uu____25008 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____25008) with
| true -> begin
(

let uu____25009 = (wl_to_string wl)
in (

let uu____25010 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" uu____25009 uu____25010)))
end
| uu____25023 -> begin
()
end));
(

let g1 = (

let uu____25025 = (solve_and_commit env wl fail1)
in (match (uu____25025) with
| FStar_Pervasives_Native.Some ([]) -> begin
(

let uu___176_25038 = g
in {FStar_TypeChecker_Env.guard_f = uu___176_25038.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu___176_25038.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___176_25038.FStar_TypeChecker_Env.implicits})
end
| uu____25043 -> begin
(failwith "impossible: Unexpected deferred constraints remain")
end))
in ((solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___177_25047 = g1
in {FStar_TypeChecker_Env.guard_f = uu___177_25047.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___177_25047.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = uu___177_25047.FStar_TypeChecker_Env.implicits});
));
))))


let last_proof_ns : FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let maybe_update_proof_ns : FStar_TypeChecker_Env.env  ->  unit = (fun env -> (

let pns = env.FStar_TypeChecker_Env.proof_ns
in (

let uu____25099 = (FStar_ST.op_Bang last_proof_ns)
in (match (uu____25099) with
| FStar_Pervasives_Native.None -> begin
(FStar_ST.op_Colon_Equals last_proof_ns (FStar_Pervasives_Native.Some (pns)))
end
| FStar_Pervasives_Native.Some (old) -> begin
(match ((Prims.op_Equality old pns)) with
| true -> begin
()
end
| uu____25169 -> begin
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

let uu___178_25240 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___178_25240.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___178_25240.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___178_25240.FStar_TypeChecker_Env.implicits})
in (

let uu____25241 = (

let uu____25242 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____25242)))
in (match (uu____25241) with
| true -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| uu____25245 -> begin
(match (g1.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((match (debug1) with
| true -> begin
(

let uu____25250 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____25251 = (

let uu____25252 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____25252))
in (FStar_Errors.diag uu____25250 uu____25251)))
end
| uu____25253 -> begin
()
end);
(

let vc1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env vc)
in ((match (debug1) with
| true -> begin
(

let uu____25256 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____25257 = (

let uu____25258 = (FStar_Syntax_Print.term_to_string vc1)
in (FStar_Util.format1 "After normalization VC=\n%s\n" uu____25258))
in (FStar_Errors.diag uu____25256 uu____25257)))
end
| uu____25259 -> begin
()
end);
(

let uu____25261 = (FStar_TypeChecker_Env.get_range env)
in (def_check_closed_in_env uu____25261 "discharge_guard\'" env vc1));
(

let uu____25262 = (check_trivial vc1)
in (match (uu____25262) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc2) -> begin
(match ((not (use_smt))) with
| true -> begin
((match (debug1) with
| true -> begin
(

let uu____25269 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____25270 = (

let uu____25271 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Cannot solve without SMT : %s\n" uu____25271))
in (FStar_Errors.diag uu____25269 uu____25270)))
end
| uu____25272 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end
| uu____25273 -> begin
((match (debug1) with
| true -> begin
(

let uu____25276 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____25277 = (

let uu____25278 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____25278))
in (FStar_Errors.diag uu____25276 uu____25277)))
end
| uu____25279 -> begin
()
end);
(

let vcs = (

let uu____25289 = (FStar_Options.use_tactics ())
in (match (uu____25289) with
| true -> begin
(FStar_Options.with_saved_options (fun uu____25309 -> ((

let uu____25311 = (FStar_Options.set_options FStar_Options.Set "--no_tactics")
in (FStar_All.pipe_left (fun a239 -> ()) uu____25311));
(

let vcs = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.preprocess env vc2)
in (FStar_All.pipe_right vcs (FStar_List.map (fun uu____25354 -> (match (uu____25354) with
| (env1, goal, opts) -> begin
(

let uu____25370 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env1 goal)
in ((env1), (uu____25370), (opts)))
end)))));
)))
end
| uu____25371 -> begin
(

let uu____25372 = (

let uu____25379 = (FStar_Options.peek ())
in ((env), (vc2), (uu____25379)))
in (uu____25372)::[])
end))
in (FStar_All.pipe_right vcs (FStar_List.iter (fun uu____25412 -> (match (uu____25412) with
| (env1, goal, opts) -> begin
(

let uu____25422 = (check_trivial goal)
in (match (uu____25422) with
| FStar_TypeChecker_Common.Trivial -> begin
(match (debug1) with
| true -> begin
(FStar_Util.print_string "Goal completely solved by tactic\n")
end
| uu____25424 -> begin
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

let uu____25430 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____25431 = (

let uu____25432 = (FStar_Syntax_Print.term_to_string goal1)
in (

let uu____25433 = (FStar_TypeChecker_Env.string_of_proof_ns env1)
in (FStar_Util.format2 "Trying to solve:\n> %s\nWith proof_ns:\n %s\n" uu____25432 uu____25433)))
in (FStar_Errors.diag uu____25430 uu____25431)))
end
| uu____25434 -> begin
()
end);
(match (debug1) with
| true -> begin
(

let uu____25436 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____25437 = (

let uu____25438 = (FStar_Syntax_Print.term_to_string goal1)
in (FStar_Util.format1 "Before calling solver VC=\n%s\n" uu____25438))
in (FStar_Errors.diag uu____25436 uu____25437)))
end
| uu____25439 -> begin
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

let uu____25452 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____25452) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____25459 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ExpectTrivialPreCondition), ("Expected a trivial pre-condition")) uu____25459))
end)))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let uu____25470 = (discharge_guard' FStar_Pervasives_Native.None env g true)
in (match (uu____25470) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end)))


let resolve_implicits' : Prims.bool  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun must_total forcelax g -> (

let unresolved = (fun u -> (

let uu____25498 = (FStar_Syntax_Unionfind.find u)
in (match (uu____25498) with
| FStar_Pervasives_Native.None -> begin
true
end
| uu____25501 -> begin
false
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____25523 = acc
in (match (uu____25523) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____25542 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd1)::tl1 -> begin
(

let uu____25609 = hd1
in (match (uu____25609) with
| (uu____25622, env, u, tm, k, r) -> begin
(

let uu____25628 = (unresolved u)
in (match (uu____25628) with
| true -> begin
(until_fixpoint (((hd1)::out), (changed)) tl1)
end
| uu____25655 -> begin
(

let tm1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (

let env1 = (match (forcelax) with
| true -> begin
(

let uu___179_25658 = env
in {FStar_TypeChecker_Env.solver = uu___179_25658.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___179_25658.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___179_25658.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___179_25658.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___179_25658.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___179_25658.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___179_25658.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___179_25658.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___179_25658.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___179_25658.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___179_25658.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___179_25658.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___179_25658.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___179_25658.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___179_25658.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___179_25658.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___179_25658.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___179_25658.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___179_25658.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___179_25658.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___179_25658.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___179_25658.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___179_25658.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___179_25658.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___179_25658.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___179_25658.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___179_25658.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___179_25658.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___179_25658.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___179_25658.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___179_25658.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___179_25658.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___179_25658.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___179_25658.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___179_25658.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___179_25658.FStar_TypeChecker_Env.dep_graph})
end
| uu____25659 -> begin
env
end)
in ((

let uu____25661 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("RelCheck")))
in (match (uu____25661) with
| true -> begin
(

let uu____25662 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____25663 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____25664 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" uu____25662 uu____25663 uu____25664))))
end
| uu____25665 -> begin
()
end));
(

let g1 = (FStar_All.try_with (fun uu___181_25668 -> (match (()) with
| () -> begin
(env1.FStar_TypeChecker_Env.check_type_of must_total env1 tm1 k)
end)) (fun uu___180_25672 -> (match (uu___180_25672) with
| e when (FStar_Errors.handleable e) -> begin
((

let uu____25675 = (

let uu____25684 = (

let uu____25691 = (

let uu____25692 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____25693 = (FStar_TypeChecker_Normalize.term_to_string env1 tm1)
in (FStar_Util.format2 "Failed while checking implicit %s set to %s" uu____25692 uu____25693)))
in ((FStar_Errors.Error_BadImplicit), (uu____25691), (r)))
in (uu____25684)::[])
in (FStar_Errors.add_errors uu____25675));
(FStar_Exn.raise e);
)
end)))
in (

let g2 = (match (env1.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___182_25707 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___182_25707.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___182_25707.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___182_25707.FStar_TypeChecker_Env.implicits})
end
| uu____25708 -> begin
g1
end)
in (

let g' = (

let uu____25710 = (discharge_guard' (FStar_Pervasives_Native.Some ((fun uu____25717 -> (FStar_Syntax_Print.term_to_string tm1)))) env1 g2 true)
in (match (uu____25710) with
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

let uu___183_25745 = g
in (

let uu____25746 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___183_25745.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___183_25745.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___183_25745.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____25746})))))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (resolve_implicits' true false g))


let resolve_implicits_tac : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (resolve_implicits' false true g))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  unit = (fun env g -> (

let g1 = (

let uu____25808 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____25808 resolve_implicits))
in (match (g1.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(

let uu____25821 = (discharge_guard env g1)
in (FStar_All.pipe_left (fun a240 -> ()) uu____25821))
end
| ((reason, uu____25823, uu____25824, e, t, r))::uu____25828 -> begin
(

let uu____25855 = (

let uu____25860 = (

let uu____25861 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____25862 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Failed to resolve implicit argument of type \'%s\' introduced in %s" uu____25861 uu____25862)))
in ((FStar_Errors.Fatal_FailToResolveImplicitArgument), (uu____25860)))
in (FStar_Errors.raise_error uu____25855 r))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___184_25873 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___184_25873.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___184_25873.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ((((u1), (u2)))::[])); FStar_TypeChecker_Env.implicits = uu___184_25873.FStar_TypeChecker_Env.implicits}))


let discharge_guard_nosmt : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun env g -> (

let uu____25900 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____25900) with
| FStar_Pervasives_Native.Some (uu____25906) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end)))


let teq_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____25922 = (try_teq false env t1 t2)
in (match (uu____25922) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g) -> begin
(discharge_guard_nosmt env g)
end)))


let check_subtyping : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.option = (fun env t1 t2 -> ((

let uu____25948 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____25948) with
| true -> begin
(

let uu____25949 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____25950 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "check_subtyping of %s and %s\n" uu____25949 uu____25950)))
end
| uu____25951 -> begin
()
end));
(

let uu____25952 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____25952) with
| (prob, x) -> begin
(

let g = (

let uu____25968 = (

let uu____25971 = (singleton' env prob true)
in (solve_and_commit env uu____25971 (fun uu____25973 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____25968))
in ((

let uu____25983 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____25983) with
| true -> begin
(

let uu____25984 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____25985 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____25986 = (

let uu____25987 = (FStar_Util.must g)
in (guard_to_string env uu____25987))
in (FStar_Util.print3 "check_subtyping succeeded: %s <: %s\n\tguard is %s\n" uu____25984 uu____25985 uu____25986))))
end
| uu____25988 -> begin
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

let uu____26021 = (check_subtyping env t1 t2)
in (match (uu____26021) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (x, g) -> begin
(

let uu____26040 = (

let uu____26041 = (FStar_Syntax_Syntax.mk_binder x)
in (abstract_guard uu____26041 g))
in FStar_Pervasives_Native.Some (uu____26040))
end)))


let get_subtyping_prop : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> (

let uu____26059 = (check_subtyping env t1 t2)
in (match (uu____26059) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (x, g) -> begin
(

let uu____26078 = (

let uu____26079 = (

let uu____26080 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____26080)::[])
in (close_guard env uu____26079 g))
in FStar_Pervasives_Native.Some (uu____26078))
end)))


let subtype_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> ((

let uu____26097 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____26097) with
| true -> begin
(

let uu____26098 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____26099 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____26098 uu____26099)))
end
| uu____26100 -> begin
()
end));
(

let uu____26101 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____26101) with
| (prob, x) -> begin
(

let g = (

let uu____26111 = (

let uu____26114 = (singleton' env prob false)
in (solve_and_commit env uu____26114 (fun uu____26116 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____26111))
in (match (g) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g1) -> begin
(

let g2 = (

let uu____26127 = (

let uu____26128 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____26128)::[])
in (close_guard env uu____26127 g1))
in (discharge_guard_nosmt env g2))
end))
end));
))





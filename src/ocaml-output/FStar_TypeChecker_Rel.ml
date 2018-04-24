
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
(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]
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
FStar_Syntax_Syntax.Delta_constant
end)
end
| FStar_Syntax_Syntax.Delta_defined_at_level (uu____5756) -> begin
(

let uu____5757 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5757) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Syntax.Delta_constant
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
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_type (uu____5966) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____5967) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____5980) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_abs (uu____5987) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
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
in (match (r) with
| MisMatch (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational), uu____6548) -> begin
(match ((not (retry))) with
| true -> begin
(fail1 r)
end
| uu____6565 -> begin
(

let uu____6566 = (

let uu____6575 = (maybe_inline t11)
in (

let uu____6578 = (maybe_inline t21)
in ((uu____6575), (uu____6578))))
in (match (uu____6566) with
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
| MisMatch (uu____6615, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational)) -> begin
(match ((not (retry))) with
| true -> begin
(fail1 r)
end
| uu____6632 -> begin
(

let uu____6633 = (

let uu____6642 = (maybe_inline t11)
in (

let uu____6645 = (maybe_inline t21)
in ((uu____6642), (uu____6645))))
in (match (uu____6633) with
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

let uu____6688 = (FStar_TypeChecker_Common.decr_delta_depth d1)
in (match (uu____6688) with
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

let uu____6711 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env wl t11)
in ((t1'), (t21)))
end
| uu____6721 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env wl t21)
in ((t11), (t2')))
end)
in (match (uu____6711) with
| (t12, t22) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
end)))
end
| MisMatch (uu____6735) -> begin
(fail1 r)
end
| uu____6744 -> begin
(success n_delta r t11 t21)
end)))
in (

let r = (aux true (Prims.parse_int "0") t1 t2)
in ((

let uu____6757 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelDelta")))
in (match (uu____6757) with
| true -> begin
(

let uu____6758 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6759 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____6760 = (string_of_match_result (FStar_Pervasives_Native.fst r))
in (FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6758 uu____6759 uu____6760))))
end
| uu____6767 -> begin
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
| uu____6806 -> begin
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
| uu____6850 -> begin
false
end))


let __proj__C__item___0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_0) -> begin
_0
end))


type tcs =
tc Prims.list


let tc_to_string : tc  ->  Prims.string = (fun uu___109_6864 -> (match (uu___109_6864) with
| T (t, uu____6866) -> begin
(term_to_string t)
end
| C (c) -> begin
(FStar_Syntax_Print.comp_to_string c)
end))


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____6890 = (FStar_Syntax_Util.type_u ())
in (match (uu____6890) with
| (t, uu____6896) -> begin
(

let uu____6897 = (new_uvar r binders t)
in (FStar_Pervasives_Native.fst uu____6897))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____6912 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____6912 FStar_Pervasives_Native.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * variance * tc) Prims.list) = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (

let uu____6986 = (head_matches env t1 t')
in (match (uu____6986) with
| MisMatch (uu____6987) -> begin
false
end
| uu____6996 -> begin
true
end)))
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let rebuild = (fun args' -> (

let args1 = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((uu____7096, imp), T (t2, uu____7099)) -> begin
((t2), (imp))
end
| uu____7122 -> begin
(failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd1), (args1)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun uu____7189 -> (match (uu____7189) with
| (t2, uu____7203) -> begin
((FStar_Pervasives_Native.None), (INVARIANT), (T (((t2), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____7250 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7250) with
| (bs1, c1) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs2 tcs1 -> (match (((bs2), (tcs1))) with
| (((x, imp))::bs3, (T (t2, uu____7335))::tcs2) -> begin
(aux (((((

let uu___134_7374 = x
in {FStar_Syntax_Syntax.ppname = uu___134_7374.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___134_7374.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (imp)))::out) bs3 tcs2)
end
| ([], (C (c2))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c2)
end
| uu____7392 -> begin
(failwith "Bad reconstruction")
end))
in (aux [] bs1 tcs)))
in (

let rec decompose1 = (fun out uu___110_7449 -> (match (uu___110_7449) with
| [] -> begin
(FStar_List.rev ((((FStar_Pervasives_Native.None), (COVARIANT), (C (c1))))::out))
end
| (hd1)::rest -> begin
(decompose1 ((((FStar_Pervasives_Native.Some (hd1)), (CONTRAVARIANT), (T ((((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (

let uu____7568 = (decompose1 [] bs1)
in ((rebuild), (matches), (uu____7568)))))
end))
end
| uu____7619 -> begin
(

let rebuild = (fun uu___111_7627 -> (match (uu___111_7627) with
| [] -> begin
t1
end
| uu____7630 -> begin
(failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t2 -> (FStar_Util.return_all true))), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun uu___112_7665 -> (match (uu___112_7665) with
| T (t, uu____7667) -> begin
t
end
| uu____7680 -> begin
(failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun uu___113_7685 -> (match (uu___113_7685) with
| T (t, uu____7687) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| uu____7700 -> begin
(failwith "Impossible")
end))


let imitation_sub_probs : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * variance * tc) Prims.list  ->  (FStar_TypeChecker_Common.prob Prims.list * tc Prims.list * FStar_Syntax_Syntax.formula) = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope1 args q -> (match (q) with
| (uu____7832, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope1 r)
in (

let uu____7861 = (new_uvar r scope1 k)
in (match (uu____7861) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| uu____7879 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) FStar_Pervasives_Native.None r)
end)
in (

let uu____7896 = (

let uu____7897 = (mk_problem scope1 orig gi_ps (vary_rel rel variance) ti FStar_Pervasives_Native.None "type subterm")
in (FStar_All.pipe_left (fun _0_23 -> FStar_TypeChecker_Common.TProb (_0_23)) uu____7897))
in ((T (((gi_xs), (mk_kind)))), (uu____7896))))
end)))
end
| (uu____7912, uu____7913, C (uu____7914)) -> begin
(failwith "impos")
end))
in (

let rec aux = (fun scope1 args qs1 -> (match (qs1) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs2 -> begin
(

let uu____8067 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.pos = uu____8084; FStar_Syntax_Syntax.vars = uu____8085})) -> begin
(

let uu____8108 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____8108) with
| (T (gi_xs, uu____8134), prob) -> begin
(

let uu____8148 = (

let uu____8149 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_24 -> C (_0_24)) uu____8149))
in ((uu____8148), ((prob)::[])))
end
| uu____8152 -> begin
(failwith "impossible")
end))
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.pos = uu____8167; FStar_Syntax_Syntax.vars = uu____8168})) -> begin
(

let uu____8191 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____8191) with
| (T (gi_xs, uu____8217), prob) -> begin
(

let uu____8231 = (

let uu____8232 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_25 -> C (_0_25)) uu____8232))
in ((uu____8231), ((prob)::[])))
end
| uu____8235 -> begin
(failwith "impossible")
end))
end
| (uu____8246, uu____8247, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.pos = uu____8249; FStar_Syntax_Syntax.vars = uu____8250})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((FStar_Pervasives_Native.None), (INVARIANT), (T ((((FStar_Pervasives_Native.fst t)), (generic_kind))))))))
in (

let components1 = (((FStar_Pervasives_Native.None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let uu____8385 = (

let uu____8394 = (FStar_List.map (sub_prob scope1 args) components1)
in (FStar_All.pipe_right uu____8394 FStar_List.unzip))
in (match (uu____8385) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (

let uu____8448 = (

let uu____8449 = (

let uu____8452 = (FStar_List.hd tcs)
in (FStar_All.pipe_right uu____8452 un_T))
in (

let uu____8453 = (

let uu____8462 = (FStar_List.tl tcs)
in (FStar_All.pipe_right uu____8462 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____8449; FStar_Syntax_Syntax.effect_args = uu____8453; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____8448))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| uu____8471 -> begin
(

let uu____8484 = (sub_prob scope1 args q)
in (match (uu____8484) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (uu____8067) with
| (tc, probs) -> begin
(

let uu____8515 = (match (((q), (tc))) with
| ((FStar_Pervasives_Native.Some (b, imp), uu____8578, uu____8579), T (t, uu____8581)) -> begin
(

let b1 = (((

let uu___135_8622 = b
in {FStar_Syntax_Syntax.ppname = uu___135_8622.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___135_8622.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let uu____8623 = (

let uu____8630 = (FStar_Syntax_Util.arg_of_non_null_binder b1)
in (uu____8630)::args)
in ((FStar_Pervasives_Native.Some (b1)), ((b1)::scope1), (uu____8623))))
end
| uu____8665 -> begin
((FStar_Pervasives_Native.None), (scope1), (args))
end)
in (match (uu____8515) with
| (bopt, scope2, args1) -> begin
(

let uu____8749 = (aux scope2 args1 qs2)
in (match (uu____8749) with
| (sub_probs, tcs, f) -> begin
(

let f1 = (match (bopt) with
| FStar_Pervasives_Native.None -> begin
(

let f1 = (

let uu____8787 = (

let uu____8790 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst))))
in (f)::uu____8790)
in (FStar_Syntax_Util.mk_conj_l uu____8787))
in ((def_check_closed (p_loc orig) "imitation_sub_probs (1)" f1);
f1;
))
end
| FStar_Pervasives_Native.Some (b) -> begin
(

let u_b = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (

let f1 = (

let uu____8815 = (

let uu____8818 = (FStar_Syntax_Util.mk_forall u_b (FStar_Pervasives_Native.fst b) f)
in (

let uu____8819 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst))))
in (uu____8818)::uu____8819))
in (FStar_Syntax_Util.mk_conj_l uu____8815))
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


let compress_tprob : 'Auu____8893 . worklist  ->  (FStar_Syntax_Syntax.term, 'Auu____8893) FStar_TypeChecker_Common.problem  ->  (FStar_Syntax_Syntax.term, 'Auu____8893) FStar_TypeChecker_Common.problem = (fun wl p -> (

let uu___136_8916 = p
in (

let uu____8921 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____8922 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___136_8916.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____8921; FStar_TypeChecker_Common.relation = uu___136_8916.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____8922; FStar_TypeChecker_Common.element = uu___136_8916.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___136_8916.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___136_8916.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___136_8916.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___136_8916.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___136_8916.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p1) -> begin
(

let uu____8938 = (compress_tprob wl p1)
in (FStar_All.pipe_right uu____8938 (fun _0_26 -> FStar_TypeChecker_Common.TProb (_0_26))))
end
| FStar_TypeChecker_Common.CProb (uu____8947) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (

let uu____8971 = (compress_prob wl pr)
in (FStar_All.pipe_right uu____8971 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____8981 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____8981) with
| (lh, uu____9001) -> begin
(

let uu____9022 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____9022) with
| (rh, uu____9042) -> begin
(

let uu____9063 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____9080), FStar_Syntax_Syntax.Tm_uvar (uu____9081)) -> begin
((flex_flex), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____9118), uu____9119) when ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (uu____9140, FStar_Syntax_Syntax.Tm_uvar (uu____9141)) when ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____9162), uu____9163) -> begin
(

let uu____9180 = (base_and_refinement wl.tcenv tp.FStar_TypeChecker_Common.rhs)
in (match (uu____9180) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
((flex_rigid), (tp))
end
| uu____9229 -> begin
(

let rank = (

let uu____9237 = (is_top_level_prob prob)
in (match (uu____9237) with
| true -> begin
flex_refine
end
| uu____9238 -> begin
flex_refine_inner
end))
in (

let uu____9239 = (

let uu___137_9244 = tp
in (

let uu____9249 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___137_9244.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___137_9244.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___137_9244.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____9249; FStar_TypeChecker_Common.element = uu___137_9244.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___137_9244.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___137_9244.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___137_9244.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___137_9244.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___137_9244.FStar_TypeChecker_Common.rank}))
in ((rank), (uu____9239))))
end)
end))
end
| (uu____9260, FStar_Syntax_Syntax.Tm_uvar (uu____9261)) -> begin
(

let uu____9278 = (base_and_refinement wl.tcenv tp.FStar_TypeChecker_Common.lhs)
in (match (uu____9278) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
((rigid_flex), (tp))
end
| uu____9327 -> begin
(

let uu____9334 = (

let uu___138_9341 = tp
in (

let uu____9346 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___138_9341.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____9346; FStar_TypeChecker_Common.relation = uu___138_9341.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___138_9341.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___138_9341.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___138_9341.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___138_9341.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___138_9341.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___138_9341.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___138_9341.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (uu____9334)))
end)
end))
end
| (uu____9363, uu____9364) -> begin
((rigid_rigid), (tp))
end)
in (match (uu____9063) with
| (rank, tp1) -> begin
(

let uu____9383 = (FStar_All.pipe_right (

let uu___139_9389 = tp1
in {FStar_TypeChecker_Common.pid = uu___139_9389.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___139_9389.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___139_9389.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___139_9389.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___139_9389.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___139_9389.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___139_9389.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___139_9389.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___139_9389.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rank)}) (fun _0_27 -> FStar_TypeChecker_Common.TProb (_0_27)))
in ((rank), (uu____9383)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____9399 = (FStar_All.pipe_right (

let uu___140_9405 = cp
in {FStar_TypeChecker_Common.pid = uu___140_9405.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___140_9405.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___140_9405.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___140_9405.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___140_9405.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___140_9405.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___140_9405.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___140_9405.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___140_9405.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rigid_rigid)}) (fun _0_28 -> FStar_TypeChecker_Common.CProb (_0_28)))
in ((rigid_rigid), (uu____9399)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun uu____9466 probs -> (match (uu____9466) with
| (min_rank, min1, out) -> begin
(match (probs) with
| [] -> begin
((min1), (out), (min_rank))
end
| (hd1)::tl1 -> begin
(

let uu____9519 = (rank wl hd1)
in (match (uu____9519) with
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
| uu____9565 -> begin
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
| uu____9595 -> begin
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
| uu____9635 -> begin
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
| uu____9649 -> begin
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
| uu____9663 -> begin
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

let uu____9715 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____9715) with
| (k, uu____9721) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Syntax_Unionfind.univ_equiv v1 v2)
end
| uu____9731 -> begin
false
end)
end)))))
end
| uu____9732 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (

let rec filter_out_common_univs = (fun u12 u22 -> (

let common_elts = (FStar_All.pipe_right u12 (FStar_List.fold_left (fun uvs uv1 -> (

let uu____9784 = (FStar_All.pipe_right u22 (FStar_List.existsML (fun uv2 -> (

let uu____9790 = (FStar_Syntax_Util.compare_univs uv1 uv2)
in (Prims.op_Equality uu____9790 (Prims.parse_int "0"))))))
in (match (uu____9784) with
| true -> begin
(uv1)::uvs
end
| uu____9793 -> begin
uvs
end))) []))
in (

let filter1 = (FStar_List.filter (fun u -> (

let uu____9806 = (FStar_All.pipe_right common_elts (FStar_List.existsML (fun u' -> (

let uu____9812 = (FStar_Syntax_Util.compare_univs u u')
in (Prims.op_Equality uu____9812 (Prims.parse_int "0"))))))
in (not (uu____9806)))))
in (

let uu____9813 = (filter1 u12)
in (

let uu____9816 = (filter1 u22)
in ((uu____9813), (uu____9816)))))))
in (

let try_umax_components = (fun u12 u22 msg -> (match (((u12), (u22))) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(

let uu____9845 = (filter_out_common_univs us1 us2)
in (match (uu____9845) with
| (us11, us21) -> begin
(match ((Prims.op_Equality (FStar_List.length us11) (FStar_List.length us21))) with
| true -> begin
(

let rec aux = (fun wl1 us12 us22 -> (match (((us12), (us22))) with
| ((u13)::us13, (u23)::us23) -> begin
(

let uu____9904 = (really_solve_universe_eq pid_orig wl1 u13 u23)
in (match (uu____9904) with
| USolved (wl2) -> begin
(aux wl2 us13 us23)
end
| failed -> begin
failed
end))
end
| uu____9907 -> begin
USolved (wl1)
end))
in (aux wl us11 us21))
end
| uu____9916 -> begin
(

let uu____9917 = (

let uu____9918 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____9919 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" uu____9918 uu____9919)))
in UFailed (uu____9917))
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

let uu____9943 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____9943) with
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

let uu____9969 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____9969) with
| USolved (wl2) -> begin
(aux wl2 us2)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____9972 -> begin
(

let uu____9977 = (

let uu____9978 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____9979 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" uu____9978 uu____9979 msg)))
in UFailed (uu____9977))
end))
in (match (((u11), (u21))) with
| (FStar_Syntax_Syntax.U_bvar (uu____9980), uu____9981) -> begin
(

let uu____9982 = (

let uu____9983 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____9984 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____9983 uu____9984)))
in (failwith uu____9982))
end
| (FStar_Syntax_Syntax.U_unknown, uu____9985) -> begin
(

let uu____9986 = (

let uu____9987 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____9988 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____9987 uu____9988)))
in (failwith uu____9986))
end
| (uu____9989, FStar_Syntax_Syntax.U_bvar (uu____9990)) -> begin
(

let uu____9991 = (

let uu____9992 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____9993 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____9992 uu____9993)))
in (failwith uu____9991))
end
| (uu____9994, FStar_Syntax_Syntax.U_unknown) -> begin
(

let uu____9995 = (

let uu____9996 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____9997 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____9996 uu____9997)))
in (failwith uu____9995))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____10000 -> begin
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

let uu____10021 = (FStar_Syntax_Unionfind.univ_equiv v1 v2)
in (match (uu____10021) with
| true -> begin
USolved (wl)
end
| uu____10022 -> begin
(

let wl1 = (extend_solution pid_orig ((UNIV (((v1), (u21))))::[]) wl)
in USolved (wl1))
end))
end
| (FStar_Syntax_Syntax.U_unif (v1), u) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____10043 = (occurs_univ v1 u3)
in (match (uu____10043) with
| true -> begin
(

let uu____10044 = (

let uu____10045 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____10046 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____10045 uu____10046)))
in (try_umax_components u11 u21 uu____10044))
end
| uu____10047 -> begin
(

let uu____10048 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____10048))
end)))
end
| (u, FStar_Syntax_Syntax.U_unif (v1)) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____10068 = (occurs_univ v1 u3)
in (match (uu____10068) with
| true -> begin
(

let uu____10069 = (

let uu____10070 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____10071 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____10070 uu____10071)))
in (try_umax_components u11 u21 uu____10069))
end
| uu____10072 -> begin
(

let uu____10073 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____10073))
end)))
end
| (FStar_Syntax_Syntax.U_max (uu____10082), uu____10083) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____10086 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____10089 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____10089) with
| true -> begin
USolved (wl)
end
| uu____10090 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (uu____10091, FStar_Syntax_Syntax.U_max (uu____10092)) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____10095 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____10098 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____10098) with
| true -> begin
USolved (wl)
end
| uu____10099 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (FStar_Syntax_Syntax.U_succ (uu____10100), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_succ (uu____10101), FStar_Syntax_Syntax.U_name (uu____10102)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ (uu____10103)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name (uu____10104)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____10105), FStar_Syntax_Syntax.U_succ (uu____10106)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____10107), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end)))))))


let solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (match (wl.tcenv.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
USolved (wl)
end
| uu____10128 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders : 'a 'b . ('a Prims.list * ('a Prims.list  ->  'b))  ->  ('a Prims.list * ('a Prims.list  ->  'b))  ->  (('a Prims.list * 'b) * ('a Prims.list * 'b)) = (fun bc1 bc2 -> (

let uu____10207 = bc1
in (match (uu____10207) with
| (bs1, mk_cod1) -> begin
(

let uu____10251 = bc2
in (match (uu____10251) with
| (bs2, mk_cod2) -> begin
(

let rec aux = (fun bs11 bs21 -> (match (((bs11), (bs21))) with
| ((x)::xs, (y)::ys) -> begin
(

let uu____10362 = (aux xs ys)
in (match (uu____10362) with
| ((xs1, xr), (ys1, yr)) -> begin
(((((x)::xs1), (xr))), ((((y)::ys1), (yr))))
end))
end
| (xs, ys) -> begin
(

let uu____10445 = (

let uu____10452 = (mk_cod1 xs)
in (([]), (uu____10452)))
in (

let uu____10455 = (

let uu____10462 = (mk_cod2 ys)
in (([]), (uu____10462)))
in ((uu____10445), (uu____10455))))
end))
in (aux bs1 bs2))
end))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____10647 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____10647) with
| true -> begin
(

let uu____10648 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" uu____10648))
end
| uu____10649 -> begin
()
end));
(

let uu____10650 = (next_prob probs)
in (match (uu____10650) with
| (FStar_Pervasives_Native.Some (hd1), tl1, rank1) -> begin
(

let probs1 = (

let uu___141_10671 = probs
in {attempting = tl1; wl_deferred = uu___141_10671.wl_deferred; ctr = uu___141_10671.ctr; defer_ok = uu___141_10671.defer_ok; smt_ok = uu___141_10671.smt_ok; tcenv = uu___141_10671.tcenv})
in (match (hd1) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs1)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match ((((not (probs1.defer_ok)) && (flex_refine_inner <= rank1)) && (rank1 <= flex_rigid))) with
| true -> begin
(

let uu____10682 = (solve_flex_rigid_join env tp probs1)
in (match (uu____10682) with
| FStar_Pervasives_Native.None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| FStar_Pervasives_Native.Some (wl) -> begin
(solve env wl)
end))
end
| uu____10686 -> begin
(match ((((not (probs1.defer_ok)) && (rigid_flex <= rank1)) && (rank1 <= refine_flex))) with
| true -> begin
(

let uu____10687 = (solve_rigid_flex_meet env tp probs1)
in (match (uu____10687) with
| FStar_Pervasives_Native.None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| FStar_Pervasives_Native.Some (wl) -> begin
(solve env wl)
end))
end
| uu____10691 -> begin
(solve_t' env (maybe_invert tp) probs1)
end)
end)
end))
end
| (FStar_Pervasives_Native.None, uu____10692, uu____10693) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| uu____10710 -> begin
(

let uu____10719 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____10778 -> (match (uu____10778) with
| (c, uu____10786, uu____10787) -> begin
(c < probs.ctr)
end))))
in (match (uu____10719) with
| (attempt1, rest) -> begin
(match (attempt1) with
| [] -> begin
(

let uu____10828 = (FStar_List.map (fun uu____10843 -> (match (uu____10843) with
| (uu____10854, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (uu____10828))
end
| uu____10857 -> begin
(

let uu____10866 = (

let uu___142_10867 = probs
in (

let uu____10868 = (FStar_All.pipe_right attempt1 (FStar_List.map (fun uu____10889 -> (match (uu____10889) with
| (uu____10896, uu____10897, y) -> begin
y
end))))
in {attempting = uu____10868; wl_deferred = rest; ctr = uu___142_10867.ctr; defer_ok = uu___142_10867.defer_ok; smt_ok = uu___142_10867.smt_ok; tcenv = uu___142_10867.tcenv}))
in (solve env uu____10866))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____10904 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____10904) with
| USolved (wl1) -> begin
(

let uu____10906 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____10906))
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

let uu____10958 = (solve_universe_eq (p_pid orig) wl1 u1 u2)
in (match (uu____10958) with
| USolved (wl2) -> begin
(aux wl2 us11 us21)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____10961 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t11 = (whnf env t1)
in (

let t21 = (whnf env t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.pos = uu____10973; FStar_Syntax_Syntax.vars = uu____10974}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.pos = uu____10977; FStar_Syntax_Syntax.vars = uu____10978}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____10990), uu____10991) -> begin
(failwith "Impossible: expect head symbols to match")
end
| (uu____10998, FStar_Syntax_Syntax.Tm_uinst (uu____10999)) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____11006 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____11016 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11016) with
| true -> begin
(

let uu____11017 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" uu____11017 msg))
end
| uu____11018 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____11019 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist FStar_Pervasives_Native.option = (fun env tp wl -> ((

let uu____11026 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11026) with
| true -> begin
(

let uu____11027 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" uu____11027))
end
| uu____11028 -> begin
()
end));
(

let uu____11029 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____11029) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let uu____11095 = (head_matches_delta env () t1 t2)
in (match (uu____11095) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (uu____11136) -> begin
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

let uu____11185 = (match (ts) with
| FStar_Pervasives_Native.Some (t11, t21) -> begin
(

let uu____11200 = (FStar_Syntax_Subst.compress t11)
in (

let uu____11201 = (FStar_Syntax_Subst.compress t21)
in ((uu____11200), (uu____11201))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____11206 = (FStar_Syntax_Subst.compress t1)
in (

let uu____11207 = (FStar_Syntax_Subst.compress t2)
in ((uu____11206), (uu____11207))))
end)
in (match (uu____11185) with
| (t11, t21) -> begin
(

let eq_prob = (fun t12 t22 -> (

let uu____11237 = (new_problem env t12 FStar_TypeChecker_Common.EQ t22 FStar_Pervasives_Native.None t12.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _0_29 -> FStar_TypeChecker_Common.TProb (_0_29)) uu____11237)))
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(

let uu____11268 = (

let uu____11277 = (

let uu____11280 = (

let uu____11287 = (

let uu____11288 = (

let uu____11295 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (uu____11295)))
in FStar_Syntax_Syntax.Tm_refine (uu____11288))
in (FStar_Syntax_Syntax.mk uu____11287))
in (uu____11280 FStar_Pervasives_Native.None t11.FStar_Syntax_Syntax.pos))
in (

let uu____11303 = (

let uu____11306 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (uu____11306)::[])
in ((uu____11277), (uu____11303))))
in FStar_Pervasives_Native.Some (uu____11268))
end
| (uu____11319, FStar_Syntax_Syntax.Tm_refine (x, uu____11321)) -> begin
(

let uu____11326 = (

let uu____11333 = (

let uu____11336 = (eq_prob x.FStar_Syntax_Syntax.sort t11)
in (uu____11336)::[])
in ((t11), (uu____11333)))
in FStar_Pervasives_Native.Some (uu____11326))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____11346), uu____11347) -> begin
(

let uu____11352 = (

let uu____11359 = (

let uu____11362 = (eq_prob x.FStar_Syntax_Syntax.sort t21)
in (uu____11362)::[])
in ((t21), (uu____11359)))
in FStar_Pervasives_Native.Some (uu____11352))
end
| uu____11371 -> begin
(

let uu____11376 = (FStar_Syntax_Util.head_and_args t11)
in (match (uu____11376) with
| (head1, uu____11400) -> begin
(

let uu____11421 = (

let uu____11422 = (FStar_Syntax_Util.un_uinst head1)
in uu____11422.FStar_Syntax_Syntax.n)
in (match (uu____11421) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____11433; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (i); FStar_Syntax_Syntax.fv_qual = uu____11435}) -> begin
(

let prev = (match ((i > (Prims.parse_int "1"))) with
| true -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i - (Prims.parse_int "1")))
end
| uu____11439 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
in (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t21)
in (disjoin t12 t22))))
end
| uu____11442 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____11455) -> begin
(

let uu____11480 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___114_11506 -> (match (uu___114_11506) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| FStar_Pervasives_Native.Some (rank1) when (is_rigid_flex rank1) -> begin
(

let uu____11513 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.rhs)
in (match (uu____11513) with
| (u', uu____11529) -> begin
(

let uu____11550 = (

let uu____11551 = (whnf env u')
in uu____11551.FStar_Syntax_Syntax.n)
in (match (uu____11550) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____11555) -> begin
(FStar_Syntax_Unionfind.equiv uv uv')
end
| uu____11580 -> begin
false
end))
end))
end
| uu____11581 -> begin
false
end)
end
| uu____11584 -> begin
false
end))))
in (match (uu____11480) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun uu____11622 tps -> (match (uu____11622) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
FStar_Pervasives_Native.Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____11670 = (

let uu____11679 = (whnf env hd1.FStar_TypeChecker_Common.lhs)
in (disjoin bound uu____11679))
in (match (uu____11670) with
| FStar_Pervasives_Native.Some (bound1, sub1) -> begin
(make_lower_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____11714 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let uu____11723 = (

let uu____11732 = (

let uu____11739 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((uu____11739), ([])))
in (make_lower_bound uu____11732 lower_bounds))
in (match (uu____11723) with
| FStar_Pervasives_Native.None -> begin
((

let uu____11751 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11751) with
| true -> begin
(FStar_Util.print_string "No lower bounds\n")
end
| uu____11752 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (lhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in ((

let uu____11771 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11771) with
| true -> begin
(

let wl' = (

let uu___143_11773 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___143_11773.wl_deferred; ctr = uu___143_11773.ctr; defer_ok = uu___143_11773.defer_ok; smt_ok = uu___143_11773.smt_ok; tcenv = uu___143_11773.tcenv})
in (

let uu____11774 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" uu____11774)))
end
| uu____11775 -> begin
()
end));
(

let uu____11776 = (solve_t env eq_prob (

let uu___144_11778 = wl
in {attempting = sub_probs; wl_deferred = uu___144_11778.wl_deferred; ctr = uu___144_11778.ctr; defer_ok = uu___144_11778.defer_ok; smt_ok = uu___144_11778.smt_ok; tcenv = uu___144_11778.tcenv}))
in (match (uu____11776) with
| Success (uu____11781) -> begin
(

let wl1 = (

let uu___145_11783 = wl
in {attempting = rest; wl_deferred = uu___145_11783.wl_deferred; ctr = uu___145_11783.ctr; defer_ok = uu___145_11783.defer_ok; smt_ok = uu___145_11783.smt_ok; tcenv = uu___145_11783.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) FStar_Pervasives_Native.None [] wl1)
in (

let uu____11785 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p FStar_Pervasives_Native.None [] wl3)) wl2 lower_bounds)
in FStar_Pervasives_Native.Some (wl2))))
end
| uu____11790 -> begin
FStar_Pervasives_Native.None
end));
))
end)))
end))
end
| uu____11791 -> begin
(failwith "Impossible: Not a rigid-flex")
end)))
end));
))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist FStar_Pervasives_Native.option = (fun env tp wl -> ((

let uu____11800 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11800) with
| true -> begin
(

let uu____11801 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" uu____11801))
end
| uu____11802 -> begin
()
end));
(

let uu____11803 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____11803) with
| (u, args) -> begin
(

let uu____11842 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (uu____11842) with
| (ok, head_match1, partial_match, fallback, failed_match) -> begin
(

let max1 = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____11871 -> begin
i
end))
in (

let base_types_match = (fun t1 t2 -> (

let uu____11891 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____11891) with
| (h1, args1) -> begin
(

let uu____11932 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____11932) with
| (h2, uu____11952) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
(

let uu____11979 = (FStar_Syntax_Syntax.fv_eq tc1 tc2)
in (match (uu____11979) with
| true -> begin
(match ((Prims.op_Equality (FStar_List.length args1) (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____11996 -> begin
(

let uu____11997 = (

let uu____12000 = (

let uu____12001 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_30 -> FStar_TypeChecker_Common.TProb (_0_30)) uu____12001))
in (uu____12000)::[])
in FStar_Pervasives_Native.Some (uu____11997))
end)
end
| uu____12012 -> begin
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
| uu____12033 -> begin
(

let uu____12034 = (

let uu____12037 = (

let uu____12038 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_31 -> FStar_TypeChecker_Common.TProb (_0_31)) uu____12038))
in (uu____12037)::[])
in FStar_Pervasives_Native.Some (uu____12034))
end)
end
| uu____12049 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____12052 -> begin
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

let uu____12146 = (

let uu____12155 = (

let uu____12158 = (FStar_Syntax_Util.mk_conj phi11 phi21)
in (FStar_Syntax_Util.refine x1 uu____12158))
in ((uu____12155), (m1)))
in FStar_Pervasives_Native.Some (uu____12146))))))
end))
end
| (uu____12171, FStar_Syntax_Syntax.Tm_refine (y, uu____12173)) -> begin
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
| (FStar_Syntax_Syntax.Tm_refine (x, uu____12221), uu____12222) -> begin
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
| uu____12269 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____12322) -> begin
(

let uu____12347 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___115_12373 -> (match (uu___115_12373) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| FStar_Pervasives_Native.Some (rank1) when (is_flex_rigid rank1) -> begin
(

let uu____12380 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.lhs)
in (match (uu____12380) with
| (u', uu____12396) -> begin
(

let uu____12417 = (

let uu____12418 = (whnf env u')
in uu____12418.FStar_Syntax_Syntax.n)
in (match (uu____12417) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____12422) -> begin
(FStar_Syntax_Unionfind.equiv uv uv')
end
| uu____12447 -> begin
false
end))
end))
end
| uu____12448 -> begin
false
end)
end
| uu____12451 -> begin
false
end))))
in (match (uu____12347) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun uu____12493 tps -> (match (uu____12493) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
FStar_Pervasives_Native.Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____12555 = (

let uu____12566 = (whnf env hd1.FStar_TypeChecker_Common.rhs)
in (conjoin bound uu____12566))
in (match (uu____12555) with
| FStar_Pervasives_Native.Some (bound1, sub1) -> begin
(make_upper_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____12617 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let uu____12628 = (

let uu____12639 = (

let uu____12648 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((uu____12648), ([])))
in (make_upper_bound uu____12639 upper_bounds))
in (match (uu____12628) with
| FStar_Pervasives_Native.None -> begin
((

let uu____12662 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____12662) with
| true -> begin
(FStar_Util.print_string "No upper bounds\n")
end
| uu____12663 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "joining refinements")
in ((

let uu____12688 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____12688) with
| true -> begin
(

let wl' = (

let uu___146_12690 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___146_12690.wl_deferred; ctr = uu___146_12690.ctr; defer_ok = uu___146_12690.defer_ok; smt_ok = uu___146_12690.smt_ok; tcenv = uu___146_12690.tcenv})
in (

let uu____12691 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" uu____12691)))
end
| uu____12692 -> begin
()
end));
(

let uu____12693 = (solve_t env eq_prob (

let uu___147_12695 = wl
in {attempting = sub_probs; wl_deferred = uu___147_12695.wl_deferred; ctr = uu___147_12695.ctr; defer_ok = uu___147_12695.defer_ok; smt_ok = uu___147_12695.smt_ok; tcenv = uu___147_12695.tcenv}))
in (match (uu____12693) with
| Success (uu____12698) -> begin
(

let wl1 = (

let uu___148_12700 = wl
in {attempting = rest; wl_deferred = uu___148_12700.wl_deferred; ctr = uu___148_12700.ctr; defer_ok = uu___148_12700.defer_ok; smt_ok = uu___148_12700.smt_ok; tcenv = uu___148_12700.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) FStar_Pervasives_Native.None [] wl1)
in (

let uu____12702 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p FStar_Pervasives_Native.None [] wl3)) wl2 upper_bounds)
in FStar_Pervasives_Native.Some (wl2))))
end
| uu____12707 -> begin
FStar_Pervasives_Native.None
end));
))
end)))
end))
end
| uu____12708 -> begin
(failwith "Impossible: Not a flex-rigid")
end)))))
end))
end));
))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> ((

let uu____12726 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12726) with
| true -> begin
(

let uu____12727 = (FStar_Syntax_Print.binders_to_string ", " bs1)
in (

let uu____12728 = (FStar_Syntax_Print.binders_to_string ", " bs2)
in (FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n" uu____12727 (rel_to_string (p_rel orig)) uu____12728)))
end
| uu____12729 -> begin
()
end));
(

let rec aux = (fun scope env1 subst1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
(

let rhs_prob = (rhs scope env1 subst1)
in ((

let uu____12798 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____12798) with
| true -> begin
(

let uu____12799 = (prob_to_string env1 rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" uu____12799))
end
| uu____12800 -> begin
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

let uu___149_12853 = hd1
in (

let uu____12854 = (FStar_Syntax_Subst.subst subst1 hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___149_12853.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___149_12853.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____12854}))
in (

let hd21 = (

let uu___150_12858 = hd2
in (

let uu____12859 = (FStar_Syntax_Subst.subst subst1 hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___150_12858.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___150_12858.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____12859}))
in (

let prob = (

let uu____12863 = (

let uu____12868 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd11.FStar_Syntax_Syntax.sort uu____12868 hd21.FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None "Formal parameter"))
in (FStar_All.pipe_left (fun _0_32 -> FStar_TypeChecker_Common.TProb (_0_32)) uu____12863))
in (

let hd12 = (FStar_Syntax_Syntax.freshen_bv hd11)
in (

let subst2 = (

let uu____12879 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd12))))::uu____12879)
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 hd12)
in (

let uu____12883 = (aux (FStar_List.append scope ((((hd12), (imp)))::[])) env2 subst2 xs1 ys1)
in (match (uu____12883) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi1 = (

let uu____12921 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (

let uu____12926 = (close_forall env2 ((((hd12), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj uu____12921 uu____12926)))
in ((

let uu____12936 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____12936) with
| true -> begin
(

let uu____12937 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____12938 = (FStar_Syntax_Print.bv_to_string hd12)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" uu____12937 uu____12938)))
end
| uu____12939 -> begin
()
end));
FStar_Util.Inl ((((prob)::sub_probs), (phi1)));
))
end
| fail1 -> begin
fail1
end))))))))
end
| uu____12961 -> begin
FStar_Util.Inr ("arity or argument-qualifier mismatch")
end))
in (

let scope = (p_scope orig)
in (

let uu____12971 = (aux scope env [] bs1 bs2)
in (match (uu____12971) with
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

let uu____12996 = (compress_tprob wl problem)
in (solve_t' env uu____12996 wl));
))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> ((def_check_prob "solve_t\'.1" (FStar_TypeChecker_Common.TProb (problem)));
(

let giveup_or_defer1 = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env1 orig wl1 head1 head2 t1 t2 -> (

let uu____13048 = (head_matches_delta env1 wl1 t1 t2)
in (match (uu____13048) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____13079), uu____13080) -> begin
(

let rec may_relate = (fun head3 -> (

let uu____13107 = (

let uu____13108 = (FStar_Syntax_Subst.compress head3)
in uu____13108.FStar_Syntax_Syntax.n)
in (match (uu____13107) with
| FStar_Syntax_Syntax.Tm_name (uu____13111) -> begin
true
end
| FStar_Syntax_Syntax.Tm_match (uu____13112) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____13135; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational; FStar_Syntax_Syntax.fv_qual = uu____13136}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____13139; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (uu____13140); FStar_Syntax_Syntax.fv_qual = uu____13141}) -> begin
(Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____13145, uu____13146) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____13188) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____13194) -> begin
(may_relate t)
end
| uu____13199 -> begin
false
end)))
in (

let uu____13200 = (((may_relate head1) || (may_relate head2)) && wl1.smt_ok)
in (match (uu____13200) with
| true -> begin
(

let guard = (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_eq2 orig t1 t2)
end
| uu____13202 -> begin
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

let uu____13221 = (

let uu____13222 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t11 uu____13222 t21))
in (FStar_Syntax_Util.mk_forall u_x x uu____13221))))
end))
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB)) with
| true -> begin
(has_type_guard t1 t2)
end
| uu____13223 -> begin
(has_type_guard t2 t1)
end))
end)
in (

let uu____13224 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl1)
in (solve env1 uu____13224)))
end
| uu____13225 -> begin
(

let uu____13226 = (

let uu____13227 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____13228 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.format2 "head mismatch (%s vs %s)" uu____13227 uu____13228)))
in (giveup env1 uu____13226 orig))
end)))
end
| (uu____13229, FStar_Pervasives_Native.Some (t11, t21)) -> begin
(solve_t env1 (

let uu___151_13243 = problem
in {FStar_TypeChecker_Common.pid = uu___151_13243.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___151_13243.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___151_13243.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___151_13243.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___151_13243.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___151_13243.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___151_13243.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___151_13243.FStar_TypeChecker_Common.rank}) wl1)
end
| (uu____13244, FStar_Pervasives_Native.None) -> begin
((

let uu____13256 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____13256) with
| true -> begin
(

let uu____13257 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____13258 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____13259 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____13260 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" uu____13257 uu____13258 uu____13259 uu____13260)))))
end
| uu____13261 -> begin
()
end));
(

let uu____13262 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____13262) with
| (head11, args1) -> begin
(

let uu____13299 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____13299) with
| (head21, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((Prims.op_disEquality nargs (FStar_List.length args2))) with
| true -> begin
(

let uu____13353 = (

let uu____13354 = (FStar_Syntax_Print.term_to_string head11)
in (

let uu____13355 = (args_to_string args1)
in (

let uu____13356 = (FStar_Syntax_Print.term_to_string head21)
in (

let uu____13357 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____13354 uu____13355 uu____13356 uu____13357)))))
in (giveup env1 uu____13353 orig))
end
| uu____13358 -> begin
(

let uu____13359 = ((Prims.op_Equality nargs (Prims.parse_int "0")) || (

let uu____13365 = (FStar_Syntax_Util.eq_args args1 args2)
in (Prims.op_Equality uu____13365 FStar_Syntax_Util.Equal)))
in (match (uu____13359) with
| true -> begin
(

let uu____13366 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____13366) with
| USolved (wl2) -> begin
(

let uu____13368 = (solve_prob orig FStar_Pervasives_Native.None [] wl2)
in (solve env1 uu____13368))
end
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end))
end
| uu____13371 -> begin
(

let uu____13372 = (base_and_refinement env1 t1)
in (match (uu____13372) with
| (base1, refinement1) -> begin
(

let uu____13397 = (base_and_refinement env1 t2)
in (match (uu____13397) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(

let uu____13454 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____13454) with
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end
| USolved (wl2) -> begin
(

let subprobs = (FStar_List.map2 (fun uu____13476 uu____13477 -> (match (((uu____13476), (uu____13477))) with
| ((a, uu____13495), (a', uu____13497)) -> begin
(

let uu____13506 = (

let uu____13511 = (p_scope orig)
in (mk_problem uu____13511 orig a FStar_TypeChecker_Common.EQ a' FStar_Pervasives_Native.None "index"))
in (FStar_All.pipe_left (fun _0_33 -> FStar_TypeChecker_Common.TProb (_0_33)) uu____13506))
end)) args1 args2)
in (

let formula = (

let uu____13517 = (FStar_List.map (fun p -> (FStar_Pervasives_Native.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____13517))
in (

let wl3 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) [] wl2)
in (solve env1 (attempt subprobs wl3)))))
end))
end
| uu____13523 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env1 (

let uu___152_13559 = problem
in {FStar_TypeChecker_Common.pid = uu___152_13559.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___152_13559.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___152_13559.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___152_13559.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___152_13559.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___152_13559.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___152_13559.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___152_13559.FStar_TypeChecker_Common.rank}) wl1)))
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

let force_quasi_pattern = (fun xs_opt uu____13596 -> (match (uu____13596) with
| (t, u, k, args) -> begin
(

let debug1 = (fun f -> (

let uu____13640 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____13640) with
| true -> begin
(f ())
end
| uu____13641 -> begin
()
end)))
in (

let rec aux = (fun pat_args pat_args_set pattern_vars pattern_var_set seen_formals formals res_t args1 -> ((debug1 (fun uu____13752 -> (

let uu____13753 = (FStar_Syntax_Print.binders_to_string ", " pat_args)
in (FStar_Util.print1 "pat_args so far: {%s}\n" uu____13753))));
(match (((formals), (args1))) with
| ([], []) -> begin
(

let pat_args1 = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun uu____13821 -> (match (uu____13821) with
| (x, imp) -> begin
(

let uu____13832 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____13832), (imp)))
end))))
in (

let pattern_vars1 = (FStar_List.rev pattern_vars)
in (

let kk = (

let uu____13845 = (FStar_Syntax_Util.type_u ())
in (match (uu____13845) with
| (t1, uu____13851) -> begin
(

let uu____13852 = (new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1 t1)
in (FStar_Pervasives_Native.fst uu____13852))
end))
in (

let uu____13857 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk)
in (match (uu____13857) with
| (t', tm_u1) -> begin
(

let uu____13870 = (destruct_flex_t t')
in (match (uu____13870) with
| (uu____13907, u1, k1, uu____13910) -> begin
(

let all_formals = (FStar_List.rev seen_formals)
in (

let k2 = (

let uu____13969 = (FStar_Syntax_Syntax.mk_Total res_t)
in (FStar_Syntax_Util.arrow all_formals uu____13969))
in (

let sol = (

let uu____13973 = (

let uu____13982 = (u_abs k2 all_formals t')
in ((((u), (k2))), (uu____13982)))
in TERM (uu____13973))
in (

let t_app = (FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (((sol), (((t_app), (u1), (k1), (pat_args1)))))))))
end))
end)))))
end
| ((formal)::formals1, (hd1)::tl1) -> begin
((debug1 (fun uu____14117 -> (

let uu____14118 = (FStar_Syntax_Print.binder_to_string formal)
in (

let uu____14119 = (FStar_Syntax_Print.args_to_string ((hd1)::[]))
in (FStar_Util.print2 "force_quasi_pattern (case 2): formal=%s, hd=%s\n" uu____14118 uu____14119)))));
(

let uu____14132 = (pat_var_opt env pat_args hd1)
in (match (uu____14132) with
| FStar_Pervasives_Native.None -> begin
((debug1 (fun uu____14152 -> (FStar_Util.print_string "not a pattern var\n")));
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun uu____14195 -> (match (uu____14195) with
| (x, uu____14201) -> begin
(FStar_Syntax_Syntax.bv_eq x (FStar_Pervasives_Native.fst y))
end))))
end)
in (match ((not (maybe_pat))) with
| true -> begin
(aux pat_args pat_args_set pattern_vars pattern_var_set ((formal)::seen_formals) formals1 res_t tl1)
end
| uu____14208 -> begin
((debug1 (fun uu____14216 -> (

let uu____14217 = (FStar_Syntax_Print.args_to_string ((hd1)::[]))
in (

let uu____14230 = (FStar_Syntax_Print.binder_to_string y)
in (FStar_Util.print2 "%s (var = %s) maybe pat\n" uu____14217 uu____14230)))));
(

let fvs = (FStar_Syntax_Free.names (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____14234 = (

let uu____14235 = (FStar_Util.set_is_subset_of fvs pat_args_set)
in (not (uu____14235)))
in (match (uu____14234) with
| true -> begin
((debug1 (fun uu____14247 -> (

let uu____14248 = (

let uu____14251 = (FStar_Syntax_Print.args_to_string ((hd1)::[]))
in (

let uu____14264 = (

let uu____14267 = (FStar_Syntax_Print.binder_to_string y)
in (

let uu____14268 = (

let uu____14271 = (FStar_Syntax_Print.term_to_string (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____14272 = (

let uu____14275 = (names_to_string fvs)
in (

let uu____14276 = (

let uu____14279 = (names_to_string pattern_var_set)
in (uu____14279)::[])
in (uu____14275)::uu____14276))
in (uu____14271)::uu____14272))
in (uu____14267)::uu____14268))
in (uu____14251)::uu____14264))
in (FStar_Util.print "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n" uu____14248))));
(aux pat_args pat_args_set pattern_vars pattern_var_set ((formal)::seen_formals) formals1 res_t tl1);
)
end
| uu____14280 -> begin
(

let uu____14281 = (FStar_Util.set_add (FStar_Pervasives_Native.fst y) pat_args_set)
in (

let uu____14284 = (FStar_Util.set_add (FStar_Pervasives_Native.fst formal) pattern_var_set)
in (aux ((y)::pat_args) uu____14281 ((formal)::pattern_vars) uu____14284 ((formal)::seen_formals) formals1 res_t tl1)))
end)));
)
end))
end));
)
end
| ([], (uu____14291)::uu____14292) -> begin
(

let uu____14323 = (

let uu____14336 = (FStar_TypeChecker_Normalize.unfold_whnf env res_t)
in (FStar_Syntax_Util.arrow_formals uu____14336))
in (match (uu____14323) with
| (more_formals, res_t1) -> begin
(match (more_formals) with
| [] -> begin
FStar_Pervasives_Native.None
end
| uu____14375 -> begin
(aux pat_args pat_args_set pattern_vars pattern_var_set seen_formals more_formals res_t1 args1)
end)
end))
end
| ((uu____14382)::uu____14383, []) -> begin
FStar_Pervasives_Native.None
end);
))
in (

let uu____14406 = (

let uu____14419 = (FStar_TypeChecker_Normalize.unfold_whnf env k)
in (FStar_Syntax_Util.arrow_formals uu____14419))
in (match (uu____14406) with
| (all_formals, res_t) -> begin
((debug1 (fun uu____14455 -> (

let uu____14456 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____14457 = (FStar_Syntax_Print.binders_to_string ", " all_formals)
in (

let uu____14458 = (FStar_Syntax_Print.term_to_string res_t)
in (

let uu____14459 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print4 "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n" uu____14456 uu____14457 uu____14458 uu____14459)))))));
(

let uu____14460 = (FStar_Syntax_Syntax.new_bv_set ())
in (

let uu____14463 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] uu____14460 [] uu____14463 [] all_formals res_t args)));
)
end))))
end))
in (

let use_pattern_equality = (fun orig env1 wl1 lhs pat_vars1 rhs -> (

let uu____14509 = lhs
in (match (uu____14509) with
| (t1, uv, k_uv, args_lhs) -> begin
(

let sol = (match (pat_vars1) with
| [] -> begin
rhs
end
| uu____14519 -> begin
(

let uu____14520 = (sn_binders env1 pat_vars1)
in (u_abs k_uv uu____14520 rhs))
end)
in (

let wl2 = (solve_prob orig FStar_Pervasives_Native.None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl1)
in (solve env1 wl2)))
end)))
in (

let imitate = (fun orig env1 wl1 p -> (

let uu____14551 = p
in (match (uu____14551) with
| (((u, k), xs, c), ps, (h, uu____14562, qs)) -> begin
(

let xs1 = (sn_binders env1 xs)
in (

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____14650 = (imitation_sub_probs orig env1 xs1 ps qs)
in (match (uu____14650) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (

let uu____14673 = (h gs_xs)
in (

let uu____14674 = (FStar_All.pipe_right (FStar_Syntax_Util.residual_comp_of_comp c) (fun _0_34 -> FStar_Pervasives_Native.Some (_0_34)))
in (FStar_Syntax_Util.abs xs1 uu____14673 uu____14674)))
in ((

let uu____14680 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____14680) with
| true -> begin
(

let uu____14681 = (

let uu____14684 = (

let uu____14685 = (FStar_List.map tc_to_string gs_xs)
in (FStar_All.pipe_right uu____14685 (FStar_String.concat "\n\t>")))
in (

let uu____14690 = (

let uu____14693 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____14694 = (

let uu____14697 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____14698 = (

let uu____14701 = (FStar_Syntax_Print.term_to_string im)
in (

let uu____14702 = (

let uu____14705 = (FStar_Syntax_Print.tag_of_term im)
in (

let uu____14706 = (

let uu____14709 = (

let uu____14710 = (FStar_List.map (prob_to_string env1) sub_probs)
in (FStar_All.pipe_right uu____14710 (FStar_String.concat ", ")))
in (

let uu____14715 = (

let uu____14718 = (FStar_TypeChecker_Normalize.term_to_string env1 formula)
in (uu____14718)::[])
in (uu____14709)::uu____14715))
in (uu____14705)::uu____14706))
in (uu____14701)::uu____14702))
in (uu____14697)::uu____14698))
in (uu____14693)::uu____14694))
in (uu____14684)::uu____14690))
in (FStar_Util.print "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" uu____14681))
end
| uu____14719 -> begin
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

let imitate' = (fun orig env1 wl1 uu___116_14748 -> (match (uu___116_14748) with
| FStar_Pervasives_Native.None -> begin
(giveup env1 "unable to compute subterms" orig)
end
| FStar_Pervasives_Native.Some (p) -> begin
(imitate orig env1 wl1 p)
end))
in (

let project = (fun orig env1 wl1 i p -> (

let uu____14790 = p
in (match (uu____14790) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____14887 = (FStar_List.nth ps i)
in (match (uu____14887) with
| (pi, uu____14891) -> begin
(

let uu____14896 = (FStar_List.nth xs i)
in (match (uu____14896) with
| (xi, uu____14908) -> begin
(

let rec gs = (fun k -> (

let uu____14923 = (

let uu____14936 = (FStar_TypeChecker_Normalize.unfold_whnf env1 k)
in (FStar_Syntax_Util.arrow_formals uu____14936))
in (match (uu____14923) with
| (bs, k1) -> begin
(

let rec aux = (fun subst1 bs1 -> (match (bs1) with
| [] -> begin
(([]), ([]))
end
| ((a, uu____15015))::tl1 -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst1 a.FStar_Syntax_Syntax.sort)
in (

let uu____15028 = (new_uvar r xs k_a)
in (match (uu____15028) with
| (gi_xs, gi) -> begin
(

let gi_xs1 = (FStar_TypeChecker_Normalize.eta_expand env1 gi_xs)
in (

let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps FStar_Pervasives_Native.None r)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((a), (gi_xs1))))::subst1
in (

let uu____15050 = (aux subst2 tl1)
in (match (uu____15050) with
| (gi_xs', gi_ps') -> begin
(

let uu____15077 = (

let uu____15080 = (FStar_Syntax_Syntax.as_arg gi_xs1)
in (uu____15080)::gi_xs')
in (

let uu____15081 = (

let uu____15084 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (uu____15084)::gi_ps')
in ((uu____15077), (uu____15081))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in (

let uu____15089 = (

let uu____15090 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation uu____15090))
in (match (uu____15089) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____15093 -> begin
(

let uu____15094 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (uu____15094) with
| (g_xs, uu____15106) -> begin
(

let xi1 = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (

let uu____15117 = (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs FStar_Pervasives_Native.None r)
in (

let uu____15118 = (FStar_All.pipe_right (FStar_Syntax_Util.residual_comp_of_comp c) (fun _0_35 -> FStar_Pervasives_Native.Some (_0_35)))
in (FStar_Syntax_Util.abs xs uu____15117 uu____15118)))
in (

let sub1 = (

let uu____15124 = (

let uu____15129 = (p_scope orig)
in (

let uu____15130 = (FStar_Syntax_Syntax.mk_Tm_app proj ps FStar_Pervasives_Native.None r)
in (

let uu____15133 = (

let uu____15136 = (FStar_List.map (fun uu____15151 -> (match (uu____15151) with
| (uu____15160, uu____15161, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h uu____15136))
in (mk_problem uu____15129 orig uu____15130 (p_rel orig) uu____15133 FStar_Pervasives_Native.None "projection"))))
in (FStar_All.pipe_left (fun _0_36 -> FStar_TypeChecker_Common.TProb (_0_36)) uu____15124))
in ((

let uu____15176 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____15176) with
| true -> begin
(

let uu____15177 = (FStar_Syntax_Print.term_to_string proj)
in (

let uu____15178 = (prob_to_string env1 sub1)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" uu____15177 uu____15178)))
end
| uu____15179 -> begin
()
end));
(

let wl2 = (

let uu____15181 = (

let uu____15184 = (FStar_All.pipe_left FStar_Pervasives_Native.fst (p_guard sub1))
in FStar_Pervasives_Native.Some (uu____15184))
in (solve_prob orig uu____15181 ((TERM (((u), (proj))))::[]) wl1))
in (

let uu____15193 = (solve env1 (attempt ((sub1)::[]) wl2))
in (FStar_All.pipe_left (fun _0_37 -> FStar_Pervasives_Native.Some (_0_37)) uu____15193)));
))))
end))
end)))
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl1 -> (

let uu____15234 = lhs
in (match (uu____15234) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let uu____15272 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (uu____15272) with
| (xs, c) -> begin
(match ((Prims.op_Equality (FStar_List.length xs) (FStar_List.length ps))) with
| true -> begin
(

let uu____15305 = (

let uu____15354 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____15354)))
in FStar_Pervasives_Native.Some (uu____15305))
end
| uu____15479 -> begin
(

let rec elim = (fun k args -> (

let k1 = (FStar_TypeChecker_Normalize.unfold_whnf env k)
in (

let uu____15508 = (

let uu____15515 = (

let uu____15516 = (FStar_Syntax_Subst.compress k1)
in uu____15516.FStar_Syntax_Syntax.n)
in ((uu____15515), (args)))
in (match (uu____15508) with
| (uu____15527, []) -> begin
(

let uu____15530 = (

let uu____15541 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____15541)))
in FStar_Pervasives_Native.Some (uu____15530))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____15562), uu____15563) -> begin
(

let uu____15584 = (FStar_Syntax_Util.head_and_args k1)
in (match (uu____15584) with
| (uv1, uv_args) -> begin
(

let uu____15627 = (

let uu____15628 = (FStar_Syntax_Subst.compress uv1)
in uu____15628.FStar_Syntax_Syntax.n)
in (match (uu____15627) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____15638) -> begin
(

let uu____15663 = (pat_vars env [] uv_args)
in (match (uu____15663) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (scope) -> begin
(

let xs1 = (FStar_All.pipe_right args (FStar_List.map (fun uu____15690 -> (

let uu____15691 = (

let uu____15692 = (

let uu____15693 = (

let uu____15698 = (

let uu____15699 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____15699 FStar_Pervasives_Native.fst))
in (new_uvar k1.FStar_Syntax_Syntax.pos scope uu____15698))
in (FStar_Pervasives_Native.fst uu____15693))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (k1.FStar_Syntax_Syntax.pos)) uu____15692))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____15691)))))
in (

let c1 = (

let uu____15709 = (

let uu____15710 = (

let uu____15715 = (

let uu____15716 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____15716 FStar_Pervasives_Native.fst))
in (new_uvar k1.FStar_Syntax_Syntax.pos scope uu____15715))
in (FStar_Pervasives_Native.fst uu____15710))
in (FStar_Syntax_Syntax.mk_Total uu____15709))
in (

let k' = (FStar_Syntax_Util.arrow xs1 c1)
in (

let uv_sol = (

let uu____15729 = (

let uu____15732 = (

let uu____15733 = (

let uu____15736 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____15736 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Util.residual_tot uu____15733))
in FStar_Pervasives_Native.Some (uu____15732))
in (FStar_Syntax_Util.abs scope k' uu____15729))
in ((def_check_closed (p_loc orig) "solve_t_flex_rigid.subterms" uv_sol);
(FStar_Syntax_Util.set_uvar uvar uv_sol);
FStar_Pervasives_Native.Some (((xs1), (c1)));
)))))
end))
end
| uu____15755 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_app (uu____15760), uu____15761) -> begin
(

let uu____15780 = (FStar_Syntax_Util.head_and_args k1)
in (match (uu____15780) with
| (uv1, uv_args) -> begin
(

let uu____15823 = (

let uu____15824 = (FStar_Syntax_Subst.compress uv1)
in uu____15824.FStar_Syntax_Syntax.n)
in (match (uu____15823) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____15834) -> begin
(

let uu____15859 = (pat_vars env [] uv_args)
in (match (uu____15859) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (scope) -> begin
(

let xs1 = (FStar_All.pipe_right args (FStar_List.map (fun uu____15886 -> (

let uu____15887 = (

let uu____15888 = (

let uu____15889 = (

let uu____15894 = (

let uu____15895 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____15895 FStar_Pervasives_Native.fst))
in (new_uvar k1.FStar_Syntax_Syntax.pos scope uu____15894))
in (FStar_Pervasives_Native.fst uu____15889))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (k1.FStar_Syntax_Syntax.pos)) uu____15888))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____15887)))))
in (

let c1 = (

let uu____15905 = (

let uu____15906 = (

let uu____15911 = (

let uu____15912 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____15912 FStar_Pervasives_Native.fst))
in (new_uvar k1.FStar_Syntax_Syntax.pos scope uu____15911))
in (FStar_Pervasives_Native.fst uu____15906))
in (FStar_Syntax_Syntax.mk_Total uu____15905))
in (

let k' = (FStar_Syntax_Util.arrow xs1 c1)
in (

let uv_sol = (

let uu____15925 = (

let uu____15928 = (

let uu____15929 = (

let uu____15932 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____15932 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Util.residual_tot uu____15929))
in FStar_Pervasives_Native.Some (uu____15928))
in (FStar_Syntax_Util.abs scope k' uu____15925))
in ((def_check_closed (p_loc orig) "solve_t_flex_rigid.subterms" uv_sol);
(FStar_Syntax_Util.set_uvar uvar uv_sol);
FStar_Pervasives_Native.Some (((xs1), (c1)));
)))))
end))
end
| uu____15951 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs1, c1), uu____15958) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs1)
in (match ((Prims.op_Equality n_xs n_args)) with
| true -> begin
(

let uu____15999 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (FStar_All.pipe_right uu____15999 (fun _0_38 -> FStar_Pervasives_Native.Some (_0_38))))
end
| uu____16018 -> begin
(match ((n_xs < n_args)) with
| true -> begin
(

let uu____16035 = (FStar_Util.first_N n_xs args)
in (match (uu____16035) with
| (args1, rest) -> begin
(

let uu____16064 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (match (uu____16064) with
| (xs2, c2) -> begin
(

let uu____16077 = (elim (FStar_Syntax_Util.comp_result c2) rest)
in (FStar_Util.bind_opt uu____16077 (fun uu____16101 -> (match (uu____16101) with
| (xs', c3) -> begin
FStar_Pervasives_Native.Some ((((FStar_List.append xs2 xs')), (c3)))
end))))
end))
end))
end
| uu____16140 -> begin
(

let uu____16141 = (FStar_Util.first_N n_args xs1)
in (match (uu____16141) with
| (xs2, rest) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c1)))) FStar_Pervasives_Native.None k1.FStar_Syntax_Syntax.pos)
in (

let uu____16209 = (

let uu____16214 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs2 uu____16214))
in (FStar_All.pipe_right uu____16209 (fun _0_39 -> FStar_Pervasives_Native.Some (_0_39)))))
end))
end)
end)))
end
| uu____16229 -> begin
(

let uu____16236 = (

let uu____16241 = (

let uu____16242 = (FStar_Syntax_Print.uvar_to_string uv)
in (

let uu____16243 = (FStar_Syntax_Print.term_to_string k1)
in (

let uu____16244 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" uu____16242 uu____16243 uu____16244))))
in ((FStar_Errors.Fatal_IllTyped), (uu____16241)))
in (FStar_Errors.raise_error uu____16236 t1.FStar_Syntax_Syntax.pos))
end))))
in (

let uu____16251 = (elim k_uv ps)
in (FStar_Util.bind_opt uu____16251 (fun uu____16308 -> (match (uu____16308) with
| (xs1, c1) -> begin
(

let uu____16359 = (

let uu____16402 = (decompose env t2)
in ((((((uv), (k_uv))), (xs1), (c1))), (ps), (uu____16402)))
in FStar_Pervasives_Native.Some (uu____16359))
end)))))
end)
end)))
in (

let imitate_or_project = (fun n1 lhs1 rhs stopt -> (

let fail1 = (fun uu____16539 -> (giveup env "flex-rigid case failed all backtracking attempts" orig))
in (

let rec try_project = (fun st i -> (match ((i >= n1)) with
| true -> begin
(fail1 ())
end
| uu____16557 -> begin
(

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____16559 = (project orig env wl1 i st)
in (match (uu____16559) with
| FStar_Pervasives_Native.None -> begin
((FStar_Syntax_Unionfind.rollback tx);
(try_project st (i + (Prims.parse_int "1")));
)
end
| FStar_Pervasives_Native.Some (Failed (uu____16573)) -> begin
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

let uu____16588 = (imitate orig env wl1 st)
in (match (uu____16588) with
| Failed (uu____16593) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(try_project st (Prims.parse_int "0"));
)
end
| sol -> begin
sol
end))))
end
| uu____16606 -> begin
(fail1 ())
end))))
in (

let pattern_eq_imitate_or_project = (fun n1 lhs1 rhs stopt -> (

let uu____16632 = (force_quasi_pattern FStar_Pervasives_Native.None lhs1)
in (match (uu____16632) with
| FStar_Pervasives_Native.None -> begin
(imitate_or_project n1 lhs1 rhs stopt)
end
| FStar_Pervasives_Native.Some (sol, forced_lhs_pattern) -> begin
(

let uu____16655 = forced_lhs_pattern
in (match (uu____16655) with
| (lhs_t, uu____16657, uu____16658, uu____16659) -> begin
((

let uu____16661 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____16661) with
| true -> begin
(

let uu____16662 = lhs1
in (match (uu____16662) with
| (t0, uu____16664, uu____16665, uu____16666) -> begin
(

let uu____16667 = forced_lhs_pattern
in (match (uu____16667) with
| (t11, uu____16669, uu____16670, uu____16671) -> begin
(

let uu____16672 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____16673 = (FStar_Syntax_Print.term_to_string t11)
in (FStar_Util.print2 "force_quasi_pattern succeeded, turning %s into %s\n" uu____16672 uu____16673)))
end))
end))
end
| uu____16674 -> begin
()
end));
(

let rhs_vars = (FStar_Syntax_Free.names rhs)
in (

let lhs_vars = (FStar_Syntax_Free.names lhs_t)
in (

let uu____16681 = (FStar_Util.set_is_subset_of rhs_vars lhs_vars)
in (match (uu____16681) with
| true -> begin
((

let uu____16683 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____16683) with
| true -> begin
(

let uu____16684 = (FStar_Syntax_Print.term_to_string rhs)
in (

let uu____16685 = (names_to_string rhs_vars)
in (

let uu____16686 = (names_to_string lhs_vars)
in (FStar_Util.print3 "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n" uu____16684 uu____16685 uu____16686))))
end
| uu____16687 -> begin
()
end));
(

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let wl2 = (extend_solution (p_pid orig) ((sol)::[]) wl1)
in (

let uu____16690 = (

let uu____16691 = (FStar_TypeChecker_Common.as_tprob orig)
in (solve_t env uu____16691 wl2))
in (match (uu____16690) with
| Failed (uu____16692) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(imitate_or_project n1 lhs1 rhs stopt);
)
end
| sol1 -> begin
sol1
end))));
)
end
| uu____16699 -> begin
((

let uu____16701 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Rel")))
in (match (uu____16701) with
| true -> begin
(FStar_Util.print_string "fvar check failed for quasi pattern ... im/proj\n")
end
| uu____16702 -> begin
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

let uu____16718 = (FStar_Syntax_Util.head_and_args t21)
in (match (uu____16718) with
| (hd1, uu____16734) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____16755) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____16768) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____16769) -> begin
true
end
| uu____16786 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd1)
in (

let uu____16790 = (FStar_Util.set_is_subset_of fvs_hd fvs1)
in (match (uu____16790) with
| true -> begin
true
end
| uu____16791 -> begin
((

let uu____16793 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____16793) with
| true -> begin
(

let uu____16794 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s\n" uu____16794))
end
| uu____16795 -> begin
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

let uu____16814 = (occurs_check env wl1 ((uv), (k_uv)) t21)
in (match (uu____16814) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____16827 = (

let uu____16828 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____16828))
in (giveup_or_defer1 orig uu____16827))
end
| uu____16829 -> begin
(

let uu____16830 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____16830) with
| true -> begin
(

let uu____16831 = (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t21)) && (Prims.op_disEquality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____16831) with
| true -> begin
(

let uu____16832 = (subterms args_lhs)
in (imitate' orig env wl1 uu____16832))
end
| uu____16835 -> begin
((

let uu____16837 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____16837) with
| true -> begin
(

let uu____16838 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____16839 = (names_to_string fvs1)
in (

let uu____16840 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" uu____16838 uu____16839 uu____16840))))
end
| uu____16841 -> begin
()
end));
(use_pattern_equality orig env wl1 lhs1 vars t21);
)
end))
end
| uu____16842 -> begin
(match ((((not (patterns_only)) && wl1.defer_ok) && (Prims.op_disEquality (p_rel orig) FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl1))
end
| uu____16843 -> begin
(

let uu____16844 = ((not (patterns_only)) && (check_head fvs1 t21))
in (match (uu____16844) with
| true -> begin
((

let uu____16846 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____16846) with
| true -> begin
(

let uu____16847 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____16848 = (names_to_string fvs1)
in (

let uu____16849 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n" uu____16847 uu____16848 uu____16849))))
end
| uu____16850 -> begin
()
end));
(

let uu____16851 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) lhs1 t21 uu____16851));
)
end
| uu____16860 -> begin
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
| uu____16861 -> begin
(

let uu____16862 = (

let uu____16863 = (FStar_Syntax_Free.names t1)
in (check_head uu____16863 t2))
in (match (uu____16862) with
| true -> begin
(

let n_args_lhs = (FStar_List.length args_lhs)
in ((

let uu____16874 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____16874) with
| true -> begin
(

let uu____16875 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____16876 = (FStar_Util.string_of_int n_args_lhs)
in (FStar_Util.print2 "Not a pattern (%s) ... (lhs has %s args)\n" uu____16875 uu____16876)))
end
| uu____16883 -> begin
()
end));
(

let uu____16884 = (subterms args_lhs)
in (pattern_eq_imitate_or_project n_args_lhs (FStar_Pervasives_Native.fst lhs) t2 uu____16884));
))
end
| uu____16895 -> begin
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
| uu____16912 -> begin
(

let solve_both_pats = (fun wl1 uu____16975 uu____16976 r -> (match (((uu____16975), (uu____16976))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
(

let uu____17174 = ((FStar_Syntax_Unionfind.equiv u1 u2) && (binders_eq xs ys))
in (match (uu____17174) with
| true -> begin
(

let uu____17175 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____17175))
end
| uu____17176 -> begin
(

let xs1 = (sn_binders env xs)
in (

let ys1 = (sn_binders env ys)
in (

let zs = (intersect_vars xs1 ys1)
in ((

let uu____17199 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____17199) with
| true -> begin
(

let uu____17200 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____17201 = (FStar_Syntax_Print.binders_to_string ", " ys1)
in (

let uu____17202 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (

let uu____17203 = (FStar_Syntax_Print.term_to_string k1)
in (

let uu____17204 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" uu____17200 uu____17201 uu____17202 uu____17203 uu____17204))))))
end
| uu____17205 -> begin
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

let uu____17270 = (FStar_Syntax_Util.subst_of_list xs2 args)
in (FStar_Syntax_Subst.subst uu____17270 k))
end
| uu____17273 -> begin
(match ((args_len < xs_len)) with
| true -> begin
(

let uu____17284 = (FStar_Util.first_N args_len xs2)
in (match (uu____17284) with
| (xs3, xs_rest) -> begin
(

let k3 = (

let uu____17338 = (FStar_Syntax_Syntax.mk_GTotal k)
in (FStar_Syntax_Util.arrow xs_rest uu____17338))
in (

let uu____17341 = (FStar_Syntax_Util.subst_of_list xs3 args)
in (FStar_Syntax_Subst.subst uu____17341 k3)))
end))
end
| uu____17344 -> begin
(

let uu____17345 = (

let uu____17346 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____17347 = (FStar_Syntax_Print.binders_to_string ", " xs2)
in (

let uu____17348 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" uu____17346 uu____17347 uu____17348))))
in (failwith uu____17345))
end)
end))))
in (

let uu____17349 = (

let uu____17356 = (

let uu____17369 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals uu____17369))
in (match (uu____17356) with
| (bs, k1') -> begin
(

let uu____17394 = (

let uu____17407 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals uu____17407))
in (match (uu____17394) with
| (cs, k2') -> begin
(

let k1'_xs = (subst_k k1' bs args1)
in (

let k2'_ys = (subst_k k2' cs args2)
in (

let sub_prob = (

let uu____17435 = (

let uu____17440 = (p_scope orig)
in (mk_problem uu____17440 orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys FStar_Pervasives_Native.None "flex-flex kinding"))
in (FStar_All.pipe_left (fun _0_40 -> FStar_TypeChecker_Common.TProb (_0_40)) uu____17435))
in (

let uu____17445 = (

let uu____17450 = (

let uu____17451 = (FStar_Syntax_Subst.compress k1')
in uu____17451.FStar_Syntax_Syntax.n)
in (

let uu____17454 = (

let uu____17455 = (FStar_Syntax_Subst.compress k2')
in uu____17455.FStar_Syntax_Syntax.n)
in ((uu____17450), (uu____17454))))
in (match (uu____17445) with
| (FStar_Syntax_Syntax.Tm_type (uu____17464), uu____17465) -> begin
((k1'_xs), ((sub_prob)::[]))
end
| (uu____17468, FStar_Syntax_Syntax.Tm_type (uu____17469)) -> begin
((k2'_ys), ((sub_prob)::[]))
end
| uu____17472 -> begin
(

let uu____17477 = (FStar_Syntax_Util.type_u ())
in (match (uu____17477) with
| (t, uu____17489) -> begin
(

let uu____17490 = (new_uvar r zs t)
in (match (uu____17490) with
| (k_zs, uu____17502) -> begin
(

let kprob = (

let uu____17504 = (

let uu____17509 = (p_scope orig)
in (mk_problem uu____17509 orig k1'_xs FStar_TypeChecker_Common.EQ k_zs FStar_Pervasives_Native.None "flex-flex kinding"))
in (FStar_All.pipe_left (fun _0_41 -> FStar_TypeChecker_Common.TProb (_0_41)) uu____17504))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end)))))
end))
end))
in (match (uu____17349) with
| (k_u', sub_probs) -> begin
(

let uu____17522 = (

let uu____17533 = (

let uu____17534 = (new_uvar r zs k_u')
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____17534))
in (

let uu____17543 = (

let uu____17546 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs1 uu____17546))
in (

let uu____17549 = (

let uu____17552 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys1 uu____17552))
in ((uu____17533), (uu____17543), (uu____17549)))))
in (match (uu____17522) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs1 u_zs)
in (

let uu____17571 = (occurs_check env wl1 ((u1), (k1)) sub1)
in (match (uu____17571) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occcurs check")
end
| uu____17584 -> begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in (

let uu____17590 = (FStar_Syntax_Unionfind.equiv u1 u2)
in (match (uu____17590) with
| true -> begin
(

let wl2 = (solve_prob orig FStar_Pervasives_Native.None ((sol1)::[]) wl1)
in (solve env wl2))
end
| uu____17592 -> begin
(

let sub2 = (u_abs knew2 ys1 u_zs)
in (

let uu____17594 = (occurs_check env wl1 ((u2), (k2)) sub2)
in (match (uu____17594) with
| (occurs_ok1, msg1) -> begin
(match ((not (occurs_ok1))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occurs check")
end
| uu____17607 -> begin
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

let solve_one_pat = (fun uu____17651 uu____17652 -> (match (((uu____17651), (uu____17652))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
((

let uu____17770 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____17770) with
| true -> begin
(

let uu____17771 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____17772 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" uu____17771 uu____17772)))
end
| uu____17773 -> begin
()
end));
(

let uu____17774 = (FStar_Syntax_Unionfind.equiv u1 u2)
in (match (uu____17774) with
| true -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____17793 uu____17794 -> (match (((uu____17793), (uu____17794))) with
| ((a, uu____17812), (t21, uu____17814)) -> begin
(

let uu____17823 = (

let uu____17828 = (p_scope orig)
in (

let uu____17829 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem uu____17828 orig uu____17829 FStar_TypeChecker_Common.EQ t21 FStar_Pervasives_Native.None "flex-flex index")))
in (FStar_All.pipe_right uu____17823 (fun _0_42 -> FStar_TypeChecker_Common.TProb (_0_42))))
end)) xs args2)
in (

let guard = (

let uu____17835 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) FStar_Pervasives_Native.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____17835))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))))
end
| uu____17845 -> begin
(

let t21 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t21)
in (

let uu____17850 = (occurs_check env wl ((u1), (k1)) t21)
in (match (uu____17850) with
| (occurs_ok, uu____17858) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in (

let uu____17866 = (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars))
in (match (uu____17866) with
| true -> begin
(

let sol = (

let uu____17868 = (

let uu____17877 = (u_abs k1 xs t21)
in ((((u1), (k1))), (uu____17877)))
in TERM (uu____17868))
in (

let wl1 = (solve_prob orig FStar_Pervasives_Native.None ((sol)::[]) wl)
in (solve env wl1)))
end
| uu____17883 -> begin
(

let uu____17884 = (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok))
in (match (uu____17884) with
| true -> begin
(

let uu____17885 = (force_quasi_pattern (FStar_Pervasives_Native.Some (xs)) ((t21), (u2), (k2), (args2)))
in (match (uu____17885) with
| FStar_Pervasives_Native.None -> begin
(giveup_or_defer1 orig "flex-flex constraint")
end
| FStar_Pervasives_Native.Some (sol, (uu____17909, u21, k21, ys)) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____17935 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____17935) with
| true -> begin
(

let uu____17936 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" uu____17936))
end
| uu____17937 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____17943 -> begin
(giveup env "impossible" orig)
end);
))
end))
end
| uu____17944 -> begin
(giveup_or_defer1 orig "flex-flex constraint")
end))
end)))
end))))
end));
)
end))
in (

let uu____17945 = lhs
in (match (uu____17945) with
| (t1, u1, k1, args1) -> begin
(

let uu____17950 = rhs
in (match (uu____17950) with
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
| uu____17990 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: neither side is a pattern")
end
| uu____17999 -> begin
(

let uu____18000 = (force_quasi_pattern FStar_Pervasives_Native.None ((t1), (u1), (k1), (args1)))
in (match (uu____18000) with
| FStar_Pervasives_Native.None -> begin
(giveup env "flex-flex: neither side is a pattern, nor is coercible to a pattern" orig)
end
| FStar_Pervasives_Native.Some (sol, uu____18018) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____18025 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____18025) with
| true -> begin
(

let uu____18026 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" uu____18026))
end
| uu____18027 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____18033 -> begin
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

let uu____18036 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____18036) with
| true -> begin
(

let uu____18037 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____18037))
end
| uu____18038 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in (

let uu____18041 = (FStar_Util.physical_equality t1 t2)
in (match (uu____18041) with
| true -> begin
(

let uu____18042 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____18042))
end
| uu____18043 -> begin
((

let uu____18045 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____18045) with
| true -> begin
(

let uu____18046 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____18047 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____18048 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print3 "Attempting %s (%s - %s)\n" uu____18046 uu____18047 uu____18048))))
end
| uu____18049 -> begin
()
end));
(

let r = (FStar_TypeChecker_Env.get_range env)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_delayed (uu____18051), uu____18052) -> begin
(failwith "Impossible: terms were not compressed")
end
| (uu____18077, FStar_Syntax_Syntax.Tm_delayed (uu____18078)) -> begin
(failwith "Impossible: terms were not compressed")
end
| (FStar_Syntax_Syntax.Tm_ascribed (uu____18103), uu____18104) -> begin
(

let uu____18131 = (

let uu___153_18132 = problem
in (

let uu____18133 = (FStar_Syntax_Util.unascribe t1)
in {FStar_TypeChecker_Common.pid = uu___153_18132.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____18133; FStar_TypeChecker_Common.relation = uu___153_18132.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___153_18132.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___153_18132.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___153_18132.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___153_18132.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___153_18132.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___153_18132.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___153_18132.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____18131 wl))
end
| (FStar_Syntax_Syntax.Tm_meta (uu____18134), uu____18135) -> begin
(

let uu____18142 = (

let uu___154_18143 = problem
in (

let uu____18144 = (FStar_Syntax_Util.unmeta t1)
in {FStar_TypeChecker_Common.pid = uu___154_18143.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____18144; FStar_TypeChecker_Common.relation = uu___154_18143.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___154_18143.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___154_18143.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___154_18143.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___154_18143.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___154_18143.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___154_18143.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___154_18143.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____18142 wl))
end
| (uu____18145, FStar_Syntax_Syntax.Tm_ascribed (uu____18146)) -> begin
(

let uu____18173 = (

let uu___155_18174 = problem
in (

let uu____18175 = (FStar_Syntax_Util.unascribe t2)
in {FStar_TypeChecker_Common.pid = uu___155_18174.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___155_18174.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___155_18174.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____18175; FStar_TypeChecker_Common.element = uu___155_18174.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___155_18174.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___155_18174.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___155_18174.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___155_18174.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___155_18174.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____18173 wl))
end
| (uu____18176, FStar_Syntax_Syntax.Tm_meta (uu____18177)) -> begin
(

let uu____18184 = (

let uu___156_18185 = problem
in (

let uu____18186 = (FStar_Syntax_Util.unmeta t2)
in {FStar_TypeChecker_Common.pid = uu___156_18185.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___156_18185.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___156_18185.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____18186; FStar_TypeChecker_Common.element = uu___156_18185.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___156_18185.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___156_18185.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___156_18185.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___156_18185.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___156_18185.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____18184 wl))
end
| (FStar_Syntax_Syntax.Tm_quoted (t11, uu____18188), FStar_Syntax_Syntax.Tm_quoted (t21, uu____18190)) -> begin
(

let uu____18199 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____18199))
end
| (FStar_Syntax_Syntax.Tm_bvar (uu____18200), uu____18201) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (uu____18202, FStar_Syntax_Syntax.Tm_bvar (uu____18203)) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (FStar_Syntax_Syntax.Tm_type (u1), FStar_Syntax_Syntax.Tm_type (u2)) -> begin
(solve_one_universe_eq env orig u1 u2 wl)
end
| (FStar_Syntax_Syntax.Tm_arrow (bs1, c1), FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) -> begin
(

let mk_c = (fun c uu___117_18262 -> (match (uu___117_18262) with
| [] -> begin
c
end
| bs -> begin
(

let uu____18284 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____18284))
end))
in (

let uu____18293 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____18293) with
| ((bs11, c11), (bs21, c21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let c12 = (FStar_Syntax_Subst.subst_comp subst1 c11)
in (

let c22 = (FStar_Syntax_Subst.subst_comp subst1 c21)
in (

let rel = (

let uu____18437 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____18437) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____18438 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (

let uu____18439 = (mk_problem scope orig c12 rel c22 FStar_Pervasives_Native.None "function co-domain")
in (FStar_All.pipe_left (fun _0_43 -> FStar_TypeChecker_Common.CProb (_0_43)) uu____18439)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___118_18521 -> (match (uu___118_18521) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____18555 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____18555) with
| ((bs11, tbody11), (bs21, tbody21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let uu____18693 = (

let uu____18698 = (FStar_Syntax_Subst.subst subst1 tbody11)
in (

let uu____18699 = (FStar_Syntax_Subst.subst subst1 tbody21)
in (mk_problem scope orig uu____18698 problem.FStar_TypeChecker_Common.relation uu____18699 FStar_Pervasives_Native.None "lambda co-domain")))
in (FStar_All.pipe_left (fun _0_44 -> FStar_TypeChecker_Common.TProb (_0_44)) uu____18693))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (uu____18704), uu____18705) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____18732) -> begin
true
end
| uu____18749 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____18774 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____18782 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let force_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
t
end
| uu____18799 -> begin
(

let uu____18800 = (env.FStar_TypeChecker_Env.type_of (

let uu___157_18808 = env
in {FStar_TypeChecker_Env.solver = uu___157_18808.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___157_18808.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___157_18808.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___157_18808.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___157_18808.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___157_18808.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___157_18808.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___157_18808.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___157_18808.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___157_18808.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___157_18808.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___157_18808.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___157_18808.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___157_18808.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___157_18808.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___157_18808.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___157_18808.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___157_18808.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___157_18808.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___157_18808.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___157_18808.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___157_18808.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___157_18808.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___157_18808.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___157_18808.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___157_18808.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___157_18808.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___157_18808.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___157_18808.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___157_18808.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___157_18808.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___157_18808.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___157_18808.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___157_18808.FStar_TypeChecker_Env.dep_graph}) t)
in (match (uu____18800) with
| (uu____18811, ty, uu____18813) -> begin
(

let uu____18814 = (FStar_TypeChecker_Normalize.unfold_whnf env ty)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env t uu____18814))
end))
end))
in (

let uu____18815 = (

let uu____18832 = (maybe_eta t1)
in (

let uu____18839 = (maybe_eta t2)
in ((uu____18832), (uu____18839))))
in (match (uu____18815) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___158_18881 = problem
in {FStar_TypeChecker_Common.pid = uu___158_18881.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___158_18881.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___158_18881.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___158_18881.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___158_18881.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___158_18881.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___158_18881.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___158_18881.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____18904 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____18904) with
| true -> begin
(

let uu____18905 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____18905 t_abs wl))
end
| uu____18912 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___159_18920 = problem
in {FStar_TypeChecker_Common.pid = uu___159_18920.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___159_18920.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___159_18920.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___159_18920.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___159_18920.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___159_18920.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___159_18920.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___159_18920.FStar_TypeChecker_Common.rank}) wl)
end
| uu____18923 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____18944 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____18944) with
| true -> begin
(

let uu____18945 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____18945 t_abs wl))
end
| uu____18952 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___159_18960 = problem
in {FStar_TypeChecker_Common.pid = uu___159_18960.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___159_18960.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___159_18960.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___159_18960.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___159_18960.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___159_18960.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___159_18960.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___159_18960.FStar_TypeChecker_Common.rank}) wl)
end
| uu____18963 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| uu____18964 -> begin
(failwith "Impossible: at least one side is an abstraction")
end)))))
end
| (uu____18981, FStar_Syntax_Syntax.Tm_abs (uu____18982)) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____19009) -> begin
true
end
| uu____19026 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____19051 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____19059 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let force_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
t
end
| uu____19076 -> begin
(

let uu____19077 = (env.FStar_TypeChecker_Env.type_of (

let uu___157_19085 = env
in {FStar_TypeChecker_Env.solver = uu___157_19085.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___157_19085.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___157_19085.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___157_19085.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___157_19085.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___157_19085.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___157_19085.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___157_19085.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___157_19085.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___157_19085.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___157_19085.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___157_19085.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___157_19085.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___157_19085.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___157_19085.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___157_19085.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___157_19085.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___157_19085.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___157_19085.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___157_19085.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___157_19085.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___157_19085.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___157_19085.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___157_19085.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___157_19085.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___157_19085.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___157_19085.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___157_19085.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___157_19085.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___157_19085.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___157_19085.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___157_19085.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___157_19085.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___157_19085.FStar_TypeChecker_Env.dep_graph}) t)
in (match (uu____19077) with
| (uu____19088, ty, uu____19090) -> begin
(

let uu____19091 = (FStar_TypeChecker_Normalize.unfold_whnf env ty)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env t uu____19091))
end))
end))
in (

let uu____19092 = (

let uu____19109 = (maybe_eta t1)
in (

let uu____19116 = (maybe_eta t2)
in ((uu____19109), (uu____19116))))
in (match (uu____19092) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___158_19158 = problem
in {FStar_TypeChecker_Common.pid = uu___158_19158.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___158_19158.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___158_19158.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___158_19158.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___158_19158.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___158_19158.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___158_19158.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___158_19158.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____19181 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____19181) with
| true -> begin
(

let uu____19182 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____19182 t_abs wl))
end
| uu____19189 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___159_19197 = problem
in {FStar_TypeChecker_Common.pid = uu___159_19197.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___159_19197.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___159_19197.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___159_19197.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___159_19197.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___159_19197.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___159_19197.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___159_19197.FStar_TypeChecker_Common.rank}) wl)
end
| uu____19200 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____19221 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____19221) with
| true -> begin
(

let uu____19222 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____19222 t_abs wl))
end
| uu____19229 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___159_19237 = problem
in {FStar_TypeChecker_Common.pid = uu___159_19237.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___159_19237.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___159_19237.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___159_19237.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___159_19237.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___159_19237.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___159_19237.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___159_19237.FStar_TypeChecker_Common.rank}) wl)
end
| uu____19240 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| uu____19241 -> begin
(failwith "Impossible: at least one side is an abstraction")
end)))))
end
| (FStar_Syntax_Syntax.Tm_refine (x1, ph1), FStar_Syntax_Syntax.Tm_refine (x2, phi2)) -> begin
(

let should_delta = (((

let uu____19273 = (FStar_Syntax_Free.uvars t1)
in (FStar_Util.set_is_empty uu____19273)) && (

let uu____19285 = (FStar_Syntax_Free.uvars t2)
in (FStar_Util.set_is_empty uu____19285))) && (

let uu____19300 = (head_matches env x1.FStar_Syntax_Syntax.sort x2.FStar_Syntax_Syntax.sort)
in (match (uu____19300) with
| MisMatch (FStar_Pervasives_Native.Some (d1), FStar_Pervasives_Native.Some (d2)) -> begin
(

let is_unfoldable = (fun uu___119_19312 -> (match (uu___119_19312) with
| FStar_Syntax_Syntax.Delta_constant -> begin
true
end
| FStar_Syntax_Syntax.Delta_defined_at_level (uu____19313) -> begin
true
end
| uu____19314 -> begin
false
end))
in ((is_unfoldable d1) && (is_unfoldable d2)))
end
| uu____19315 -> begin
false
end)))
in (

let uu____19316 = (as_refinement should_delta env wl t1)
in (match (uu____19316) with
| (x11, phi1) -> begin
(

let uu____19323 = (as_refinement should_delta env wl t2)
in (match (uu____19323) with
| (x21, phi21) -> begin
(

let base_prob = (

let uu____19331 = (

let uu____19336 = (p_scope orig)
in (mk_problem uu____19336 orig x11.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x21.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type"))
in (FStar_All.pipe_left (fun _0_45 -> FStar_TypeChecker_Common.TProb (_0_45)) uu____19331))
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

let uu____19376 = (imp phi12 phi23)
in (FStar_All.pipe_right uu____19376 (guard_on_element wl problem x12))))
in (

let fallback = (fun uu____19382 -> (

let impl = (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp1 FStar_Syntax_Util.mk_iff phi11 phi22)
end
| uu____19384 -> begin
(mk_imp1 FStar_Syntax_Util.mk_imp phi11 phi22)
end)
in (

let guard = (

let uu____19388 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____19388 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env1 (attempt ((base_prob)::[]) wl1))))))
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let ref_prob = (

let uu____19397 = (

let uu____19402 = (

let uu____19403 = (p_scope orig)
in (

let uu____19410 = (

let uu____19417 = (FStar_Syntax_Syntax.mk_binder x12)
in (uu____19417)::[])
in (FStar_List.append uu____19403 uu____19410)))
in (mk_problem uu____19402 orig phi11 FStar_TypeChecker_Common.EQ phi22 FStar_Pervasives_Native.None "refinement formula"))
in (FStar_All.pipe_left (fun _0_46 -> FStar_TypeChecker_Common.TProb (_0_46)) uu____19397))
in (

let uu____19426 = (solve env1 (

let uu___160_19428 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___160_19428.ctr; defer_ok = false; smt_ok = uu___160_19428.smt_ok; tcenv = uu___160_19428.tcenv}))
in (match (uu____19426) with
| Failed (uu____19435) -> begin
(fallback ())
end
| Success (uu____19440) -> begin
(

let guard = (

let uu____19444 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (

let uu____19449 = (

let uu____19450 = (FStar_All.pipe_right (p_guard ref_prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____19450 (guard_on_element wl problem x12)))
in (FStar_Syntax_Util.mk_conj uu____19444 uu____19449)))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (

let wl2 = (

let uu___161_19459 = wl1
in {attempting = uu___161_19459.attempting; wl_deferred = uu___161_19459.wl_deferred; ctr = (wl1.ctr + (Prims.parse_int "1")); defer_ok = uu___161_19459.defer_ok; smt_ok = uu___161_19459.smt_ok; tcenv = uu___161_19459.tcenv})
in (solve env1 (attempt ((base_prob)::[]) wl2)))))
end)))
end
| uu____19460 -> begin
(fallback ())
end)))))))))
end))
end)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____19461), FStar_Syntax_Syntax.Tm_uvar (uu____19462)) -> begin
(

let uu____19495 = (destruct_flex_t t1)
in (

let uu____19496 = (destruct_flex_t t2)
in (flex_flex1 orig uu____19495 uu____19496)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19497); FStar_Syntax_Syntax.pos = uu____19498; FStar_Syntax_Syntax.vars = uu____19499}, uu____19500), FStar_Syntax_Syntax.Tm_uvar (uu____19501)) -> begin
(

let uu____19554 = (destruct_flex_t t1)
in (

let uu____19555 = (destruct_flex_t t2)
in (flex_flex1 orig uu____19554 uu____19555)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____19556), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19557); FStar_Syntax_Syntax.pos = uu____19558; FStar_Syntax_Syntax.vars = uu____19559}, uu____19560)) -> begin
(

let uu____19613 = (destruct_flex_t t1)
in (

let uu____19614 = (destruct_flex_t t2)
in (flex_flex1 orig uu____19613 uu____19614)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19615); FStar_Syntax_Syntax.pos = uu____19616; FStar_Syntax_Syntax.vars = uu____19617}, uu____19618), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19619); FStar_Syntax_Syntax.pos = uu____19620; FStar_Syntax_Syntax.vars = uu____19621}, uu____19622)) -> begin
(

let uu____19695 = (destruct_flex_t t1)
in (

let uu____19696 = (destruct_flex_t t2)
in (flex_flex1 orig uu____19695 uu____19696)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____19697), uu____19698) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(

let uu____19715 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____19715 t2 wl))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19722); FStar_Syntax_Syntax.pos = uu____19723; FStar_Syntax_Syntax.vars = uu____19724}, uu____19725), uu____19726) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(

let uu____19763 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____19763 t2 wl))
end
| (uu____19770, FStar_Syntax_Syntax.Tm_uvar (uu____19771)) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (uu____19788, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19789); FStar_Syntax_Syntax.pos = uu____19790; FStar_Syntax_Syntax.vars = uu____19791}, uu____19792)) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____19829), FStar_Syntax_Syntax.Tm_type (uu____19830)) -> begin
(solve_t' env (

let uu___162_19848 = problem
in {FStar_TypeChecker_Common.pid = uu___162_19848.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___162_19848.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___162_19848.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___162_19848.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_19848.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_19848.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_19848.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_19848.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_19848.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19849); FStar_Syntax_Syntax.pos = uu____19850; FStar_Syntax_Syntax.vars = uu____19851}, uu____19852), FStar_Syntax_Syntax.Tm_type (uu____19853)) -> begin
(solve_t' env (

let uu___162_19891 = problem
in {FStar_TypeChecker_Common.pid = uu___162_19891.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___162_19891.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___162_19891.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___162_19891.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_19891.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_19891.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_19891.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_19891.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_19891.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____19892), FStar_Syntax_Syntax.Tm_arrow (uu____19893)) -> begin
(solve_t' env (

let uu___162_19923 = problem
in {FStar_TypeChecker_Common.pid = uu___162_19923.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___162_19923.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___162_19923.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___162_19923.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_19923.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_19923.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_19923.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_19923.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_19923.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19924); FStar_Syntax_Syntax.pos = uu____19925; FStar_Syntax_Syntax.vars = uu____19926}, uu____19927), FStar_Syntax_Syntax.Tm_arrow (uu____19928)) -> begin
(solve_t' env (

let uu___162_19978 = problem
in {FStar_TypeChecker_Common.pid = uu___162_19978.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___162_19978.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___162_19978.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___162_19978.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_19978.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_19978.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_19978.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_19978.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_19978.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____19979), uu____19980) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____19997 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____19999 = (

let uu____20000 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____20000))
in (match (uu____19999) with
| true -> begin
(

let uu____20001 = (FStar_All.pipe_left (fun _0_47 -> FStar_TypeChecker_Common.TProb (_0_47)) (

let uu___163_20007 = problem
in {FStar_TypeChecker_Common.pid = uu___163_20007.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___163_20007.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___163_20007.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___163_20007.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___163_20007.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___163_20007.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___163_20007.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___163_20007.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___163_20007.FStar_TypeChecker_Common.rank}))
in (

let uu____20008 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____20001 uu____20008 t2 wl)))
end
| uu____20015 -> begin
(

let uu____20016 = (base_and_refinement env t2)
in (match (uu____20016) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____20045 = (FStar_All.pipe_left (fun _0_48 -> FStar_TypeChecker_Common.TProb (_0_48)) (

let uu___164_20051 = problem
in {FStar_TypeChecker_Common.pid = uu___164_20051.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___164_20051.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___164_20051.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___164_20051.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_20051.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_20051.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_20051.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_20051.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_20051.FStar_TypeChecker_Common.rank}))
in (

let uu____20052 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____20045 uu____20052 t_base wl)))
end
| FStar_Pervasives_Native.Some (y, phi) -> begin
(

let y' = (

let uu___165_20066 = y
in {FStar_Syntax_Syntax.ppname = uu___165_20066.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___165_20066.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let base_prob = (

let uu____20069 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_49 -> FStar_TypeChecker_Common.TProb (_0_49)) uu____20069))
in (

let guard = (

let uu____20081 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____20081 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl1)))))))
end)
end))
end)))
end)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____20089); FStar_Syntax_Syntax.pos = uu____20090; FStar_Syntax_Syntax.vars = uu____20091}, uu____20092), uu____20093) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____20130 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____20132 = (

let uu____20133 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____20133))
in (match (uu____20132) with
| true -> begin
(

let uu____20134 = (FStar_All.pipe_left (fun _0_50 -> FStar_TypeChecker_Common.TProb (_0_50)) (

let uu___163_20140 = problem
in {FStar_TypeChecker_Common.pid = uu___163_20140.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___163_20140.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___163_20140.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___163_20140.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___163_20140.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___163_20140.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___163_20140.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___163_20140.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___163_20140.FStar_TypeChecker_Common.rank}))
in (

let uu____20141 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____20134 uu____20141 t2 wl)))
end
| uu____20148 -> begin
(

let uu____20149 = (base_and_refinement env t2)
in (match (uu____20149) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____20178 = (FStar_All.pipe_left (fun _0_51 -> FStar_TypeChecker_Common.TProb (_0_51)) (

let uu___164_20184 = problem
in {FStar_TypeChecker_Common.pid = uu___164_20184.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___164_20184.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___164_20184.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___164_20184.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_20184.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_20184.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_20184.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_20184.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_20184.FStar_TypeChecker_Common.rank}))
in (

let uu____20185 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____20178 uu____20185 t_base wl)))
end
| FStar_Pervasives_Native.Some (y, phi) -> begin
(

let y' = (

let uu___165_20199 = y
in {FStar_Syntax_Syntax.ppname = uu___165_20199.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___165_20199.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let base_prob = (

let uu____20202 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_52 -> FStar_TypeChecker_Common.TProb (_0_52)) uu____20202))
in (

let guard = (

let uu____20214 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____20214 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl1)))))))
end)
end))
end)))
end)
end
| (uu____20222, FStar_Syntax_Syntax.Tm_uvar (uu____20223)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| uu____20240 -> begin
(

let uu____20241 = (base_and_refinement env t1)
in (match (uu____20241) with
| (t_base, uu____20253) -> begin
(solve_t env (

let uu___166_20267 = problem
in {FStar_TypeChecker_Common.pid = uu___166_20267.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___166_20267.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___166_20267.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_20267.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___166_20267.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___166_20267.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_20267.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_20267.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (uu____20268, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____20269); FStar_Syntax_Syntax.pos = uu____20270; FStar_Syntax_Syntax.vars = uu____20271}, uu____20272)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| uu____20309 -> begin
(

let uu____20310 = (base_and_refinement env t1)
in (match (uu____20310) with
| (t_base, uu____20322) -> begin
(solve_t env (

let uu___166_20336 = problem
in {FStar_TypeChecker_Common.pid = uu___166_20336.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___166_20336.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___166_20336.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_20336.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___166_20336.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___166_20336.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_20336.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_20336.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____20338; FStar_Syntax_Syntax.vars = uu____20339}, uu____20340); FStar_Syntax_Syntax.pos = uu____20341; FStar_Syntax_Syntax.vars = uu____20342}, uu____20343), uu____20344) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.t_refine_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.p_refine_lid)) -> begin
(

let t11 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t1)
in (solve_t env (

let uu___167_20371 = problem
in {FStar_TypeChecker_Common.pid = uu___167_20371.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___167_20371.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___167_20371.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___167_20371.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___167_20371.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___167_20371.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___167_20371.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___167_20371.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___167_20371.FStar_TypeChecker_Common.rank}) wl))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____20373; FStar_Syntax_Syntax.vars = uu____20374}, uu____20375), uu____20376) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.t_refine_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.p_refine_lid)) -> begin
(

let t11 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t1)
in (solve_t env (

let uu___167_20399 = problem
in {FStar_TypeChecker_Common.pid = uu___167_20399.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___167_20399.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___167_20399.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___167_20399.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___167_20399.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___167_20399.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___167_20399.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___167_20399.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___167_20399.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____20400, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____20402; FStar_Syntax_Syntax.vars = uu____20403}, uu____20404); FStar_Syntax_Syntax.pos = uu____20405; FStar_Syntax_Syntax.vars = uu____20406}, uu____20407)) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.t_refine_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.p_refine_lid)) -> begin
(

let t21 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t2)
in (solve_t env (

let uu___168_20434 = problem
in {FStar_TypeChecker_Common.pid = uu___168_20434.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___168_20434.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___168_20434.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___168_20434.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___168_20434.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___168_20434.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___168_20434.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___168_20434.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___168_20434.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____20435, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____20437; FStar_Syntax_Syntax.vars = uu____20438}, uu____20439)) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.t_refine_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.p_refine_lid)) -> begin
(

let t21 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t2)
in (solve_t env (

let uu___168_20462 = problem
in {FStar_TypeChecker_Common.pid = uu___168_20462.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___168_20462.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___168_20462.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___168_20462.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___168_20462.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___168_20462.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___168_20462.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___168_20462.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___168_20462.FStar_TypeChecker_Common.rank}) wl))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____20463), uu____20464) -> begin
(

let t21 = (

let uu____20474 = (base_and_refinement env t2)
in (FStar_All.pipe_left force_refinement uu____20474))
in (solve_t env (

let uu___169_20498 = problem
in {FStar_TypeChecker_Common.pid = uu___169_20498.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___169_20498.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___169_20498.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___169_20498.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___169_20498.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___169_20498.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___169_20498.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___169_20498.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___169_20498.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____20499, FStar_Syntax_Syntax.Tm_refine (uu____20500)) -> begin
(

let t11 = (

let uu____20510 = (base_and_refinement env t1)
in (FStar_All.pipe_left force_refinement uu____20510))
in (solve_t env (

let uu___170_20534 = problem
in {FStar_TypeChecker_Common.pid = uu___170_20534.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___170_20534.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___170_20534.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___170_20534.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___170_20534.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___170_20534.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___170_20534.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___170_20534.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___170_20534.FStar_TypeChecker_Common.rank}) wl))
end
| (FStar_Syntax_Syntax.Tm_match (t11, brs1), FStar_Syntax_Syntax.Tm_match (t21, brs2)) -> begin
(

let sc_prob = (

let uu____20614 = (

let uu____20619 = (p_scope orig)
in (mk_problem uu____20619 orig t11 FStar_TypeChecker_Common.EQ t21 FStar_Pervasives_Native.None "match scrutinee"))
in (FStar_All.pipe_left (fun _0_53 -> FStar_TypeChecker_Common.TProb (_0_53)) uu____20614))
in (

let rec solve_branches = (fun brs11 brs21 -> (match (((brs11), (brs21))) with
| ((br1)::rs1, (br2)::rs2) -> begin
(

let uu____20809 = br1
in (match (uu____20809) with
| (p1, w1, uu____20828) -> begin
(

let uu____20841 = br2
in (match (uu____20841) with
| (p2, w2, uu____20856) -> begin
(

let uu____20861 = (

let uu____20862 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (not (uu____20862)))
in (match (uu____20861) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____20869 -> begin
(

let uu____20870 = (FStar_Syntax_Subst.open_branch' br1)
in (match (uu____20870) with
| ((p11, w11, e1), s) -> begin
(

let uu____20913 = br2
in (match (uu____20913) with
| (p21, w21, e2) -> begin
(

let w22 = (FStar_Util.map_opt w21 (FStar_Syntax_Subst.subst s))
in (

let e21 = (FStar_Syntax_Subst.subst s e2)
in (

let scope = (

let uu____20944 = (p_scope orig)
in (

let uu____20951 = (

let uu____20958 = (FStar_Syntax_Syntax.pat_bvs p11)
in (FStar_All.pipe_left (FStar_List.map FStar_Syntax_Syntax.mk_binder) uu____20958))
in (FStar_List.append uu____20944 uu____20951)))
in (

let uu____20969 = (match (((w11), (w22))) with
| (FStar_Pervasives_Native.Some (uu____20984), FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (uu____20997)) -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Pervasives_Native.Some (w12), FStar_Pervasives_Native.Some (w23)) -> begin
(

let uu____21030 = (

let uu____21033 = (

let uu____21034 = (mk_problem scope orig w12 FStar_TypeChecker_Common.EQ w23 FStar_Pervasives_Native.None "when clause")
in (FStar_All.pipe_left (fun _0_54 -> FStar_TypeChecker_Common.TProb (_0_54)) uu____21034))
in (uu____21033)::[])
in FStar_Pervasives_Native.Some (uu____21030))
end)
in (FStar_Util.bind_opt uu____20969 (fun wprobs -> (

let prob = (

let uu____21058 = (mk_problem scope orig e1 FStar_TypeChecker_Common.EQ e21 FStar_Pervasives_Native.None "branch body")
in (FStar_All.pipe_left (fun _0_55 -> FStar_TypeChecker_Common.TProb (_0_55)) uu____21058))
in (

let uu____21069 = (solve_branches rs1 rs2)
in (FStar_Util.bind_opt uu____21069 (fun r1 -> FStar_Pervasives_Native.Some ((prob)::(FStar_List.append wprobs r1))))))))))))
end))
end))
end))
end))
end))
end
| ([], []) -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____21130 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____21161 = (solve_branches brs1 brs2)
in (match (uu____21161) with
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
| (FStar_Syntax_Syntax.Tm_match (uu____21177), uu____21178) -> begin
(

let head1 = (

let uu____21204 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____21204 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____21248 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____21248 FStar_Pervasives_Native.fst))
in ((

let uu____21290 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____21290) with
| true -> begin
(

let uu____21291 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____21292 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____21293 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____21291 uu____21292 uu____21293))))
end
| uu____21294 -> begin
()
end));
(

let uu____21295 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____21295) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____21310 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____21310) with
| true -> begin
(

let guard = (

let uu____21322 = (

let uu____21323 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____21323 FStar_Syntax_Util.Equal))
in (match (uu____21322) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____21326 -> begin
(

let uu____21327 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_56 -> FStar_Pervasives_Native.Some (_0_56)) uu____21327))
end))
in (

let uu____21330 = (solve_prob orig guard [] wl)
in (solve env uu____21330)))
end
| uu____21331 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____21332 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____21333), uu____21334) -> begin
(

let head1 = (

let uu____21344 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____21344 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____21388 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____21388 FStar_Pervasives_Native.fst))
in ((

let uu____21430 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____21430) with
| true -> begin
(

let uu____21431 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____21432 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____21433 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____21431 uu____21432 uu____21433))))
end
| uu____21434 -> begin
()
end));
(

let uu____21435 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____21435) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____21450 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____21450) with
| true -> begin
(

let guard = (

let uu____21462 = (

let uu____21463 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____21463 FStar_Syntax_Util.Equal))
in (match (uu____21462) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____21466 -> begin
(

let uu____21467 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_57 -> FStar_Pervasives_Native.Some (_0_57)) uu____21467))
end))
in (

let uu____21470 = (solve_prob orig guard [] wl)
in (solve env uu____21470)))
end
| uu____21471 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____21472 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_name (uu____21473), uu____21474) -> begin
(

let head1 = (

let uu____21478 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____21478 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____21522 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____21522 FStar_Pervasives_Native.fst))
in ((

let uu____21564 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____21564) with
| true -> begin
(

let uu____21565 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____21566 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____21567 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____21565 uu____21566 uu____21567))))
end
| uu____21568 -> begin
()
end));
(

let uu____21569 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____21569) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____21584 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____21584) with
| true -> begin
(

let guard = (

let uu____21596 = (

let uu____21597 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____21597 FStar_Syntax_Util.Equal))
in (match (uu____21596) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____21600 -> begin
(

let uu____21601 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_58 -> FStar_Pervasives_Native.Some (_0_58)) uu____21601))
end))
in (

let uu____21604 = (solve_prob orig guard [] wl)
in (solve env uu____21604)))
end
| uu____21605 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____21606 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_constant (uu____21607), uu____21608) -> begin
(

let head1 = (

let uu____21612 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____21612 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____21656 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____21656 FStar_Pervasives_Native.fst))
in ((

let uu____21698 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____21698) with
| true -> begin
(

let uu____21699 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____21700 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____21701 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____21699 uu____21700 uu____21701))))
end
| uu____21702 -> begin
()
end));
(

let uu____21703 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____21703) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____21718 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____21718) with
| true -> begin
(

let guard = (

let uu____21730 = (

let uu____21731 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____21731 FStar_Syntax_Util.Equal))
in (match (uu____21730) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____21734 -> begin
(

let uu____21735 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_59 -> FStar_Pervasives_Native.Some (_0_59)) uu____21735))
end))
in (

let uu____21738 = (solve_prob orig guard [] wl)
in (solve env uu____21738)))
end
| uu____21739 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____21740 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____21741), uu____21742) -> begin
(

let head1 = (

let uu____21746 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____21746 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____21790 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____21790 FStar_Pervasives_Native.fst))
in ((

let uu____21832 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____21832) with
| true -> begin
(

let uu____21833 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____21834 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____21835 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____21833 uu____21834 uu____21835))))
end
| uu____21836 -> begin
()
end));
(

let uu____21837 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____21837) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____21852 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____21852) with
| true -> begin
(

let guard = (

let uu____21864 = (

let uu____21865 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____21865 FStar_Syntax_Util.Equal))
in (match (uu____21864) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____21868 -> begin
(

let uu____21869 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_60 -> FStar_Pervasives_Native.Some (_0_60)) uu____21869))
end))
in (

let uu____21872 = (solve_prob orig guard [] wl)
in (solve env uu____21872)))
end
| uu____21873 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____21874 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_app (uu____21875), uu____21876) -> begin
(

let head1 = (

let uu____21894 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____21894 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____21938 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____21938 FStar_Pervasives_Native.fst))
in ((

let uu____21980 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____21980) with
| true -> begin
(

let uu____21981 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____21982 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____21983 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____21981 uu____21982 uu____21983))))
end
| uu____21984 -> begin
()
end));
(

let uu____21985 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____21985) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____22000 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____22000) with
| true -> begin
(

let guard = (

let uu____22012 = (

let uu____22013 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____22013 FStar_Syntax_Util.Equal))
in (match (uu____22012) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____22016 -> begin
(

let uu____22017 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_61 -> FStar_Pervasives_Native.Some (_0_61)) uu____22017))
end))
in (

let uu____22020 = (solve_prob orig guard [] wl)
in (solve env uu____22020)))
end
| uu____22021 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____22022 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____22023, FStar_Syntax_Syntax.Tm_match (uu____22024)) -> begin
(

let head1 = (

let uu____22050 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22050 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22094 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22094 FStar_Pervasives_Native.fst))
in ((

let uu____22136 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____22136) with
| true -> begin
(

let uu____22137 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22138 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22139 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22137 uu____22138 uu____22139))))
end
| uu____22140 -> begin
()
end));
(

let uu____22141 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____22141) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____22156 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____22156) with
| true -> begin
(

let guard = (

let uu____22168 = (

let uu____22169 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____22169 FStar_Syntax_Util.Equal))
in (match (uu____22168) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____22172 -> begin
(

let uu____22173 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_62 -> FStar_Pervasives_Native.Some (_0_62)) uu____22173))
end))
in (

let uu____22176 = (solve_prob orig guard [] wl)
in (solve env uu____22176)))
end
| uu____22177 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____22178 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____22179, FStar_Syntax_Syntax.Tm_uinst (uu____22180)) -> begin
(

let head1 = (

let uu____22190 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22190 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22234 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22234 FStar_Pervasives_Native.fst))
in ((

let uu____22276 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____22276) with
| true -> begin
(

let uu____22277 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22278 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22279 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22277 uu____22278 uu____22279))))
end
| uu____22280 -> begin
()
end));
(

let uu____22281 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____22281) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____22296 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____22296) with
| true -> begin
(

let guard = (

let uu____22308 = (

let uu____22309 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____22309 FStar_Syntax_Util.Equal))
in (match (uu____22308) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____22312 -> begin
(

let uu____22313 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_63 -> FStar_Pervasives_Native.Some (_0_63)) uu____22313))
end))
in (

let uu____22316 = (solve_prob orig guard [] wl)
in (solve env uu____22316)))
end
| uu____22317 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____22318 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____22319, FStar_Syntax_Syntax.Tm_name (uu____22320)) -> begin
(

let head1 = (

let uu____22324 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22324 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22368 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22368 FStar_Pervasives_Native.fst))
in ((

let uu____22410 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____22410) with
| true -> begin
(

let uu____22411 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22412 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22413 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22411 uu____22412 uu____22413))))
end
| uu____22414 -> begin
()
end));
(

let uu____22415 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____22415) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____22430 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____22430) with
| true -> begin
(

let guard = (

let uu____22442 = (

let uu____22443 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____22443 FStar_Syntax_Util.Equal))
in (match (uu____22442) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____22446 -> begin
(

let uu____22447 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_64 -> FStar_Pervasives_Native.Some (_0_64)) uu____22447))
end))
in (

let uu____22450 = (solve_prob orig guard [] wl)
in (solve env uu____22450)))
end
| uu____22451 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____22452 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____22453, FStar_Syntax_Syntax.Tm_constant (uu____22454)) -> begin
(

let head1 = (

let uu____22458 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22458 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22502 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22502 FStar_Pervasives_Native.fst))
in ((

let uu____22544 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____22544) with
| true -> begin
(

let uu____22545 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22546 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22547 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22545 uu____22546 uu____22547))))
end
| uu____22548 -> begin
()
end));
(

let uu____22549 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____22549) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____22564 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____22564) with
| true -> begin
(

let guard = (

let uu____22576 = (

let uu____22577 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____22577 FStar_Syntax_Util.Equal))
in (match (uu____22576) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____22580 -> begin
(

let uu____22581 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_65 -> FStar_Pervasives_Native.Some (_0_65)) uu____22581))
end))
in (

let uu____22584 = (solve_prob orig guard [] wl)
in (solve env uu____22584)))
end
| uu____22585 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____22586 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____22587, FStar_Syntax_Syntax.Tm_fvar (uu____22588)) -> begin
(

let head1 = (

let uu____22592 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22592 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22636 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22636 FStar_Pervasives_Native.fst))
in ((

let uu____22678 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____22678) with
| true -> begin
(

let uu____22679 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22680 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22681 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22679 uu____22680 uu____22681))))
end
| uu____22682 -> begin
()
end));
(

let uu____22683 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____22683) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____22698 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____22698) with
| true -> begin
(

let guard = (

let uu____22710 = (

let uu____22711 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____22711 FStar_Syntax_Util.Equal))
in (match (uu____22710) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____22714 -> begin
(

let uu____22715 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_66 -> FStar_Pervasives_Native.Some (_0_66)) uu____22715))
end))
in (

let uu____22718 = (solve_prob orig guard [] wl)
in (solve env uu____22718)))
end
| uu____22719 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____22720 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____22721, FStar_Syntax_Syntax.Tm_app (uu____22722)) -> begin
(

let head1 = (

let uu____22740 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____22740 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____22784 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____22784 FStar_Pervasives_Native.fst))
in ((

let uu____22826 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____22826) with
| true -> begin
(

let uu____22827 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____22828 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____22829 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____22827 uu____22828 uu____22829))))
end
| uu____22830 -> begin
()
end));
(

let uu____22831 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____22831) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____22846 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____22846) with
| true -> begin
(

let guard = (

let uu____22858 = (

let uu____22859 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____22859 FStar_Syntax_Util.Equal))
in (match (uu____22858) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____22862 -> begin
(

let uu____22863 = (mk_eq2 orig t1 t2)
in (FStar_All.pipe_left (fun _0_67 -> FStar_Pervasives_Native.Some (_0_67)) uu____22863))
end))
in (

let uu____22866 = (solve_prob orig guard [] wl)
in (solve env uu____22866)))
end
| uu____22867 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____22868 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_let (uu____22869), FStar_Syntax_Syntax.Tm_let (uu____22870)) -> begin
(

let uu____22895 = (FStar_Syntax_Util.term_eq t1 t2)
in (match (uu____22895) with
| true -> begin
(

let uu____22896 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____22896))
end
| uu____22897 -> begin
(giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig)
end))
end
| (FStar_Syntax_Syntax.Tm_let (uu____22898), uu____22899) -> begin
(

let uu____22912 = (

let uu____22917 = (

let uu____22918 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____22919 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____22920 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____22921 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)" uu____22918 uu____22919 uu____22920 uu____22921)))))
in ((FStar_Errors.Fatal_UnificationNotWellFormed), (uu____22917)))
in (FStar_Errors.raise_error uu____22912 t1.FStar_Syntax_Syntax.pos))
end
| (uu____22922, FStar_Syntax_Syntax.Tm_let (uu____22923)) -> begin
(

let uu____22936 = (

let uu____22941 = (

let uu____22942 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____22943 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____22944 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____22945 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)" uu____22942 uu____22943 uu____22944 uu____22945)))))
in ((FStar_Errors.Fatal_UnificationNotWellFormed), (uu____22941)))
in (FStar_Errors.raise_error uu____22936 t1.FStar_Syntax_Syntax.pos))
end
| uu____22946 -> begin
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

let uu____22982 = (p_scope orig)
in (mk_problem uu____22982 orig t1 rel t2 FStar_Pervasives_Native.None reason)))
in (

let solve_eq = (fun c1_comp c2_comp -> ((

let uu____22995 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____22995) with
| true -> begin
(

let uu____22996 = (

let uu____22997 = (FStar_Syntax_Syntax.mk_Comp c1_comp)
in (FStar_Syntax_Print.comp_to_string uu____22997))
in (

let uu____22998 = (

let uu____22999 = (FStar_Syntax_Syntax.mk_Comp c2_comp)
in (FStar_Syntax_Print.comp_to_string uu____22999))
in (FStar_Util.print2 "solve_c is using an equality constraint (%s vs %s)\n" uu____22996 uu____22998)))
end
| uu____23000 -> begin
()
end));
(

let uu____23001 = (

let uu____23002 = (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)
in (not (uu____23002)))
in (match (uu____23001) with
| true -> begin
(

let uu____23003 = (

let uu____23004 = (FStar_Syntax_Print.lid_to_string c1_comp.FStar_Syntax_Syntax.effect_name)
in (

let uu____23005 = (FStar_Syntax_Print.lid_to_string c2_comp.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible effects: %s <> %s" uu____23004 uu____23005)))
in (giveup env uu____23003 orig))
end
| uu____23006 -> begin
(

let ret_sub_prob = (

let uu____23008 = (sub_prob c1_comp.FStar_Syntax_Syntax.result_typ FStar_TypeChecker_Common.EQ c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type")
in (FStar_All.pipe_left (fun _0_68 -> FStar_TypeChecker_Common.TProb (_0_68)) uu____23008))
in (

let arg_sub_probs = (FStar_List.map2 (fun uu____23035 uu____23036 -> (match (((uu____23035), (uu____23036))) with
| ((a1, uu____23054), (a2, uu____23056)) -> begin
(

let uu____23065 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _0_69 -> FStar_TypeChecker_Common.TProb (_0_69)) uu____23065))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let sub_probs = (ret_sub_prob)::arg_sub_probs
in (

let guard = (

let uu____23078 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) FStar_Pervasives_Native.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____23078))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))))))
end));
))
in (

let solve_sub = (fun c11 edge c21 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let lift_c1 = (fun uu____23110 -> (

let wp = (match (c11.FStar_Syntax_Syntax.effect_args) with
| ((wp1, uu____23117))::[] -> begin
wp1
end
| uu____23134 -> begin
(

let uu____23143 = (

let uu____23144 = (

let uu____23145 = (FStar_Ident.range_of_lid c11.FStar_Syntax_Syntax.effect_name)
in (FStar_Range.string_of_range uu____23145))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" uu____23144))
in (failwith uu____23143))
end)
in (

let univs1 = (match (c11.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
(

let uu____23153 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (uu____23153)::[])
end
| x -> begin
x
end)
in (

let uu____23155 = (

let uu____23164 = (

let uu____23165 = (

let uu____23166 = (FStar_List.hd univs1)
in (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp uu____23166 c11.FStar_Syntax_Syntax.result_typ wp))
in (FStar_Syntax_Syntax.as_arg uu____23165))
in (uu____23164)::[])
in {FStar_Syntax_Syntax.comp_univs = univs1; FStar_Syntax_Syntax.effect_name = c21.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c11.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____23155; FStar_Syntax_Syntax.flags = c11.FStar_Syntax_Syntax.flags}))))
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____23167 = (lift_c1 ())
in (solve_eq uu____23167 c21))
end
| uu____23168 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___120_23173 -> (match (uu___120_23173) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| uu____23174 -> begin
false
end))))
in (

let uu____23175 = (match (((c11.FStar_Syntax_Syntax.effect_args), (c21.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____23209))::uu____23210, ((wp2, uu____23212))::uu____23213) -> begin
((wp1), (wp2))
end
| uu____23270 -> begin
(

let uu____23291 = (

let uu____23296 = (

let uu____23297 = (FStar_Syntax_Print.lid_to_string c11.FStar_Syntax_Syntax.effect_name)
in (

let uu____23298 = (FStar_Syntax_Print.lid_to_string c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____23297 uu____23298)))
in ((FStar_Errors.Fatal_ExpectNormalizedEffect), (uu____23296)))
in (FStar_Errors.raise_error uu____23291 env.FStar_TypeChecker_Env.range))
end)
in (match (uu____23175) with
| (wpc1, wpc2) -> begin
(

let uu____23317 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____23317) with
| true -> begin
(

let uu____23320 = (problem_using_guard orig c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ FStar_Pervasives_Native.None "result type")
in (solve_t env uu____23320 wl))
end
| uu____23323 -> begin
(

let uu____23324 = (

let uu____23331 = (FStar_TypeChecker_Env.effect_decl_opt env c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.must uu____23331))
in (match (uu____23324) with
| (c2_decl, qualifiers) -> begin
(

let uu____23352 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____23352) with
| true -> begin
(

let c1_repr = (

let uu____23356 = (

let uu____23357 = (

let uu____23358 = (lift_c1 ())
in (FStar_Syntax_Syntax.mk_Comp uu____23358))
in (

let uu____23359 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____23357 uu____23359)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env uu____23356))
in (

let c2_repr = (

let uu____23361 = (

let uu____23362 = (FStar_Syntax_Syntax.mk_Comp c21)
in (

let uu____23363 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____23362 uu____23363)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env uu____23361))
in (

let prob = (

let uu____23365 = (

let uu____23370 = (

let uu____23371 = (FStar_Syntax_Print.term_to_string c1_repr)
in (

let uu____23372 = (FStar_Syntax_Print.term_to_string c2_repr)
in (FStar_Util.format2 "sub effect repr: %s <: %s" uu____23371 uu____23372)))
in (sub_prob c1_repr problem.FStar_TypeChecker_Common.relation c2_repr uu____23370))
in FStar_TypeChecker_Common.TProb (uu____23365))
in (

let wl1 = (

let uu____23374 = (

let uu____23377 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in FStar_Pervasives_Native.Some (uu____23377))
in (solve_prob orig uu____23374 [] wl))
in (solve env (attempt ((prob)::[]) wl1))))))
end
| uu____23382 -> begin
(

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____23384 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____23386 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____23386) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____23387 -> begin
()
end));
(

let c1_univ = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____23389 = (

let uu____23396 = (

let uu____23397 = (

let uu____23412 = (FStar_TypeChecker_Env.inst_effect_fun_with ((c1_univ)::[]) env c2_decl c2_decl.FStar_Syntax_Syntax.trivial)
in (

let uu____23413 = (

let uu____23416 = (FStar_Syntax_Syntax.as_arg c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____23417 = (

let uu____23420 = (

let uu____23421 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c1_univ c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____23421))
in (uu____23420)::[])
in (uu____23416)::uu____23417))
in ((uu____23412), (uu____23413))))
in FStar_Syntax_Syntax.Tm_app (uu____23397))
in (FStar_Syntax_Syntax.mk uu____23396))
in (uu____23389 FStar_Pervasives_Native.None r)));
)
end
| uu____23427 -> begin
(

let c1_univ = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (

let c2_univ = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____23430 = (

let uu____23437 = (

let uu____23438 = (

let uu____23453 = (FStar_TypeChecker_Env.inst_effect_fun_with ((c2_univ)::[]) env c2_decl c2_decl.FStar_Syntax_Syntax.stronger)
in (

let uu____23454 = (

let uu____23457 = (FStar_Syntax_Syntax.as_arg c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____23458 = (

let uu____23461 = (FStar_Syntax_Syntax.as_arg wpc2)
in (

let uu____23462 = (

let uu____23465 = (

let uu____23466 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c1_univ c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____23466))
in (uu____23465)::[])
in (uu____23461)::uu____23462))
in (uu____23457)::uu____23458))
in ((uu____23453), (uu____23454))))
in FStar_Syntax_Syntax.Tm_app (uu____23438))
in (FStar_Syntax_Syntax.mk uu____23437))
in (uu____23430 FStar_Pervasives_Native.None r))))
end)
end)
in (

let base_prob = (

let uu____23473 = (sub_prob c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _0_70 -> FStar_TypeChecker_Common.TProb (_0_70)) uu____23473))
in (

let wl1 = (

let uu____23483 = (

let uu____23486 = (

let uu____23489 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____23489 g))
in (FStar_All.pipe_left (fun _0_71 -> FStar_Pervasives_Native.Some (_0_71)) uu____23486))
in (solve_prob orig uu____23483 [] wl))
in (solve env (attempt ((base_prob)::[]) wl1)))))
end))
end))
end))
end)))
end))))
in (

let uu____23502 = (FStar_Util.physical_equality c1 c2)
in (match (uu____23502) with
| true -> begin
(

let uu____23503 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____23503))
end
| uu____23504 -> begin
((

let uu____23506 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____23506) with
| true -> begin
(

let uu____23507 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____23508 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____23507 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____23508)))
end
| uu____23509 -> begin
()
end));
(

let uu____23510 = (

let uu____23515 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____23516 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____23515), (uu____23516))))
in (match (uu____23510) with
| (c11, c21) -> begin
(match (((c11.FStar_Syntax_Syntax.n), (c21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____23520), FStar_Syntax_Syntax.Total (t2, uu____23522)) when (FStar_Syntax_Util.non_informative t2) -> begin
(

let uu____23539 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____23539 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____23542), FStar_Syntax_Syntax.Total (uu____23543)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| (FStar_Syntax_Syntax.Total (t1, uu____23561), FStar_Syntax_Syntax.Total (t2, uu____23563)) -> begin
(

let uu____23580 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____23580 wl))
end
| (FStar_Syntax_Syntax.GTotal (t1, uu____23584), FStar_Syntax_Syntax.GTotal (t2, uu____23586)) -> begin
(

let uu____23603 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____23603 wl))
end
| (FStar_Syntax_Syntax.Total (t1, uu____23607), FStar_Syntax_Syntax.GTotal (t2, uu____23609)) -> begin
(

let uu____23626 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____23626 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____23629), FStar_Syntax_Syntax.Comp (uu____23630)) -> begin
(

let uu____23639 = (

let uu___171_23644 = problem
in (

let uu____23649 = (

let uu____23650 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____23650))
in {FStar_TypeChecker_Common.pid = uu___171_23644.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____23649; FStar_TypeChecker_Common.relation = uu___171_23644.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___171_23644.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___171_23644.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___171_23644.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___171_23644.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___171_23644.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___171_23644.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___171_23644.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____23639 wl))
end
| (FStar_Syntax_Syntax.Total (uu____23651), FStar_Syntax_Syntax.Comp (uu____23652)) -> begin
(

let uu____23661 = (

let uu___171_23666 = problem
in (

let uu____23671 = (

let uu____23672 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____23672))
in {FStar_TypeChecker_Common.pid = uu___171_23666.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____23671; FStar_TypeChecker_Common.relation = uu___171_23666.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___171_23666.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___171_23666.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___171_23666.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___171_23666.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___171_23666.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___171_23666.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___171_23666.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____23661 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____23673), FStar_Syntax_Syntax.GTotal (uu____23674)) -> begin
(

let uu____23683 = (

let uu___172_23688 = problem
in (

let uu____23693 = (

let uu____23694 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____23694))
in {FStar_TypeChecker_Common.pid = uu___172_23688.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___172_23688.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___172_23688.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____23693; FStar_TypeChecker_Common.element = uu___172_23688.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___172_23688.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___172_23688.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___172_23688.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___172_23688.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___172_23688.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____23683 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____23695), FStar_Syntax_Syntax.Total (uu____23696)) -> begin
(

let uu____23705 = (

let uu___172_23710 = problem
in (

let uu____23715 = (

let uu____23716 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____23716))
in {FStar_TypeChecker_Common.pid = uu___172_23710.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___172_23710.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___172_23710.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____23715; FStar_TypeChecker_Common.element = uu___172_23710.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___172_23710.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___172_23710.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___172_23710.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___172_23710.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___172_23710.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____23705 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____23717), FStar_Syntax_Syntax.Comp (uu____23718)) -> begin
(

let uu____23719 = ((((FStar_Syntax_Util.is_ml_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) || ((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_total_comp c21))) || (((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB)))
in (match (uu____23719) with
| true -> begin
(

let uu____23720 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c11) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c21) FStar_Pervasives_Native.None "result type")
in (solve_t env uu____23720 wl))
end
| uu____23723 -> begin
(

let c1_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (

let c2_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____23726 = (

let uu____23731 = (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)
in (match (uu____23731) with
| true -> begin
((c1_comp), (c2_comp))
end
| uu____23736 -> begin
(

let uu____23737 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let uu____23738 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((uu____23737), (uu____23738))))
end))
in (match (uu____23726) with
| (c1_comp1, c2_comp1) -> begin
(solve_eq c1_comp1 c2_comp1)
end))
end
| uu____23741 -> begin
(

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((

let uu____23745 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____23745) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c12.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c22.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____23746 -> begin
()
end));
(

let uu____23747 = (FStar_TypeChecker_Env.monad_leq env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____23747) with
| FStar_Pervasives_Native.None -> begin
(

let uu____23750 = (

let uu____23751 = (FStar_Syntax_Print.lid_to_string c12.FStar_Syntax_Syntax.effect_name)
in (

let uu____23752 = (FStar_Syntax_Print.lid_to_string c22.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____23751 uu____23752)))
in (giveup env uu____23750 orig))
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

let uu____23759 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____23797 -> (match (uu____23797) with
| (uu____23810, uu____23811, u, uu____23813, uu____23814, uu____23815) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____23759 (FStar_String.concat ", "))))


let ineqs_to_string : (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.string = (fun ineqs -> (

let vars = (

let uu____23848 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs) (FStar_List.map FStar_Syntax_Print.univ_to_string))
in (FStar_All.pipe_right uu____23848 (FStar_String.concat ", ")))
in (

let ineqs1 = (

let uu____23866 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs) (FStar_List.map (fun uu____23894 -> (match (uu____23894) with
| (u1, u2) -> begin
(

let uu____23901 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____23902 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "%s < %s" uu____23901 uu____23902)))
end))))
in (FStar_All.pipe_right uu____23866 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred), (g.FStar_TypeChecker_Env.univ_ineqs))) with
| (FStar_TypeChecker_Common.Trivial, [], (uu____23923, [])) -> begin
"{}"
end
| uu____23948 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____23965 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____23965) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____23966 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____23968 = (FStar_List.map (fun uu____23978 -> (match (uu____23978) with
| (uu____23983, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right uu____23968 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (

let uu____23988 = (ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs)
in (FStar_Util.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n" form carry uu____23988 imps)))))
end))


let new_t_problem : 'Auu____24003 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  'Auu____24003 FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term, 'Auu____24003) FStar_TypeChecker_Common.problem = (fun env lhs rel rhs elt loc -> (

let reason = (

let uu____24043 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____24043) with
| true -> begin
(

let uu____24044 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____24045 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____24044 (rel_to_string rel) uu____24045)))
end
| uu____24046 -> begin
"TOP"
end))
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (

let uu____24077 = (

let uu____24080 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_72 -> FStar_Pervasives_Native.Some (_0_72)) uu____24080))
in (FStar_Syntax_Syntax.new_bv uu____24077 t1))
in (

let env1 = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (

let uu____24089 = (

let uu____24092 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _0_73 -> FStar_Pervasives_Native.Some (_0_73)) uu____24092))
in (

let uu____24095 = (FStar_TypeChecker_Env.get_range env1)
in (new_t_problem env1 t1 rel t2 uu____24089 uu____24095)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option = (fun env probs err -> (

let probs1 = (

let uu____24131 = (FStar_Options.eager_inference ())
in (match (uu____24131) with
| true -> begin
(

let uu___173_24132 = probs
in {attempting = uu___173_24132.attempting; wl_deferred = uu___173_24132.wl_deferred; ctr = uu___173_24132.ctr; defer_ok = false; smt_ok = uu___173_24132.smt_ok; tcenv = uu___173_24132.tcenv})
end
| uu____24133 -> begin
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

let uu____24143 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____24143) with
| true -> begin
(

let uu____24144 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____24144))
end
| uu____24145 -> begin
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

let uu____24162 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____24162) with
| true -> begin
(

let uu____24163 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____24163))
end
| uu____24164 -> begin
()
end));
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env f)
in ((

let uu____24167 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____24167) with
| true -> begin
(

let uu____24168 = (FStar_Syntax_Print.term_to_string f1)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____24168))
end
| uu____24169 -> begin
()
end));
(

let f2 = (

let uu____24171 = (

let uu____24172 = (FStar_Syntax_Util.unmeta f1)
in uu____24172.FStar_Syntax_Syntax.n)
in (match (uu____24171) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____24176 -> begin
FStar_TypeChecker_Common.NonTrivial (f1)
end))
in (

let uu___174_24177 = g
in {FStar_TypeChecker_Env.guard_f = f2; FStar_TypeChecker_Env.deferred = uu___174_24177.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___174_24177.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___174_24177.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____24202 = (

let uu____24203 = (

let uu____24204 = (

let uu____24205 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____24205 (fun _0_74 -> FStar_TypeChecker_Common.NonTrivial (_0_74))))
in {FStar_TypeChecker_Env.guard_f = uu____24204; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env uu____24203))
in (FStar_All.pipe_left (fun _0_75 -> FStar_Pervasives_Native.Some (_0_75)) uu____24202))
end))


let with_guard_no_simp : 'Auu____24236 . 'Auu____24236  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____24259 = (

let uu____24260 = (

let uu____24261 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____24261 (fun _0_76 -> FStar_TypeChecker_Common.NonTrivial (_0_76))))
in {FStar_TypeChecker_Env.guard_f = uu____24260; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in FStar_Pervasives_Native.Some (uu____24259))
end))


let try_teq : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun smt_ok env t1 t2 -> ((

let uu____24307 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____24307) with
| true -> begin
(

let uu____24308 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____24309 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" uu____24308 uu____24309)))
end
| uu____24310 -> begin
()
end));
(

let prob = (

let uu____24312 = (

let uu____24317 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None uu____24317))
in (FStar_All.pipe_left (fun _0_77 -> FStar_TypeChecker_Common.TProb (_0_77)) uu____24312))
in (

let g = (

let uu____24325 = (

let uu____24328 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____24328 (fun uu____24330 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____24325))
in g));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____24354 = (try_teq true env t1 t2)
in (match (uu____24354) with
| FStar_Pervasives_Native.None -> begin
((

let uu____24358 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____24359 = (FStar_TypeChecker_Err.basic_type_error env FStar_Pervasives_Native.None t2 t1)
in (FStar_Errors.log_issue uu____24358 uu____24359)));
trivial_guard;
)
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____24366 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____24366) with
| true -> begin
(

let uu____24367 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____24368 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____24369 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____24367 uu____24368 uu____24369))))
end
| uu____24370 -> begin
()
end));
g;
)
end)))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun env e t1 t2 -> (

let uu____24391 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____24392 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t2 t1)
in (FStar_Errors.log_issue uu____24391 uu____24392))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env c1 c2 -> (

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____24415 -> begin
FStar_TypeChecker_Common.SUB
end)
in ((

let uu____24417 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____24417) with
| true -> begin
(

let uu____24418 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____24419 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n" uu____24418 uu____24419 (match ((Prims.op_Equality rel FStar_TypeChecker_Common.EQ)) with
| true -> begin
"EQ"
end
| uu____24420 -> begin
"SUB"
end))))
end
| uu____24421 -> begin
()
end));
(

let prob = (

let uu____24423 = (

let uu____24428 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 FStar_Pervasives_Native.None uu____24428 "sub_comp"))
in (FStar_All.pipe_left (fun _0_78 -> FStar_TypeChecker_Common.CProb (_0_78)) uu____24423))
in (

let uu____24433 = (

let uu____24436 = (singleton env prob)
in (solve_and_commit env uu____24436 (fun uu____24438 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____24433)));
)))


let solve_universe_inequalities' : FStar_Syntax_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  unit = (fun tx env uu____24473 -> (match (uu____24473) with
| (variables, ineqs) -> begin
(

let fail1 = (fun u1 u2 -> ((FStar_Syntax_Unionfind.rollback tx);
(

let uu____24516 = (

let uu____24521 = (

let uu____24522 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____24523 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Universe %s and %s are incompatible" uu____24522 uu____24523)))
in ((FStar_Errors.Fatal_IncompatibleUniverse), (uu____24521)))
in (

let uu____24524 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____24516 uu____24524)));
))
in (

let equiv1 = (fun v1 v' -> (

let uu____24536 = (

let uu____24541 = (FStar_Syntax_Subst.compress_univ v1)
in (

let uu____24542 = (FStar_Syntax_Subst.compress_univ v')
in ((uu____24541), (uu____24542))))
in (match (uu____24536) with
| (FStar_Syntax_Syntax.U_unif (v0), FStar_Syntax_Syntax.U_unif (v0')) -> begin
(FStar_Syntax_Unionfind.univ_equiv v0 v0')
end
| uu____24561 -> begin
false
end)))
in (

let sols = (FStar_All.pipe_right variables (FStar_List.collect (fun v1 -> (

let uu____24591 = (FStar_Syntax_Subst.compress_univ v1)
in (match (uu____24591) with
| FStar_Syntax_Syntax.U_unif (uu____24598) -> begin
(

let lower_bounds_of_v = (FStar_All.pipe_right ineqs (FStar_List.collect (fun uu____24627 -> (match (uu____24627) with
| (u, v') -> begin
(

let uu____24636 = (equiv1 v1 v')
in (match (uu____24636) with
| true -> begin
(

let uu____24639 = (FStar_All.pipe_right variables (FStar_Util.for_some (equiv1 u)))
in (match (uu____24639) with
| true -> begin
[]
end
| uu____24644 -> begin
(u)::[]
end))
end
| uu____24645 -> begin
[]
end))
end))))
in (

let lb = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max (lower_bounds_of_v)))
in (((lb), (v1)))::[]))
end
| uu____24655 -> begin
[]
end)))))
in (

let uu____24660 = (

let wl = (

let uu___175_24664 = (empty_worklist env)
in {attempting = uu___175_24664.attempting; wl_deferred = uu___175_24664.wl_deferred; ctr = uu___175_24664.ctr; defer_ok = false; smt_ok = uu___175_24664.smt_ok; tcenv = uu___175_24664.tcenv})
in (FStar_All.pipe_right sols (FStar_List.map (fun uu____24682 -> (match (uu____24682) with
| (lb, v1) -> begin
(

let uu____24689 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl lb v1)
in (match (uu____24689) with
| USolved (wl1) -> begin
()
end
| uu____24691 -> begin
(fail1 lb v1)
end))
end)))))
in (

let rec check_ineq = (fun uu____24701 -> (match (uu____24701) with
| (u, v1) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u)
in (

let v2 = (FStar_TypeChecker_Normalize.normalize_universe env v1)
in (match (((u1), (v2))) with
| (FStar_Syntax_Syntax.U_zero, uu____24710) -> begin
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
| (FStar_Syntax_Syntax.U_name (uu____24733), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_unif (uu____24735), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_max (us), uu____24746) -> begin
(FStar_All.pipe_right us (FStar_Util.for_all (fun u2 -> (check_ineq ((u2), (v2))))))
end
| (uu____24753, FStar_Syntax_Syntax.U_max (vs)) -> begin
(FStar_All.pipe_right vs (FStar_Util.for_some (fun v3 -> (check_ineq ((u1), (v3))))))
end
| uu____24761 -> begin
false
end)))
end))
in (

let uu____24766 = (FStar_All.pipe_right ineqs (FStar_Util.for_all (fun uu____24781 -> (match (uu____24781) with
| (u, v1) -> begin
(

let uu____24788 = (check_ineq ((u), (v1)))
in (match (uu____24788) with
| true -> begin
true
end
| uu____24789 -> begin
((

let uu____24791 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____24791) with
| true -> begin
(

let uu____24792 = (FStar_Syntax_Print.univ_to_string u)
in (

let uu____24793 = (FStar_Syntax_Print.univ_to_string v1)
in (FStar_Util.print2 "%s </= %s" uu____24792 uu____24793)))
end
| uu____24794 -> begin
()
end));
false;
)
end))
end))))
in (match (uu____24766) with
| true -> begin
()
end
| uu____24795 -> begin
((

let uu____24797 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____24797) with
| true -> begin
((

let uu____24799 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Partially solved inequality constraints are: %s\n" uu____24799));
(FStar_Syntax_Unionfind.rollback tx);
(

let uu____24809 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Original solved inequality constraints are: %s\n" uu____24809));
)
end
| uu____24818 -> begin
()
end));
(

let uu____24819 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_FailToSolveUniverseInEquality), ("Failed to solve universe inequalities for inductives")) uu____24819));
)
end)))))))
end))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  unit = (fun env ineqs -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Syntax_Unionfind.commit tx);
)))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail1 = (fun uu____24877 -> (match (uu____24877) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ErrorInSolveDeferredConstraints), (msg)) (p_loc d)))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in ((

let uu____24891 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____24891) with
| true -> begin
(

let uu____24892 = (wl_to_string wl)
in (

let uu____24893 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" uu____24892 uu____24893)))
end
| uu____24906 -> begin
()
end));
(

let g1 = (

let uu____24908 = (solve_and_commit env wl fail1)
in (match (uu____24908) with
| FStar_Pervasives_Native.Some ([]) -> begin
(

let uu___176_24921 = g
in {FStar_TypeChecker_Env.guard_f = uu___176_24921.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu___176_24921.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___176_24921.FStar_TypeChecker_Env.implicits})
end
| uu____24926 -> begin
(failwith "impossible: Unexpected deferred constraints remain")
end))
in ((solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___177_24930 = g1
in {FStar_TypeChecker_Env.guard_f = uu___177_24930.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___177_24930.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = uu___177_24930.FStar_TypeChecker_Env.implicits});
));
))))


let last_proof_ns : FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let maybe_update_proof_ns : FStar_TypeChecker_Env.env  ->  unit = (fun env -> (

let pns = env.FStar_TypeChecker_Env.proof_ns
in (

let uu____24982 = (FStar_ST.op_Bang last_proof_ns)
in (match (uu____24982) with
| FStar_Pervasives_Native.None -> begin
(FStar_ST.op_Colon_Equals last_proof_ns (FStar_Pervasives_Native.Some (pns)))
end
| FStar_Pervasives_Native.Some (old) -> begin
(match ((Prims.op_Equality old pns)) with
| true -> begin
()
end
| uu____25052 -> begin
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

let uu___178_25123 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___178_25123.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___178_25123.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___178_25123.FStar_TypeChecker_Env.implicits})
in (

let uu____25124 = (

let uu____25125 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____25125)))
in (match (uu____25124) with
| true -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| uu____25128 -> begin
(match (g1.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((match (debug1) with
| true -> begin
(

let uu____25133 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____25134 = (

let uu____25135 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____25135))
in (FStar_Errors.diag uu____25133 uu____25134)))
end
| uu____25136 -> begin
()
end);
(

let vc1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env vc)
in ((match (debug1) with
| true -> begin
(

let uu____25139 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____25140 = (

let uu____25141 = (FStar_Syntax_Print.term_to_string vc1)
in (FStar_Util.format1 "After normalization VC=\n%s\n" uu____25141))
in (FStar_Errors.diag uu____25139 uu____25140)))
end
| uu____25142 -> begin
()
end);
(

let uu____25144 = (FStar_TypeChecker_Env.get_range env)
in (def_check_closed_in_env uu____25144 "discharge_guard\'" env vc1));
(

let uu____25145 = (check_trivial vc1)
in (match (uu____25145) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc2) -> begin
(match ((not (use_smt))) with
| true -> begin
((match (debug1) with
| true -> begin
(

let uu____25152 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____25153 = (

let uu____25154 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Cannot solve without SMT : %s\n" uu____25154))
in (FStar_Errors.diag uu____25152 uu____25153)))
end
| uu____25155 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end
| uu____25156 -> begin
((match (debug1) with
| true -> begin
(

let uu____25159 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____25160 = (

let uu____25161 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____25161))
in (FStar_Errors.diag uu____25159 uu____25160)))
end
| uu____25162 -> begin
()
end);
(

let vcs = (

let uu____25172 = (FStar_Options.use_tactics ())
in (match (uu____25172) with
| true -> begin
(FStar_Options.with_saved_options (fun uu____25192 -> ((

let uu____25194 = (FStar_Options.set_options FStar_Options.Set "--no_tactics")
in (FStar_All.pipe_left (fun a239 -> ()) uu____25194));
(

let vcs = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.preprocess env vc2)
in (FStar_All.pipe_right vcs (FStar_List.map (fun uu____25237 -> (match (uu____25237) with
| (env1, goal, opts) -> begin
(

let uu____25253 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env1 goal)
in ((env1), (uu____25253), (opts)))
end)))));
)))
end
| uu____25254 -> begin
(

let uu____25255 = (

let uu____25262 = (FStar_Options.peek ())
in ((env), (vc2), (uu____25262)))
in (uu____25255)::[])
end))
in (FStar_All.pipe_right vcs (FStar_List.iter (fun uu____25295 -> (match (uu____25295) with
| (env1, goal, opts) -> begin
(

let uu____25305 = (check_trivial goal)
in (match (uu____25305) with
| FStar_TypeChecker_Common.Trivial -> begin
(match (debug1) with
| true -> begin
(FStar_Util.print_string "Goal completely solved by tactic\n")
end
| uu____25307 -> begin
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

let uu____25313 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____25314 = (

let uu____25315 = (FStar_Syntax_Print.term_to_string goal1)
in (

let uu____25316 = (FStar_TypeChecker_Env.string_of_proof_ns env1)
in (FStar_Util.format2 "Trying to solve:\n> %s\nWith proof_ns:\n %s\n" uu____25315 uu____25316)))
in (FStar_Errors.diag uu____25313 uu____25314)))
end
| uu____25317 -> begin
()
end);
(match (debug1) with
| true -> begin
(

let uu____25319 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____25320 = (

let uu____25321 = (FStar_Syntax_Print.term_to_string goal1)
in (FStar_Util.format1 "Before calling solver VC=\n%s\n" uu____25321))
in (FStar_Errors.diag uu____25319 uu____25320)))
end
| uu____25322 -> begin
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

let uu____25335 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____25335) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____25342 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ExpectTrivialPreCondition), ("Expected a trivial pre-condition")) uu____25342))
end)))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let uu____25353 = (discharge_guard' FStar_Pervasives_Native.None env g true)
in (match (uu____25353) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end)))


let resolve_implicits' : Prims.bool  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun must_total forcelax g -> (

let unresolved = (fun u -> (

let uu____25381 = (FStar_Syntax_Unionfind.find u)
in (match (uu____25381) with
| FStar_Pervasives_Native.None -> begin
true
end
| uu____25384 -> begin
false
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____25406 = acc
in (match (uu____25406) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____25425 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd1)::tl1 -> begin
(

let uu____25492 = hd1
in (match (uu____25492) with
| (uu____25505, env, u, tm, k, r) -> begin
(

let uu____25511 = (unresolved u)
in (match (uu____25511) with
| true -> begin
(until_fixpoint (((hd1)::out), (changed)) tl1)
end
| uu____25538 -> begin
(

let tm1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (

let env1 = (match (forcelax) with
| true -> begin
(

let uu___179_25541 = env
in {FStar_TypeChecker_Env.solver = uu___179_25541.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___179_25541.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___179_25541.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___179_25541.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___179_25541.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___179_25541.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___179_25541.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___179_25541.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___179_25541.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___179_25541.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___179_25541.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___179_25541.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___179_25541.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___179_25541.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___179_25541.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___179_25541.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___179_25541.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___179_25541.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___179_25541.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___179_25541.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___179_25541.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___179_25541.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___179_25541.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___179_25541.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___179_25541.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___179_25541.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___179_25541.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___179_25541.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___179_25541.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___179_25541.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___179_25541.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___179_25541.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___179_25541.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___179_25541.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___179_25541.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___179_25541.FStar_TypeChecker_Env.dep_graph})
end
| uu____25542 -> begin
env
end)
in ((

let uu____25544 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("RelCheck")))
in (match (uu____25544) with
| true -> begin
(

let uu____25545 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____25546 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____25547 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" uu____25545 uu____25546 uu____25547))))
end
| uu____25548 -> begin
()
end));
(

let g1 = (FStar_All.try_with (fun uu___181_25551 -> (match (()) with
| () -> begin
(env1.FStar_TypeChecker_Env.check_type_of must_total env1 tm1 k)
end)) (fun uu___180_25555 -> (match (uu___180_25555) with
| e -> begin
((

let uu____25558 = (

let uu____25567 = (

let uu____25574 = (

let uu____25575 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____25576 = (FStar_TypeChecker_Normalize.term_to_string env1 tm1)
in (FStar_Util.format2 "Failed while checking implicit %s set to %s" uu____25575 uu____25576)))
in ((FStar_Errors.Error_BadImplicit), (uu____25574), (r)))
in (uu____25567)::[])
in (FStar_Errors.add_errors uu____25558));
(FStar_Exn.raise e);
)
end)))
in (

let g2 = (match (env1.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___182_25590 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___182_25590.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___182_25590.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___182_25590.FStar_TypeChecker_Env.implicits})
end
| uu____25591 -> begin
g1
end)
in (

let g' = (

let uu____25593 = (discharge_guard' (FStar_Pervasives_Native.Some ((fun uu____25600 -> (FStar_Syntax_Print.term_to_string tm1)))) env1 g2 true)
in (match (uu____25593) with
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

let uu___183_25628 = g
in (

let uu____25629 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___183_25628.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___183_25628.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___183_25628.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____25629})))))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (resolve_implicits' true false g))


let resolve_implicits_tac : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (resolve_implicits' false true g))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  unit = (fun env g -> (

let g1 = (

let uu____25691 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____25691 resolve_implicits))
in (match (g1.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(

let uu____25704 = (discharge_guard env g1)
in (FStar_All.pipe_left (fun a240 -> ()) uu____25704))
end
| ((reason, uu____25706, uu____25707, e, t, r))::uu____25711 -> begin
(

let uu____25738 = (

let uu____25743 = (

let uu____25744 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____25745 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Failed to resolve implicit argument of type \'%s\' introduced in %s" uu____25744 uu____25745)))
in ((FStar_Errors.Fatal_FailToResolveImplicitArgument), (uu____25743)))
in (FStar_Errors.raise_error uu____25738 r))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___184_25756 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___184_25756.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___184_25756.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ((((u1), (u2)))::[])); FStar_TypeChecker_Env.implicits = uu___184_25756.FStar_TypeChecker_Env.implicits}))


let discharge_guard_nosmt : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun env g -> (

let uu____25783 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____25783) with
| FStar_Pervasives_Native.Some (uu____25789) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end)))


let teq_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____25805 = (try_teq false env t1 t2)
in (match (uu____25805) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g) -> begin
(discharge_guard_nosmt env g)
end)))


let check_subtyping : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.option = (fun env t1 t2 -> ((

let uu____25831 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____25831) with
| true -> begin
(

let uu____25832 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____25833 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "check_subtyping of %s and %s\n" uu____25832 uu____25833)))
end
| uu____25834 -> begin
()
end));
(

let uu____25835 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____25835) with
| (prob, x) -> begin
(

let g = (

let uu____25851 = (

let uu____25854 = (singleton' env prob true)
in (solve_and_commit env uu____25854 (fun uu____25856 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____25851))
in ((

let uu____25866 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____25866) with
| true -> begin
(

let uu____25867 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____25868 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____25869 = (

let uu____25870 = (FStar_Util.must g)
in (guard_to_string env uu____25870))
in (FStar_Util.print3 "check_subtyping succeeded: %s <: %s\n\tguard is %s\n" uu____25867 uu____25868 uu____25869))))
end
| uu____25871 -> begin
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

let uu____25904 = (check_subtyping env t1 t2)
in (match (uu____25904) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (x, g) -> begin
(

let uu____25923 = (

let uu____25924 = (FStar_Syntax_Syntax.mk_binder x)
in (abstract_guard uu____25924 g))
in FStar_Pervasives_Native.Some (uu____25923))
end)))


let get_subtyping_prop : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> (

let uu____25942 = (check_subtyping env t1 t2)
in (match (uu____25942) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (x, g) -> begin
(

let uu____25961 = (

let uu____25962 = (

let uu____25963 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____25963)::[])
in (close_guard env uu____25962 g))
in FStar_Pervasives_Native.Some (uu____25961))
end)))


let subtype_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> ((

let uu____25980 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____25980) with
| true -> begin
(

let uu____25981 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____25982 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____25981 uu____25982)))
end
| uu____25983 -> begin
()
end));
(

let uu____25984 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____25984) with
| (prob, x) -> begin
(

let g = (

let uu____25994 = (

let uu____25997 = (singleton' env prob false)
in (solve_and_commit env uu____25997 (fun uu____25999 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____25994))
in (match (g) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g1) -> begin
(

let g2 = (

let uu____26010 = (

let uu____26011 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____26011)::[])
in (close_guard env uu____26010 g1))
in (discharge_guard_nosmt env g2))
end))
end));
))





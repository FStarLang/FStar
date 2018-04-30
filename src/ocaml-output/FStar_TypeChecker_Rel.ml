
open Prims
open FStar_Pervasives

let print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar  ->  Prims.string = (fun ctx_uvar -> (FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu____39; FStar_TypeChecker_Env.implicits = uu____40} -> begin
true
end
| uu____65 -> begin
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

let uu___118_102 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.NonTrivial (f'); FStar_TypeChecker_Env.deferred = uu___118_102.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___118_102.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___118_102.FStar_TypeChecker_Env.implicits}))
end))


let abstract_guard : FStar_Syntax_Syntax.binder  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun b g -> (abstract_guard_n ((b)::[]) g))


let def_check_vars_in_set : FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.term  ->  unit = (fun rng msg vset t -> (

let uu____137 = (FStar_Options.defensive ())
in (match (uu____137) with
| true -> begin
(

let s = (FStar_Syntax_Free.names t)
in (

let uu____141 = (

let uu____142 = (

let uu____143 = (FStar_Util.set_difference s vset)
in (FStar_All.pipe_left FStar_Util.set_is_empty uu____143))
in (not (uu____142)))
in (match (uu____141) with
| true -> begin
(

let uu____148 = (

let uu____153 = (

let uu____154 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____155 = (

let uu____156 = (FStar_Util.set_elements s)
in (FStar_All.pipe_right uu____156 (FStar_Syntax_Print.bvs_to_string ",\n\t")))
in (FStar_Util.format3 "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n" msg uu____154 uu____155)))
in ((FStar_Errors.Warning_Defensive), (uu____153)))
in (FStar_Errors.log_issue rng uu____148))
end
| uu____161 -> begin
()
end)))
end
| uu____162 -> begin
()
end)))


let def_check_closed : FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  unit = (fun rng msg t -> (

let uu____178 = (

let uu____179 = (FStar_Options.defensive ())
in (not (uu____179)))
in (match (uu____178) with
| true -> begin
()
end
| uu____180 -> begin
(def_check_vars_in_set rng msg FStar_Syntax_Free.empty t)
end)))


let def_check_closed_in : FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  unit = (fun rng msg l t -> (

let uu____205 = (

let uu____206 = (FStar_Options.defensive ())
in (not (uu____206)))
in (match (uu____205) with
| true -> begin
()
end
| uu____207 -> begin
(

let uu____208 = (FStar_Util.as_set l FStar_Syntax_Syntax.order_bv)
in (def_check_vars_in_set rng msg uu____208 t))
end)))


let def_check_closed_in_env : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  unit = (fun rng msg e t -> (

let uu____231 = (

let uu____232 = (FStar_Options.defensive ())
in (not (uu____232)))
in (match (uu____231) with
| true -> begin
()
end
| uu____233 -> begin
(

let uu____234 = (FStar_TypeChecker_Env.bound_vars e)
in (def_check_closed_in rng msg uu____234 t))
end)))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___119_248 = g
in (

let uu____249 = (

let uu____250 = (

let uu____251 = (

let uu____258 = (

let uu____259 = (

let uu____274 = (

let uu____283 = (FStar_Syntax_Syntax.as_arg e)
in (uu____283)::[])
in ((f), (uu____274)))
in FStar_Syntax_Syntax.Tm_app (uu____259))
in (FStar_Syntax_Syntax.mk uu____258))
in (uu____251 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _0_17 -> FStar_TypeChecker_Common.NonTrivial (_0_17)) uu____250))
in {FStar_TypeChecker_Env.guard_f = uu____249; FStar_TypeChecker_Env.deferred = uu___119_248.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___119_248.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___119_248.FStar_TypeChecker_Env.implicits}))
end))


let map_guard : FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  FStar_TypeChecker_Env.guard_t = (fun g map1 -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___120_331 = g
in (

let uu____332 = (

let uu____333 = (map1 f)
in FStar_TypeChecker_Common.NonTrivial (uu____333))
in {FStar_TypeChecker_Env.guard_f = uu____332; FStar_TypeChecker_Env.deferred = uu___120_331.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___120_331.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___120_331.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____339) -> begin
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

let uu____354 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (uu____354))
end))


let check_trivial : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (

let uu____364 = (

let uu____365 = (FStar_Syntax_Util.unmeta t)
in uu____365.FStar_Syntax_Syntax.n)
in (match (uu____364) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____369 -> begin
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

let uu____410 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = uu____410; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (((FStar_List.append (FStar_Pervasives_Native.fst g1.FStar_TypeChecker_Env.univ_ineqs) (FStar_Pervasives_Native.fst g2.FStar_TypeChecker_Env.univ_ineqs))), ((FStar_List.append (FStar_Pervasives_Native.snd g1.FStar_TypeChecker_Env.univ_ineqs) (FStar_Pervasives_Native.snd g2.FStar_TypeChecker_Env.univ_ineqs)))); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard_univs : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun us bs g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let f1 = (FStar_List.fold_right2 (fun u b f1 -> (

let uu____497 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____497) with
| true -> begin
f1
end
| uu____498 -> begin
(FStar_Syntax_Util.mk_forall u (FStar_Pervasives_Native.fst b) f1)
end))) us bs f)
in (

let uu___121_499 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.NonTrivial (f1); FStar_TypeChecker_Env.deferred = uu___121_499.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___121_499.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___121_499.FStar_TypeChecker_Env.implicits}))
end))


let close_forall : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____540 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____540) with
| true -> begin
f1
end
| uu____541 -> begin
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

let uu___122_559 = g
in (

let uu____560 = (

let uu____561 = (close_forall env binders f)
in FStar_TypeChecker_Common.NonTrivial (uu____561))
in {FStar_TypeChecker_Env.guard_f = uu____560; FStar_TypeChecker_Env.deferred = uu___122_559.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___122_559.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___122_559.FStar_TypeChecker_Env.implicits}))
end))

type uvi =
| TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)


let uu___is_TERM : uvi  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TERM (_0) -> begin
true
end
| uu____590 -> begin
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
| uu____620 -> begin
false
end))


let __proj__UNIV__item___0 : uvi  ->  (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe) = (fun projectee -> (match (projectee) with
| UNIV (_0) -> begin
_0
end))

type worklist =
{attempting : FStar_TypeChecker_Common.probs; wl_deferred : (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list; ctr : Prims.int; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_TypeChecker_Env.env; wl_implicits : FStar_TypeChecker_Env.implicits}


let __proj__Mkworklist__item__attempting : worklist  ->  FStar_TypeChecker_Common.probs = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits} -> begin
__fname__attempting
end))


let __proj__Mkworklist__item__wl_deferred : worklist  ->  (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits} -> begin
__fname__wl_deferred
end))


let __proj__Mkworklist__item__ctr : worklist  ->  Prims.int = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits} -> begin
__fname__ctr
end))


let __proj__Mkworklist__item__defer_ok : worklist  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits} -> begin
__fname__defer_ok
end))


let __proj__Mkworklist__item__smt_ok : worklist  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits} -> begin
__fname__smt_ok
end))


let __proj__Mkworklist__item__tcenv : worklist  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits} -> begin
__fname__tcenv
end))


let __proj__Mkworklist__item__wl_implicits : worklist  ->  FStar_TypeChecker_Env.implicits = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits} -> begin
__fname__wl_implicits
end))


let new_uvar : Prims.string  ->  worklist  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.binding Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term * worklist) = (fun reason wl r gamma binders k should_check -> (

let ctx_uvar = (

let uu____907 = (FStar_Syntax_Unionfind.fresh ())
in {FStar_Syntax_Syntax.ctx_uvar_head = uu____907; FStar_Syntax_Syntax.ctx_uvar_gamma = gamma; FStar_Syntax_Syntax.ctx_uvar_binders = binders; FStar_Syntax_Syntax.ctx_uvar_typ = k; FStar_Syntax_Syntax.ctx_uvar_reason = reason; FStar_Syntax_Syntax.ctx_uvar_should_check = should_check; FStar_Syntax_Syntax.ctx_uvar_range = r})
in ((FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r should_check gamma binders);
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (ctx_uvar)) FStar_Pervasives_Native.None r)
in ((ctx_uvar), (t), ((

let uu___123_923 = wl
in {attempting = uu___123_923.attempting; wl_deferred = uu___123_923.wl_deferred; ctr = uu___123_923.ctr; defer_ok = uu___123_923.defer_ok; smt_ok = uu___123_923.smt_ok; tcenv = uu___123_923.tcenv; wl_implicits = (((reason), (t), (ctx_uvar), (r), (should_check)))::wl.wl_implicits}))));
)))


let copy_uvar : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  worklist  ->  (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term * worklist) = (fun u t wl -> (new_uvar u.FStar_Syntax_Syntax.ctx_uvar_reason wl u.FStar_Syntax_Syntax.ctx_uvar_range u.FStar_Syntax_Syntax.ctx_uvar_gamma u.FStar_Syntax_Syntax.ctx_uvar_binders t u.FStar_Syntax_Syntax.ctx_uvar_should_check))

type solution =
| Success of (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits)
| Failed of (FStar_TypeChecker_Common.prob * Prims.string)


let uu___is_Success : solution  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
true
end
| uu____987 -> begin
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
| uu____1017 -> begin
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
| uu____1042 -> begin
false
end))


let uu___is_CONTRAVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CONTRAVARIANT -> begin
true
end
| uu____1048 -> begin
false
end))


let uu___is_INVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| INVARIANT -> begin
true
end
| uu____1054 -> begin
false
end))


type tprob =
FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem


type cprob =
FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem


type 'a problem_t =
'a FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun uu___89_1069 -> (match (uu___89_1069) with
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

let uu____1075 = (

let uu____1076 = (FStar_Syntax_Subst.compress t)
in uu____1076.FStar_Syntax_Syntax.n)
in (match (uu____1075) with
| FStar_Syntax_Syntax.Tm_uvar (u) -> begin
(print_ctx_uvar u)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u); FStar_Syntax_Syntax.pos = uu____1081; FStar_Syntax_Syntax.vars = uu____1082}, args) -> begin
(

let uu____1104 = (print_ctx_uvar u)
in (

let uu____1105 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "%s [%s]" uu____1104 uu____1105)))
end
| uu____1106 -> begin
(FStar_Syntax_Print.term_to_string t)
end)))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env uu___90_1116 -> (match (uu___90_1116) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____1120 = (

let uu____1123 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1124 = (

let uu____1127 = (term_to_string p.FStar_TypeChecker_Common.lhs)
in (

let uu____1128 = (

let uu____1131 = (

let uu____1134 = (term_to_string p.FStar_TypeChecker_Common.rhs)
in (uu____1134)::[])
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::uu____1131)
in (uu____1127)::uu____1128))
in (uu____1123)::uu____1124))
in (FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____1120))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____1138 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1139 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____1140 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1138 uu____1139 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1140))))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env uu___91_1150 -> (match (uu___91_1150) with
| UNIV (u, t) -> begin
(

let x = (

let uu____1154 = (FStar_Options.hide_uvar_nums ())
in (match (uu____1154) with
| true -> begin
"?"
end
| uu____1155 -> begin
(

let uu____1156 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____1156 FStar_Util.string_of_int))
end))
in (

let uu____1157 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x uu____1157)))
end
| TERM (u, t) -> begin
(

let x = (

let uu____1161 = (FStar_Options.hide_uvar_nums ())
in (match (uu____1161) with
| true -> begin
"?"
end
| uu____1162 -> begin
(

let uu____1163 = (FStar_Syntax_Unionfind.uvar_id u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_right uu____1163 FStar_Util.string_of_int))
end))
in (

let uu____1164 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x uu____1164)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (

let uu____1179 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right uu____1179 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (

let uu____1193 = (

let uu____1196 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right uu____1196 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right uu____1193 (FStar_String.concat ", "))))


let args_to_string : 'Auu____1209 . (FStar_Syntax_Syntax.term * 'Auu____1209) Prims.list  ->  Prims.string = (fun args -> (

let uu____1227 = (FStar_All.pipe_right args (FStar_List.map (fun uu____1245 -> (match (uu____1245) with
| (x, uu____1251) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____1227 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> (

let uu____1259 = (

let uu____1260 = (FStar_Options.eager_inference ())
in (not (uu____1260)))
in {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = uu____1259; smt_ok = true; tcenv = env; wl_implicits = []}))


let singleton : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun wl prob smt_ok -> (

let uu___124_1292 = wl
in {attempting = (prob)::[]; wl_deferred = uu___124_1292.wl_deferred; ctr = uu___124_1292.ctr; defer_ok = uu___124_1292.defer_ok; smt_ok = smt_ok; tcenv = uu___124_1292.tcenv; wl_implicits = uu___124_1292.wl_implicits}))


let wl_of_guard : 'Auu____1299 . FStar_TypeChecker_Env.env  ->  ('Auu____1299 * FStar_TypeChecker_Common.prob) Prims.list  ->  worklist = (fun env g -> (

let uu___125_1322 = (empty_worklist env)
in (

let uu____1323 = (FStar_List.map FStar_Pervasives_Native.snd g)
in {attempting = uu____1323; wl_deferred = uu___125_1322.wl_deferred; ctr = uu___125_1322.ctr; defer_ok = uu___125_1322.defer_ok; smt_ok = uu___125_1322.smt_ok; tcenv = uu___125_1322.tcenv; wl_implicits = uu___125_1322.wl_implicits})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu___126_1343 = wl
in {attempting = uu___126_1343.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = uu___126_1343.ctr; defer_ok = uu___126_1343.defer_ok; smt_ok = uu___126_1343.smt_ok; tcenv = uu___126_1343.tcenv; wl_implicits = uu___126_1343.wl_implicits}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let uu___127_1364 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = uu___127_1364.wl_deferred; ctr = uu___127_1364.ctr; defer_ok = uu___127_1364.defer_ok; smt_ok = uu___127_1364.smt_ok; tcenv = uu___127_1364.tcenv; wl_implicits = uu___127_1364.wl_implicits}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> ((

let uu____1381 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____1381) with
| true -> begin
(

let uu____1382 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1382))
end
| uu____1383 -> begin
()
end));
Failed (((prob), (reason)));
))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun uu___92_1388 -> (match (uu___92_1388) with
| FStar_TypeChecker_Common.EQ -> begin
FStar_TypeChecker_Common.EQ
end
| FStar_TypeChecker_Common.SUB -> begin
FStar_TypeChecker_Common.SUBINV
end
| FStar_TypeChecker_Common.SUBINV -> begin
FStar_TypeChecker_Common.SUB
end))


let invert : 'Auu____1393 . 'Auu____1393 FStar_TypeChecker_Common.problem  ->  'Auu____1393 FStar_TypeChecker_Common.problem = (fun p -> (

let uu___128_1405 = p
in {FStar_TypeChecker_Common.pid = uu___128_1405.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = uu___128_1405.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___128_1405.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___128_1405.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___128_1405.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___128_1405.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___128_1405.FStar_TypeChecker_Common.rank}))


let maybe_invert : 'Auu____1412 . 'Auu____1412 FStar_TypeChecker_Common.problem  ->  'Auu____1412 FStar_TypeChecker_Common.problem = (fun p -> (match ((Prims.op_Equality p.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUBINV)) with
| true -> begin
(invert p)
end
| uu____1424 -> begin
p
end))


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___93_1429 -> (match (uu___93_1429) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_18 -> FStar_TypeChecker_Common.TProb (_0_18)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_19 -> FStar_TypeChecker_Common.CProb (_0_19)))
end))


let make_prob_eq : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___94_1444 -> (match (uu___94_1444) with
| FStar_TypeChecker_Common.TProb (p) -> begin
FStar_TypeChecker_Common.TProb ((

let uu___129_1450 = p
in {FStar_TypeChecker_Common.pid = uu___129_1450.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___129_1450.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___129_1450.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___129_1450.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___129_1450.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___129_1450.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___129_1450.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___129_1450.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___129_1450.FStar_TypeChecker_Common.rank}))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
FStar_TypeChecker_Common.CProb ((

let uu___130_1458 = p
in {FStar_TypeChecker_Common.pid = uu___130_1458.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___130_1458.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___130_1458.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___130_1458.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___130_1458.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___130_1458.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___130_1458.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___130_1458.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___130_1458.FStar_TypeChecker_Common.rank}))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel uu___95_1470 -> (match (uu___95_1470) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun uu___96_1475 -> (match (uu___96_1475) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun uu___97_1486 -> (match (uu___97_1486) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun uu___98_1499 -> (match (uu___98_1499) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun uu___99_1512 -> (match (uu___99_1512) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term = (fun uu___100_1523 -> (match (uu___100_1523) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_guard_uvar : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.ctx_uvar) = (fun uu___101_1538 -> (match (uu___101_1538) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard_uvar
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard_uvar
end))


let def_scope_wf : 'Auu____1557 . Prims.string  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.bv * 'Auu____1557) Prims.list  ->  unit = (fun msg rng r -> (

let uu____1585 = (

let uu____1586 = (FStar_Options.defensive ())
in (not (uu____1586)))
in (match (uu____1585) with
| true -> begin
()
end
| uu____1587 -> begin
(

let rec aux = (fun prev next -> (match (next) with
| [] -> begin
()
end
| ((bv, uu____1620))::bs -> begin
((def_check_closed_in rng msg prev bv.FStar_Syntax_Syntax.sort);
(aux (FStar_List.append prev ((bv)::[])) bs);
)
end))
in (aux [] r))
end)))


let p_scope : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun prob -> (

let r = (match (prob) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_List.append (FStar_Pervasives_Native.snd p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders (FStar_Pervasives_Native.fst p.FStar_TypeChecker_Common.logical_guard_uvar))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_List.append (FStar_Pervasives_Native.snd p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders (FStar_Pervasives_Native.fst p.FStar_TypeChecker_Common.logical_guard_uvar))
end)
in ((def_scope_wf "p_scope" (p_loc prob) r);
r;
)))


let def_check_scoped : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  unit = (fun msg prob phi -> (

let uu____1687 = (

let uu____1688 = (FStar_Options.defensive ())
in (not (uu____1688)))
in (match (uu____1687) with
| true -> begin
()
end
| uu____1689 -> begin
(

let uu____1690 = (

let uu____1693 = (p_scope prob)
in (FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst) uu____1693))
in (def_check_closed_in (p_loc prob) msg uu____1690 phi))
end)))


let def_check_prob : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  unit = (fun msg prob -> ((

let uu____1723 = (

let uu____1724 = (FStar_Options.defensive ())
in (not (uu____1724)))
in (match (uu____1723) with
| true -> begin
()
end
| uu____1725 -> begin
(

let uu____1726 = (p_scope prob)
in (def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1726))
end));
(def_check_scoped (Prims.strcat msg ".guard") prob (p_guard prob));
(match (prob) with
| FStar_TypeChecker_Common.TProb (p) -> begin
((def_check_scoped (Prims.strcat msg ".lhs") prob p.FStar_TypeChecker_Common.lhs);
(def_check_scoped (Prims.strcat msg ".rhs") prob p.FStar_TypeChecker_Common.rhs);
)
end
| uu____1738 -> begin
()
end);
))


let mk_eq2 : 'Auu____1750 . worklist  ->  'Auu____1750  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * worklist) = (fun wl prob t1 t2 -> (

let uu____1779 = (FStar_Syntax_Util.type_u ())
in (match (uu____1779) with
| (t_type, u) -> begin
(

let uu____1790 = (new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos wl.tcenv.FStar_TypeChecker_Env.gamma [] t_type false)
in (match (uu____1790) with
| (uu____1805, tt, wl1) -> begin
(

let uu____1808 = (FStar_Syntax_Util.mk_eq2 u tt t1 t2)
in ((uu____1808), (wl1)))
end))
end)))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___102_1813 -> (match (uu___102_1813) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _0_20 -> FStar_TypeChecker_Common.TProb (_0_20)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _0_21 -> FStar_TypeChecker_Common.CProb (_0_21)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> (

let uu____1829 = (FStar_All.pipe_right (p_reason p) FStar_List.length)
in (Prims.op_Equality uu____1829 (Prims.parse_int "1"))))


let next_pid : unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____1841 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
)))


let mk_problem : 'Auu____1939 . worklist  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_TypeChecker_Common.prob  ->  'Auu____1939  ->  FStar_TypeChecker_Common.rel  ->  'Auu____1939  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  Prims.string  ->  ('Auu____1939 FStar_TypeChecker_Common.problem * worklist) = (fun wl scope orig lhs rel rhs elt reason -> (

let guard_ty = (

let uu____2005 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow scope uu____2005))
in (

let uu____2008 = (

let uu____2015 = (FStar_TypeChecker_Env.all_binders wl.tcenv)
in (new_uvar (Prims.strcat "mk_problem: logical guard for " reason) wl FStar_Range.dummyRange wl.tcenv.FStar_TypeChecker_Env.gamma uu____2015 guard_ty false))
in (match (uu____2008) with
| (ctx_uvar, lg, wl1) -> begin
(

let lg1 = (match (scope) with
| [] -> begin
lg
end
| uu____2036 -> begin
(

let uu____2043 = (

let uu____2048 = (FStar_List.map (fun uu____2061 -> (match (uu____2061) with
| (x, i) -> begin
(

let uu____2072 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____2072), (i)))
end)) scope)
in (FStar_Syntax_Syntax.mk_Tm_app lg uu____2048))
in (uu____2043 FStar_Pervasives_Native.None lg.FStar_Syntax_Syntax.pos))
end)
in (

let uu____2075 = (

let uu____2078 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____2078; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = lg1; FStar_TypeChecker_Common.logical_guard_uvar = ((scope), (ctx_uvar)); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})
in ((uu____2075), (wl1))))
end))))


let mk_t_problem : worklist  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_TypeChecker_Common.prob * worklist) = (fun wl scope orig lhs rel rhs elt reason -> (

let uu____2141 = (mk_problem wl scope orig lhs rel rhs elt reason)
in (match (uu____2141) with
| (p, wl1) -> begin
((FStar_TypeChecker_Common.TProb (p)), (wl1))
end)))


let mk_c_problem : worklist  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_TypeChecker_Common.prob * worklist) = (fun wl scope orig lhs rel rhs elt reason -> (

let uu____2218 = (mk_problem wl scope orig lhs rel rhs elt reason)
in (match (uu____2218) with
| (p, wl1) -> begin
((FStar_TypeChecker_Common.CProb (p)), (wl1))
end)))


let new_problem : 'Auu____2253 . worklist  ->  FStar_TypeChecker_Env.env  ->  'Auu____2253  ->  FStar_TypeChecker_Common.rel  ->  'Auu____2253  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  Prims.string  ->  ('Auu____2253 FStar_TypeChecker_Common.problem * worklist) = (fun wl env lhs rel rhs subject loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (

let uu____2305 = (match (subject) with
| FStar_Pervasives_Native.None -> begin
(([]), (FStar_Syntax_Util.ktype0), (FStar_Pervasives_Native.None))
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let bs = (

let uu____2360 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2360)::[])
in (

let uu____2373 = (

let uu____2376 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow bs uu____2376))
in (

let uu____2379 = (

let uu____2382 = (FStar_Syntax_Syntax.bv_to_name x)
in FStar_Pervasives_Native.Some (uu____2382))
in ((bs), (uu____2373), (uu____2379)))))
end)
in (match (uu____2305) with
| (bs, lg_ty, elt) -> begin
(

let uu____2422 = (new_uvar (Prims.strcat "new_problem: logical guard for " reason) (

let uu___131_2430 = wl
in {attempting = uu___131_2430.attempting; wl_deferred = uu___131_2430.wl_deferred; ctr = uu___131_2430.ctr; defer_ok = uu___131_2430.defer_ok; smt_ok = uu___131_2430.smt_ok; tcenv = env; wl_implicits = uu___131_2430.wl_implicits}) loc env.FStar_TypeChecker_Env.gamma scope lg_ty false)
in (match (uu____2422) with
| (ctx_uvar, lg, wl1) -> begin
(

let lg1 = (match (elt) with
| FStar_Pervasives_Native.None -> begin
lg
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____2442 = (

let uu____2447 = (

let uu____2448 = (FStar_Syntax_Syntax.as_arg x)
in (uu____2448)::[])
in (FStar_Syntax_Syntax.mk_Tm_app lg uu____2447))
in (uu____2442 FStar_Pervasives_Native.None loc))
end)
in (

let uu____2469 = (

let uu____2472 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____2472; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = lg1; FStar_TypeChecker_Common.logical_guard_uvar = ((bs), (ctx_uvar)); FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})
in ((uu____2469), (wl1))))
end))
end))))


let problem_using_guard : 'Auu____2489 . FStar_TypeChecker_Common.prob  ->  'Auu____2489  ->  FStar_TypeChecker_Common.rel  ->  'Auu____2489  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  Prims.string  ->  'Auu____2489 FStar_TypeChecker_Common.problem = (fun orig lhs rel rhs elt reason -> (

let uu____2526 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____2526; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.logical_guard_uvar = (p_guard_uvar orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None}))


let guard_on_element : 'Auu____2537 . worklist  ->  'Auu____2537 FStar_TypeChecker_Common.problem  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun wl problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| FStar_Pervasives_Native.None -> begin
(

let u = (wl.tcenv.FStar_TypeChecker_Env.universe_of wl.tcenv x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Util.mk_forall u x phi))
end
| FStar_Pervasives_Native.Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (

let uu____2587 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____2587) with
| true -> begin
(

let uu____2588 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (

let uu____2589 = (prob_to_string env d)
in (

let uu____2590 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" uu____2588 uu____2589 uu____2590 s))))
end
| uu____2593 -> begin
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
| uu____2596 -> begin
(failwith "impossible")
end)
in (

let uu____2597 = (match (d1) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____2609 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (

let uu____2610 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((uu____2609), (uu____2610))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____2614 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (

let uu____2615 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((uu____2614), (uu____2615))))
end)
in (match (uu____2597) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___103_2633 -> (match (uu___103_2633) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Syntax_Unionfind.univ_union u u')
end
| uu____2645 -> begin
(FStar_Syntax_Unionfind.univ_change u t)
end)
end
| TERM (u, t) -> begin
((def_check_closed t.FStar_Syntax_Syntax.pos "commit" t);
(FStar_Syntax_Util.set_uvar u.FStar_Syntax_Syntax.ctx_uvar_head t);
)
end)))))


let find_term_uvar : FStar_Syntax_Syntax.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun uv s -> (FStar_Util.find_map s (fun uu___104_2667 -> (match (uu___104_2667) with
| UNIV (uu____2670) -> begin
FStar_Pervasives_Native.None
end
| TERM (u, t) -> begin
(

let uu____2677 = (FStar_Syntax_Unionfind.equiv uv u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____2677) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____2680 -> begin
FStar_Pervasives_Native.None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe_uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun u s -> (FStar_Util.find_map s (fun uu___105_2701 -> (match (uu___105_2701) with
| UNIV (u', t) -> begin
(

let uu____2706 = (FStar_Syntax_Unionfind.univ_equiv u u')
in (match (uu____2706) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____2709 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____2710 -> begin
FStar_Pervasives_Native.None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____2721 = (

let uu____2722 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env uu____2722))
in (FStar_Syntax_Subst.compress uu____2721)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____2733 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress uu____2733)))


let norm_arg : 'Auu____2740 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * 'Auu____2740)  ->  (FStar_Syntax_Syntax.term * 'Auu____2740) = (fun env t -> (

let uu____2763 = (sn env (FStar_Pervasives_Native.fst t))
in ((uu____2763), ((FStar_Pervasives_Native.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____2804 -> (match (uu____2804) with
| (x, imp) -> begin
(

let uu____2815 = (

let uu___132_2816 = x
in (

let uu____2817 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___132_2816.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___132_2816.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2817}))
in ((uu____2815), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____2838 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____2838))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____2842 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____2842))
end
| uu____2845 -> begin
u2
end)))
in (

let uu____2846 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2846))))


let base_and_refinement_maybe_delta : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option) = (fun should_delta env t1 -> (

let norm_refinement = (fun env1 t -> (

let steps = (match (should_delta) with
| true -> begin
(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]
end
| uu____2886 -> begin
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
| uu____2959 -> begin
(

let uu____2960 = (norm_refinement env t12)
in (match (uu____2960) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x1, phi1); FStar_Syntax_Syntax.pos = uu____2975; FStar_Syntax_Syntax.vars = uu____2976} -> begin
((x1.FStar_Syntax_Syntax.sort), (FStar_Pervasives_Native.Some (((x1), (phi1)))))
end
| tt -> begin
(

let uu____3002 = (

let uu____3003 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____3004 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" uu____3003 uu____3004)))
in (failwith uu____3002))
end))
end)
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____3018 = (FStar_Syntax_Util.unfold_lazy i)
in (aux norm1 uu____3018))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____3019) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____3052 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____3054 = (

let uu____3055 = (FStar_Syntax_Subst.compress t1')
in uu____3055.FStar_Syntax_Syntax.n)
in (match (uu____3054) with
| FStar_Syntax_Syntax.Tm_refine (uu____3070) -> begin
(aux true t1')
end
| uu____3077 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____3092) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____3119 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____3121 = (

let uu____3122 = (FStar_Syntax_Subst.compress t1')
in uu____3122.FStar_Syntax_Syntax.n)
in (match (uu____3121) with
| FStar_Syntax_Syntax.Tm_refine (uu____3137) -> begin
(aux true t1')
end
| uu____3144 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_app (uu____3159) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____3200 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____3202 = (

let uu____3203 = (FStar_Syntax_Subst.compress t1')
in uu____3203.FStar_Syntax_Syntax.n)
in (match (uu____3202) with
| FStar_Syntax_Syntax.Tm_refine (uu____3218) -> begin
(aux true t1')
end
| uu____3225 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_type (uu____3240) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_constant (uu____3255) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_name (uu____3270) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3285) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3300) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_abs (uu____3327) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_quoted (uu____3358) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3379) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_let (uu____3394) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_match (uu____3421) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_meta (uu____3458) -> begin
(

let uu____3465 = (

let uu____3466 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3467 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3466 uu____3467)))
in (failwith uu____3465))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3480) -> begin
(

let uu____3507 = (

let uu____3508 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3509 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3508 uu____3509)))
in (failwith uu____3507))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____3522) -> begin
(

let uu____3547 = (

let uu____3548 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3549 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3548 uu____3549)))
in (failwith uu____3547))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____3562 = (

let uu____3563 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3564 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3563 uu____3564)))
in (failwith uu____3562))
end)))
in (

let uu____3577 = (whnf env t1)
in (aux false uu____3577)))))


let base_and_refinement : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option) = (fun env t -> (base_and_refinement_maybe_delta false env t))


let normalize_refinement : 'Auu____3608 . FStar_TypeChecker_Normalize.steps  ->  FStar_TypeChecker_Env.env  ->  'Auu____3608  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____3639 = (base_and_refinement env t)
in (FStar_All.pipe_right uu____3639 FStar_Pervasives_Native.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (

let uu____3675 = (FStar_Syntax_Syntax.null_bv t)
in ((uu____3675), (FStar_Syntax_Util.t_true))))


let as_refinement : 'Auu____3686 . Prims.bool  ->  FStar_TypeChecker_Env.env  ->  'Auu____3686  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun delta1 env wl t -> (

let uu____3711 = (base_and_refinement_maybe_delta delta1 env t)
in (match (uu____3711) with
| (t_base, refinement) -> begin
(match (refinement) with
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end
| FStar_Pervasives_Native.Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun uu____3788 -> (match (uu____3788) with
| (t_base, refopt) -> begin
(

let uu____3821 = (match (refopt) with
| FStar_Pervasives_Native.Some (y, phi) -> begin
((y), (phi))
end
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end)
in (match (uu____3821) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl prob -> (prob_to_string wl.tcenv prob))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (

let uu____3861 = (

let uu____3864 = (

let uu____3867 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____3890 -> (match (uu____3890) with
| (uu____3897, uu____3898, x) -> begin
x
end))))
in (FStar_List.append wl.attempting uu____3867))
in (FStar_List.map (wl_prob_to_string wl) uu____3864))
in (FStar_All.pipe_right uu____3861 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____3917 = (

let uu____3930 = (

let uu____3931 = (FStar_Syntax_Subst.compress k)
in uu____3931.FStar_Syntax_Syntax.n)
in (match (uu____3930) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((Prims.op_Equality (FStar_List.length bs) (FStar_List.length ys))) with
| true -> begin
(

let uu____3984 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (uu____3984)))
end
| uu____3997 -> begin
(

let uu____3998 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____3998) with
| (ys', t1, uu____4021) -> begin
(

let uu____4026 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t1))), (uu____4026)))
end))
end)
end
| uu____4067 -> begin
(

let uu____4068 = (

let uu____4079 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____4079)))
in ((((ys), (t))), (uu____4068)))
end))
in (match (uu____3917) with
| ((ys1, t1), (xs, c)) -> begin
(match ((Prims.op_disEquality (FStar_List.length xs) (FStar_List.length ys1))) with
| true -> begin
(FStar_Syntax_Util.abs ys1 t1 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None []))))
end
| uu____4126 -> begin
(

let c1 = (

let uu____4128 = (FStar_Syntax_Util.rename_binders xs ys1)
in (FStar_Syntax_Subst.subst_comp uu____4128 c))
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

let uu____4181 = (p_guard_uvar prob)
in (match (uu____4181) with
| (xs, uv) -> begin
((

let uu____4189 = (FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____4189) with
| FStar_Pervasives_Native.None -> begin
((

let uu____4193 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____4193) with
| true -> begin
(

let uu____4194 = (FStar_Util.string_of_int (p_pid prob))
in (

let uu____4195 = (print_ctx_uvar uv)
in (

let uu____4196 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" uu____4194 uu____4195 uu____4196))))
end
| uu____4197 -> begin
()
end));
(

let phi1 = (FStar_Syntax_Util.abs xs phi (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in ((def_check_closed (p_loc prob) "solve_prob\'" phi1);
(FStar_Syntax_Util.set_uvar uv.FStar_Syntax_Syntax.ctx_uvar_head phi1);
));
)
end
| FStar_Pervasives_Native.Some (uu____4202) -> begin
(match ((not (resolve_ok))) with
| true -> begin
(failwith "Impossible: this instance has already been assigned a solution")
end
| uu____4203 -> begin
()
end)
end));
(commit uvis);
(

let uu___133_4205 = wl
in {attempting = uu___133_4205.attempting; wl_deferred = uu___133_4205.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___133_4205.defer_ok; smt_ok = uu___133_4205.smt_ok; tcenv = uu___133_4205.tcenv; wl_implicits = uu___133_4205.wl_implicits});
)
end)));
))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____4226 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____4226) with
| true -> begin
(

let uu____4227 = (FStar_Util.string_of_int pid)
in (

let uu____4228 = (

let uu____4229 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right uu____4229 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with [%s]\n" uu____4227 uu____4228)))
end
| uu____4234 -> begin
()
end));
(commit sol);
(

let uu___134_4236 = wl
in {attempting = uu___134_4236.attempting; wl_deferred = uu___134_4236.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___134_4236.defer_ok; smt_ok = uu___134_4236.smt_ok; tcenv = uu___134_4236.tcenv; wl_implicits = uu___134_4236.wl_implicits});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> ((def_check_prob "solve_prob.prob" prob);
(FStar_Util.iter_opt logical_guard (def_check_scoped "solve_prob.guard" prob));
(

let conj_guard1 = (fun t g -> (match (((t), (g))) with
| (uu____4298, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (FStar_Pervasives_Native.None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
FStar_Pervasives_Native.Some (f)
end
| (FStar_Pervasives_Native.Some (t1), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(

let uu____4324 = (FStar_Syntax_Util.mk_conj t1 f)
in FStar_Pervasives_Native.Some (uu____4324))
end))
in ((

let uu____4330 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____4330) with
| true -> begin
(

let uu____4331 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (

let uu____4332 = (

let uu____4333 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right uu____4333 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____4331 uu____4332)))
end
| uu____4338 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
));
))


let occurs : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool) = (fun uk t -> (

let uvars1 = (

let uu____4358 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right uu____4358 FStar_Util.set_elements))
in (

let occurs = (FStar_All.pipe_right uvars1 (FStar_Util.for_some (fun uv -> (FStar_Syntax_Unionfind.equiv uv.FStar_Syntax_Syntax.ctx_uvar_head uk.FStar_Syntax_Syntax.ctx_uvar_head))))
in ((uvars1), (occurs)))))


let occurs_check : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool * Prims.string FStar_Pervasives_Native.option) = (fun uk t -> (

let uu____4392 = (occurs uk t)
in (match (uu____4392) with
| (uvars1, occurs1) -> begin
(

let msg = (match ((not (occurs1))) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4420 -> begin
(

let uu____4421 = (

let uu____4422 = (FStar_Syntax_Print.uvar_to_string uk.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____4423 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" uu____4422 uu____4423)))
in FStar_Pervasives_Native.Some (uu____4421))
end)
in ((uvars1), ((not (occurs1))), (msg)))
end)))


let rec maximal_prefix : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.binders)) = (fun bs bs' -> (match (((bs), (bs'))) with
| (((b, i))::bs_tail, ((b', i'))::bs'_tail) -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
(

let uu____4512 = (maximal_prefix bs_tail bs'_tail)
in (match (uu____4512) with
| (pfx, rest) -> begin
(((((b), (i)))::pfx), (rest))
end))
end
| uu____4547 -> begin
(([]), (((bs), (bs'))))
end)
end
| uu____4556 -> begin
(([]), (((bs), (bs'))))
end))


let extend_gamma : FStar_Syntax_Syntax.gamma  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binding Prims.list = (fun g bs -> (FStar_List.fold_left (fun g1 uu____4604 -> (match (uu____4604) with
| (x, uu____4614) -> begin
(FStar_Syntax_Syntax.Binding_var (x))::g1
end)) g bs))


let gamma_until : FStar_Syntax_Syntax.gamma  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binding Prims.list = (fun g bs -> (

let uu____4627 = (FStar_List.last bs)
in (match (uu____4627) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (x, uu____4645) -> begin
(

let uu____4650 = (FStar_Util.prefix_until (fun uu___106_4665 -> (match (uu___106_4665) with
| FStar_Syntax_Syntax.Binding_var (x') -> begin
(FStar_Syntax_Syntax.bv_eq x x')
end
| uu____4667 -> begin
false
end)) g)
in (match (uu____4650) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____4680, bx, rest) -> begin
(bx)::rest
end))
end)))


let restrict_ctx : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.ctx_uvar  ->  worklist  ->  worklist = (fun tgt src wl -> (

let uu____4716 = (maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders src.FStar_Syntax_Syntax.ctx_uvar_binders)
in (match (uu____4716) with
| (pfx, uu____4726) -> begin
(

let g = (gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx)
in (

let uu____4738 = (new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl src.FStar_Syntax_Syntax.ctx_uvar_range g pfx src.FStar_Syntax_Syntax.ctx_uvar_typ src.FStar_Syntax_Syntax.ctx_uvar_should_check)
in (match (uu____4738) with
| (uu____4745, src', wl1) -> begin
((FStar_Syntax_Unionfind.change src.FStar_Syntax_Syntax.ctx_uvar_head src');
wl1;
)
end)))
end)))


let restrict_all_uvars : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.ctx_uvar Prims.list  ->  worklist  ->  worklist = (fun tgt sources wl -> (FStar_List.fold_right (restrict_ctx tgt) sources wl))


let intersect_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun v1 v2 -> (

let as_set1 = (fun v3 -> (FStar_All.pipe_right v3 (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set1 v1)
in (

let uu____4825 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____4879 uu____4880 -> (match (((uu____4879), (uu____4880))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____4961 = (

let uu____4962 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation uu____4962))
in (match (uu____4961) with
| true -> begin
((isect), (isect_set))
end
| uu____4983 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____4987 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____4987) with
| true -> begin
(

let uu____5000 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (uu____5000)))
end
| uu____5015 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (uu____4825) with
| (isect, uu____5037) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq : 'Auu____5066 'Auu____5067 . (FStar_Syntax_Syntax.bv * 'Auu____5066) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____5067) Prims.list  ->  Prims.bool = (fun v1 v2 -> ((Prims.op_Equality (FStar_List.length v1) (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____5124 uu____5125 -> (match (((uu____5124), (uu____5125))) with
| ((a, uu____5143), (b, uu____5145)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let name_exists_in_binders : 'Auu____5160 . FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.bv * 'Auu____5160) Prims.list  ->  Prims.bool = (fun x bs -> (FStar_Util.for_some (fun uu____5190 -> (match (uu____5190) with
| (y, uu____5196) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end)) bs))


let pat_vars : 'Auu____5207 'Auu____5208 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____5207) Prims.list  ->  (FStar_Syntax_Syntax.term * 'Auu____5208) Prims.list  ->  FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option = (fun env ctx args -> (

let rec aux = (fun seen args1 -> (match (args1) with
| [] -> begin
FStar_Pervasives_Native.Some ((FStar_List.rev seen))
end
| (arg)::args2 -> begin
(

let hd1 = (norm_arg env arg)
in (match ((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(

let uu____5317 = ((name_exists_in_binders a seen) || (name_exists_in_binders a ctx))
in (match (uu____5317) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5324 -> begin
(

let uu____5325 = (

let uu____5328 = (FStar_Syntax_Syntax.mk_binder a)
in (uu____5328)::seen)
in (aux uu____5325 args2))
end))
end
| uu____5329 -> begin
FStar_Pervasives_Native.None
end))
end))
in (aux [] args)))


type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)


let flex_t_to_string : 'Auu____5342 . ('Auu____5342 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)  ->  Prims.string = (fun uu____5353 -> (match (uu____5353) with
| (uu____5360, c, args) -> begin
(

let uu____5363 = (print_ctx_uvar c)
in (

let uu____5364 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "%s [%s]" uu____5363 uu____5364)))
end))


let is_flex : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____5370 = (

let uu____5371 = (FStar_Syntax_Subst.compress t)
in uu____5371.FStar_Syntax_Syntax.n)
in (match (uu____5370) with
| FStar_Syntax_Syntax.Tm_uvar (uu____5374) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____5375); FStar_Syntax_Syntax.pos = uu____5376; FStar_Syntax_Syntax.vars = uu____5377}, uu____5378) -> begin
true
end
| uu____5399 -> begin
false
end)))


let destruct_flex_t : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv) -> begin
((t), (uv), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv); FStar_Syntax_Syntax.pos = uu____5417; FStar_Syntax_Syntax.vars = uu____5418}, args) -> begin
((t), (uv), (args))
end
| uu____5440 -> begin
(failwith "Not a flex-uvar")
end))

type match_result =
| MisMatch of (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
| HeadMatch
| FullMatch


let uu___is_MisMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MisMatch (_0) -> begin
true
end
| uu____5468 -> begin
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
| uu____5505 -> begin
false
end))


let uu___is_FullMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullMatch -> begin
true
end
| uu____5511 -> begin
false
end))


let string_of_option : 'Auu____5518 . ('Auu____5518  ->  Prims.string)  ->  'Auu____5518 FStar_Pervasives_Native.option  ->  Prims.string = (fun f uu___107_5533 -> (match (uu___107_5533) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____5539 = (f x)
in (Prims.strcat "Some " uu____5539))
end))


let string_of_match_result : match_result  ->  Prims.string = (fun uu___108_5544 -> (match (uu___108_5544) with
| MisMatch (d1, d2) -> begin
(

let uu____5555 = (

let uu____5556 = (string_of_option FStar_Syntax_Print.delta_depth_to_string d1)
in (

let uu____5557 = (

let uu____5558 = (

let uu____5559 = (string_of_option FStar_Syntax_Print.delta_depth_to_string d2)
in (Prims.strcat uu____5559 ")"))
in (Prims.strcat ") (" uu____5558))
in (Prims.strcat uu____5556 uu____5557)))
in (Prims.strcat "MisMatch (" uu____5555))
end
| HeadMatch -> begin
"HeadMatch"
end
| FullMatch -> begin
"FullMatch"
end))


let head_match : match_result  ->  match_result = (fun uu___109_5564 -> (match (uu___109_5564) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____5579 -> begin
HeadMatch
end))


let and_match : match_result  ->  (unit  ->  match_result)  ->  match_result = (fun m1 m2 -> (match (m1) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| HeadMatch -> begin
(

let uu____5609 = (m2 ())
in (match (uu____5609) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____5624 -> begin
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
| uu____5636 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
end
| FStar_Syntax_Syntax.Delta_defined_at_level (uu____5637) -> begin
(

let uu____5638 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5638) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Syntax.Delta_constant
end
| uu____5649 -> begin
fv.FStar_Syntax_Syntax.fv_delta
end))
end
| d -> begin
d
end))


let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____5672) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____5681) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____5709 = (FStar_Syntax_Util.unfold_lazy i)
in (delta_depth_of_term env uu____5709))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_bvar (uu____5710) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_name (uu____5711) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uvar (uu____5712) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_let (uu____5713) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_match (uu____5726) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____5750) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____5756, uu____5757) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____5799) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____5820; FStar_Syntax_Syntax.index = uu____5821; FStar_Syntax_Syntax.sort = t2}, uu____5823) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_constant (uu____5830) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_type (uu____5831) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____5832) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____5845) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_abs (uu____5852) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5870 = (fv_delta_depth env fv)
in FStar_Pervasives_Native.Some (uu____5870))
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
| uu____5890 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____5897 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____5897) with
| true -> begin
FullMatch
end
| uu____5898 -> begin
(

let uu____5899 = (

let uu____5908 = (

let uu____5911 = (fv_delta_depth env f)
in FStar_Pervasives_Native.Some (uu____5911))
in (

let uu____5912 = (

let uu____5915 = (fv_delta_depth env g)
in FStar_Pervasives_Native.Some (uu____5915))
in ((uu____5908), (uu____5912))))
in MisMatch (uu____5899))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____5921), FStar_Syntax_Syntax.Tm_uinst (g, uu____5923)) -> begin
(

let uu____5932 = (head_matches env f g)
in (FStar_All.pipe_right uu____5932 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____5935 = (FStar_Const.eq_const c d)
in (match (uu____5935) with
| true -> begin
FullMatch
end
| uu____5936 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (uv), FStar_Syntax_Syntax.Tm_uvar (uv')) -> begin
(

let uu____5943 = (FStar_Syntax_Unionfind.equiv uv.FStar_Syntax_Syntax.ctx_uvar_head uv'.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____5943) with
| true -> begin
FullMatch
end
| uu____5944 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____5950), FStar_Syntax_Syntax.Tm_refine (y, uu____5952)) -> begin
(

let uu____5961 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____5961 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____5963), uu____5964) -> begin
(

let uu____5969 = (head_matches env x.FStar_Syntax_Syntax.sort t21)
in (FStar_All.pipe_right uu____5969 head_match))
end
| (uu____5970, FStar_Syntax_Syntax.Tm_refine (x, uu____5972)) -> begin
(

let uu____5977 = (head_matches env t11 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____5977 head_match))
end
| (FStar_Syntax_Syntax.Tm_type (uu____5978), FStar_Syntax_Syntax.Tm_type (uu____5979)) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_arrow (uu____5980), FStar_Syntax_Syntax.Tm_arrow (uu____5981)) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____6007), FStar_Syntax_Syntax.Tm_app (head', uu____6009)) -> begin
(

let uu____6050 = (head_matches env head1 head')
in (FStar_All.pipe_right uu____6050 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____6052), uu____6053) -> begin
(

let uu____6074 = (head_matches env head1 t21)
in (FStar_All.pipe_right uu____6074 head_match))
end
| (uu____6075, FStar_Syntax_Syntax.Tm_app (head1, uu____6077)) -> begin
(

let uu____6098 = (head_matches env t11 head1)
in (FStar_All.pipe_right uu____6098 head_match))
end
| uu____6099 -> begin
(

let uu____6104 = (

let uu____6113 = (delta_depth_of_term env t11)
in (

let uu____6116 = (delta_depth_of_term env t21)
in ((uu____6113), (uu____6116))))
in MisMatch (uu____6104))
end))))


let head_matches_delta : 'Auu____6133 . FStar_TypeChecker_Env.env  ->  'Auu____6133  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (match_result * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) FStar_Pervasives_Native.option) = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let uu____6172 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____6172) with
| (head1, uu____6190) -> begin
(

let uu____6211 = (

let uu____6212 = (FStar_Syntax_Util.un_uinst head1)
in uu____6212.FStar_Syntax_Syntax.n)
in (match (uu____6211) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____6218 = (

let uu____6219 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____6219 FStar_Option.isSome))
in (match (uu____6218) with
| true -> begin
(

let uu____6238 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right uu____6238 (fun _0_22 -> FStar_Pervasives_Native.Some (_0_22))))
end
| uu____6241 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____6242 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (

let success = (fun d r t11 t21 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (((t11), (t21)))
end
| uu____6290 -> begin
FStar_Pervasives_Native.None
end))))
in (

let fail1 = (fun r -> ((r), (FStar_Pervasives_Native.None)))
in (

let rec aux = (fun retry n_delta t11 t21 -> (

let r = (head_matches env t11 t21)
in (match (r) with
| MisMatch (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational), uu____6363) -> begin
(match ((not (retry))) with
| true -> begin
(fail1 r)
end
| uu____6380 -> begin
(

let uu____6381 = (

let uu____6390 = (maybe_inline t11)
in (

let uu____6393 = (maybe_inline t21)
in ((uu____6390), (uu____6393))))
in (match (uu____6381) with
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
| MisMatch (uu____6430, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational)) -> begin
(match ((not (retry))) with
| true -> begin
(fail1 r)
end
| uu____6447 -> begin
(

let uu____6448 = (

let uu____6457 = (maybe_inline t11)
in (

let uu____6460 = (maybe_inline t21)
in ((uu____6457), (uu____6460))))
in (match (uu____6448) with
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

let uu____6503 = (FStar_TypeChecker_Common.decr_delta_depth d1)
in (match (uu____6503) with
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

let uu____6526 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env wl t11)
in ((t1'), (t21)))
end
| uu____6536 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env wl t21)
in ((t11), (t2')))
end)
in (match (uu____6526) with
| (t12, t22) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
end)))
end
| MisMatch (uu____6550) -> begin
(fail1 r)
end
| uu____6559 -> begin
(success n_delta r t11 t21)
end)))
in (

let r = (aux true (Prims.parse_int "0") t1 t2)
in ((

let uu____6572 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelDelta")))
in (match (uu____6572) with
| true -> begin
(

let uu____6573 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6574 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____6575 = (string_of_match_result (FStar_Pervasives_Native.fst r))
in (FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6573 uu____6574 uu____6575))))
end
| uu____6582 -> begin
()
end));
r;
)))))))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____6593 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____6593 FStar_Pervasives_Native.fst)))


let rank_t_num : FStar_TypeChecker_Common.rank_t  ->  Prims.int = (fun uu___110_6606 -> (match (uu___110_6606) with
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

let uu___135_6643 = p
in (

let uu____6646 = (whnf tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____6647 = (whnf tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___135_6643.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____6646; FStar_TypeChecker_Common.relation = uu___135_6643.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____6647; FStar_TypeChecker_Common.element = uu___135_6643.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___135_6643.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___135_6643.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___135_6643.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___135_6643.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___135_6643.FStar_TypeChecker_Common.rank}))))


let compress_prob : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun tcenv p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p1) -> begin
(

let uu____6661 = (compress_tprob tcenv p1)
in (FStar_All.pipe_right uu____6661 (fun _0_23 -> FStar_TypeChecker_Common.TProb (_0_23))))
end
| FStar_TypeChecker_Common.CProb (uu____6666) -> begin
p
end))


let rank : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob) = (fun tcenv pr -> (

let prob = (

let uu____6688 = (compress_prob tcenv pr)
in (FStar_All.pipe_right uu____6688 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____6696 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____6696) with
| (lh, lhs_args) -> begin
(

let uu____6737 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____6737) with
| (rh, rhs_args) -> begin
(

let uu____6778 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____6791), FStar_Syntax_Syntax.Tm_uvar (uu____6792)) -> begin
(match (((lhs_args), (rhs_args))) with
| ([], []) when (Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
((FStar_TypeChecker_Common.Flex_flex_pattern_eq), (tp))
end
| uu____6845 -> begin
((FStar_TypeChecker_Common.Flex_flex), (tp))
end)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____6868), uu____6869) when ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((FStar_TypeChecker_Common.Flex_rigid_eq), (tp))
end
| (uu____6872, FStar_Syntax_Syntax.Tm_uvar (uu____6873)) when ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((FStar_TypeChecker_Common.Flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____6876), FStar_Syntax_Syntax.Tm_type (uu____6877)) -> begin
((FStar_TypeChecker_Common.Flex_rigid_eq), ((

let uu___136_6881 = tp
in {FStar_TypeChecker_Common.pid = uu___136_6881.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___136_6881.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___136_6881.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___136_6881.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___136_6881.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___136_6881.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___136_6881.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___136_6881.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___136_6881.FStar_TypeChecker_Common.rank})))
end
| (FStar_Syntax_Syntax.Tm_type (uu____6884), FStar_Syntax_Syntax.Tm_uvar (uu____6885)) -> begin
((FStar_TypeChecker_Common.Flex_rigid_eq), ((

let uu___136_6889 = tp
in {FStar_TypeChecker_Common.pid = uu___136_6889.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___136_6889.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___136_6889.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___136_6889.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___136_6889.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___136_6889.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___136_6889.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___136_6889.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___136_6889.FStar_TypeChecker_Common.rank})))
end
| (uu____6892, FStar_Syntax_Syntax.Tm_uvar (uu____6893)) -> begin
((FStar_TypeChecker_Common.Rigid_flex), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____6896), uu____6897) -> begin
((FStar_TypeChecker_Common.Flex_rigid), (tp))
end
| (uu____6900, FStar_Syntax_Syntax.Tm_uvar (uu____6901)) -> begin
((FStar_TypeChecker_Common.Rigid_flex), (tp))
end
| (uu____6904, uu____6905) -> begin
((FStar_TypeChecker_Common.Rigid_rigid), (tp))
end)
in (match (uu____6778) with
| (rank, tp1) -> begin
(

let uu____6918 = (FStar_All.pipe_right (

let uu___137_6922 = tp1
in {FStar_TypeChecker_Common.pid = uu___137_6922.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___137_6922.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___137_6922.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___137_6922.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___137_6922.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___137_6922.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___137_6922.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___137_6922.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___137_6922.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rank)}) (fun _0_24 -> FStar_TypeChecker_Common.TProb (_0_24)))
in ((rank), (uu____6918)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____6928 = (FStar_All.pipe_right (

let uu___138_6932 = cp
in {FStar_TypeChecker_Common.pid = uu___138_6932.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___138_6932.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___138_6932.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___138_6932.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___138_6932.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___138_6932.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___138_6932.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___138_6932.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___138_6932.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (FStar_TypeChecker_Common.Rigid_rigid)}) (fun _0_25 -> FStar_TypeChecker_Common.CProb (_0_25)))
in ((FStar_TypeChecker_Common.Rigid_rigid), (uu____6928)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option = (fun wl -> (

let rec aux = (fun uu____6993 probs -> (match (uu____6993) with
| (min_rank, min1, out) -> begin
(match (probs) with
| [] -> begin
(match (((min1), (min_rank))) with
| (FStar_Pervasives_Native.Some (p), FStar_Pervasives_Native.Some (r)) -> begin
FStar_Pervasives_Native.Some (((p), (out), (r)))
end
| uu____7074 -> begin
FStar_Pervasives_Native.None
end)
end
| (hd1)::tl1 -> begin
(

let uu____7095 = (rank wl.tcenv hd1)
in (match (uu____7095) with
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
| uu____7153 -> begin
(

let uu____7154 = ((Prims.op_Equality min_rank FStar_Pervasives_Native.None) || (

let uu____7158 = (FStar_Option.get min_rank)
in (rank_less_than rank1 uu____7158)))
in (match (uu____7154) with
| true -> begin
(match (min1) with
| FStar_Pervasives_Native.None -> begin
(aux ((FStar_Pervasives_Native.Some (rank1)), (FStar_Pervasives_Native.Some (hd2)), (out)) tl1)
end
| FStar_Pervasives_Native.Some (m) -> begin
(aux ((FStar_Pervasives_Native.Some (rank1)), (FStar_Pervasives_Native.Some (hd2)), ((m)::out)) tl1)
end)
end
| uu____7192 -> begin
(aux ((min_rank), (min1), ((hd2)::out)) tl1)
end))
end)
end))
end)
end))
in (aux ((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), ([])) wl.attempting)))


let flex_prob_closing : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun tcenv bs p -> (

let flex_will_be_closed = (fun t -> (

let uu____7230 = (destruct_flex_t t)
in (match (uu____7230) with
| (uu____7231, u, uu____7233) -> begin
(FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders (FStar_Util.for_some (fun uu____7247 -> (match (uu____7247) with
| (y, uu____7253) -> begin
(FStar_All.pipe_right bs (FStar_Util.for_some (fun uu____7267 -> (match (uu____7267) with
| (x, uu____7273) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end))))
end))))
end)))
in (

let uu____7274 = (rank tcenv p)
in (match (uu____7274) with
| (r, p1) -> begin
(match (p1) with
| FStar_TypeChecker_Common.CProb (uu____7281) -> begin
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
((flex_will_be_closed p2.FStar_TypeChecker_Common.lhs) || (flex_will_be_closed p2.FStar_TypeChecker_Common.rhs))
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
| uu____7308 -> begin
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
| uu____7322 -> begin
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
| uu____7336 -> begin
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

let uu____7388 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____7388) with
| (k, uu____7394) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Syntax_Unionfind.univ_equiv v1 v2)
end
| uu____7404 -> begin
false
end)
end)))))
end
| uu____7405 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (

let rec filter_out_common_univs = (fun u12 u22 -> (

let common_elts = (FStar_All.pipe_right u12 (FStar_List.fold_left (fun uvs uv1 -> (

let uu____7457 = (FStar_All.pipe_right u22 (FStar_List.existsML (fun uv2 -> (

let uu____7463 = (FStar_Syntax_Util.compare_univs uv1 uv2)
in (Prims.op_Equality uu____7463 (Prims.parse_int "0"))))))
in (match (uu____7457) with
| true -> begin
(uv1)::uvs
end
| uu____7466 -> begin
uvs
end))) []))
in (

let filter1 = (FStar_List.filter (fun u -> (

let uu____7479 = (FStar_All.pipe_right common_elts (FStar_List.existsML (fun u' -> (

let uu____7485 = (FStar_Syntax_Util.compare_univs u u')
in (Prims.op_Equality uu____7485 (Prims.parse_int "0"))))))
in (not (uu____7479)))))
in (

let uu____7486 = (filter1 u12)
in (

let uu____7489 = (filter1 u22)
in ((uu____7486), (uu____7489)))))))
in (

let try_umax_components = (fun u12 u22 msg -> (match (((u12), (u22))) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(

let uu____7518 = (filter_out_common_univs us1 us2)
in (match (uu____7518) with
| (us11, us21) -> begin
(match ((Prims.op_Equality (FStar_List.length us11) (FStar_List.length us21))) with
| true -> begin
(

let rec aux = (fun wl1 us12 us22 -> (match (((us12), (us22))) with
| ((u13)::us13, (u23)::us23) -> begin
(

let uu____7577 = (really_solve_universe_eq pid_orig wl1 u13 u23)
in (match (uu____7577) with
| USolved (wl2) -> begin
(aux wl2 us13 us23)
end
| failed -> begin
failed
end))
end
| uu____7580 -> begin
USolved (wl1)
end))
in (aux wl us11 us21))
end
| uu____7589 -> begin
(

let uu____7590 = (

let uu____7591 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____7592 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" uu____7591 uu____7592)))
in UFailed (uu____7590))
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

let uu____7616 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____7616) with
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

let uu____7642 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____7642) with
| USolved (wl2) -> begin
(aux wl2 us2)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____7645 -> begin
(

let uu____7650 = (

let uu____7651 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____7652 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" uu____7651 uu____7652 msg)))
in UFailed (uu____7650))
end))
in (match (((u11), (u21))) with
| (FStar_Syntax_Syntax.U_bvar (uu____7653), uu____7654) -> begin
(

let uu____7655 = (

let uu____7656 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____7657 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____7656 uu____7657)))
in (failwith uu____7655))
end
| (FStar_Syntax_Syntax.U_unknown, uu____7658) -> begin
(

let uu____7659 = (

let uu____7660 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____7661 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____7660 uu____7661)))
in (failwith uu____7659))
end
| (uu____7662, FStar_Syntax_Syntax.U_bvar (uu____7663)) -> begin
(

let uu____7664 = (

let uu____7665 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____7666 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____7665 uu____7666)))
in (failwith uu____7664))
end
| (uu____7667, FStar_Syntax_Syntax.U_unknown) -> begin
(

let uu____7668 = (

let uu____7669 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____7670 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____7669 uu____7670)))
in (failwith uu____7668))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____7673 -> begin
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

let uu____7694 = (FStar_Syntax_Unionfind.univ_equiv v1 v2)
in (match (uu____7694) with
| true -> begin
USolved (wl)
end
| uu____7695 -> begin
(

let wl1 = (extend_solution pid_orig ((UNIV (((v1), (u21))))::[]) wl)
in USolved (wl1))
end))
end
| (FStar_Syntax_Syntax.U_unif (v1), u) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____7708 = (occurs_univ v1 u3)
in (match (uu____7708) with
| true -> begin
(

let uu____7709 = (

let uu____7710 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____7711 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____7710 uu____7711)))
in (try_umax_components u11 u21 uu____7709))
end
| uu____7712 -> begin
(

let uu____7713 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____7713))
end)))
end
| (u, FStar_Syntax_Syntax.U_unif (v1)) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____7725 = (occurs_univ v1 u3)
in (match (uu____7725) with
| true -> begin
(

let uu____7726 = (

let uu____7727 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____7728 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____7727 uu____7728)))
in (try_umax_components u11 u21 uu____7726))
end
| uu____7729 -> begin
(

let uu____7730 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____7730))
end)))
end
| (FStar_Syntax_Syntax.U_max (uu____7731), uu____7732) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____7735 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____7738 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____7738) with
| true -> begin
USolved (wl)
end
| uu____7739 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (uu____7740, FStar_Syntax_Syntax.U_max (uu____7741)) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____7744 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____7747 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____7747) with
| true -> begin
USolved (wl)
end
| uu____7748 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (FStar_Syntax_Syntax.U_succ (uu____7749), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_succ (uu____7750), FStar_Syntax_Syntax.U_name (uu____7751)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ (uu____7752)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name (uu____7753)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____7754), FStar_Syntax_Syntax.U_succ (uu____7755)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____7756), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end)))))))


let solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (match (wl.tcenv.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
USolved (wl)
end
| uu____7777 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders : 'a 'b . ('a Prims.list * ('a Prims.list  ->  'b))  ->  ('a Prims.list * ('a Prims.list  ->  'b))  ->  (('a Prims.list * 'b) * ('a Prims.list * 'b)) = (fun bc1 bc2 -> (

let uu____7856 = bc1
in (match (uu____7856) with
| (bs1, mk_cod1) -> begin
(

let uu____7900 = bc2
in (match (uu____7900) with
| (bs2, mk_cod2) -> begin
(

let rec aux = (fun bs11 bs21 -> (match (((bs11), (bs21))) with
| ((x)::xs, (y)::ys) -> begin
(

let uu____8011 = (aux xs ys)
in (match (uu____8011) with
| ((xs1, xr), (ys1, yr)) -> begin
(((((x)::xs1), (xr))), ((((y)::ys1), (yr))))
end))
end
| (xs, ys) -> begin
(

let uu____8094 = (

let uu____8101 = (mk_cod1 xs)
in (([]), (uu____8101)))
in (

let uu____8104 = (

let uu____8111 = (mk_cod2 ys)
in (([]), (uu____8111)))
in ((uu____8094), (uu____8104))))
end))
in (aux bs1 bs2))
end))
end)))


let is_flex_pat : 'Auu____8134 'Auu____8135 'Auu____8136 . ('Auu____8134 * 'Auu____8135 * 'Auu____8136 Prims.list)  ->  Prims.bool = (fun uu___111_8149 -> (match (uu___111_8149) with
| (uu____8158, uu____8159, []) -> begin
true
end
| uu____8162 -> begin
false
end))


let quasi_pattern : FStar_TypeChecker_Env.env  ->  flex_t  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ) FStar_Pervasives_Native.option = (fun env f -> (

let uu____8193 = f
in (match (uu____8193) with
| (uu____8200, {FStar_Syntax_Syntax.ctx_uvar_head = uu____8201; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____8202; FStar_Syntax_Syntax.ctx_uvar_binders = ctx; FStar_Syntax_Syntax.ctx_uvar_typ = t_hd; FStar_Syntax_Syntax.ctx_uvar_reason = uu____8205; FStar_Syntax_Syntax.ctx_uvar_should_check = uu____8206; FStar_Syntax_Syntax.ctx_uvar_range = uu____8207}, args) -> begin
(

let name_exists_in = (fun x bs -> (FStar_Util.for_some (fun uu____8259 -> (match (uu____8259) with
| (y, uu____8265) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end)) bs))
in (

let rec aux = (fun pat_binders formals t_res args1 -> (match (((formals), (args1))) with
| ([], []) -> begin
(

let uu____8371 = (

let uu____8380 = (

let uu____8383 = (FStar_Syntax_Syntax.mk_Total t_res)
in (FStar_Syntax_Util.arrow formals uu____8383))
in (((FStar_List.rev pat_binders)), (uu____8380)))
in FStar_Pervasives_Native.Some (uu____8371))
end
| (uu____8398, []) -> begin
(

let uu____8421 = (

let uu____8430 = (

let uu____8433 = (FStar_Syntax_Syntax.mk_Total t_res)
in (FStar_Syntax_Util.arrow formals uu____8433))
in (((FStar_List.rev pat_binders)), (uu____8430)))
in FStar_Pervasives_Native.Some (uu____8421))
end
| (((formal, uu____8449))::formals1, ((a, uu____8452))::args2) -> begin
(

let uu____8486 = (

let uu____8487 = (FStar_Syntax_Subst.compress a)
in uu____8487.FStar_Syntax_Syntax.n)
in (match (uu____8486) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____8501 = ((name_exists_in x ctx) || (name_exists_in x pat_binders))
in (match (uu____8501) with
| true -> begin
(

let uu____8512 = (

let uu____8515 = (FStar_Syntax_Syntax.mk_binder formal)
in (uu____8515)::pat_binders)
in (aux uu____8512 formals1 t_res args2))
end
| uu____8516 -> begin
(

let x1 = (

let uu___139_8518 = x
in {FStar_Syntax_Syntax.ppname = uu___139_8518.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___139_8518.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = formal.FStar_Syntax_Syntax.sort})
in (

let subst1 = (

let uu____8522 = (

let uu____8523 = (

let uu____8530 = (FStar_Syntax_Syntax.bv_to_name x1)
in ((formal), (uu____8530)))
in FStar_Syntax_Syntax.NT (uu____8523))
in (uu____8522)::[])
in (

let formals2 = (FStar_Syntax_Subst.subst_binders subst1 formals1)
in (

let t_res1 = (FStar_Syntax_Subst.subst subst1 t_res)
in (

let uu____8537 = (

let uu____8540 = (FStar_Syntax_Syntax.mk_binder (

let uu___140_8543 = x1
in {FStar_Syntax_Syntax.ppname = uu___140_8543.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___140_8543.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = formal.FStar_Syntax_Syntax.sort}))
in (uu____8540)::pat_binders)
in (aux uu____8537 formals2 t_res1 args2))))))
end))
end
| uu____8544 -> begin
(

let uu____8545 = (

let uu____8548 = (FStar_Syntax_Syntax.mk_binder formal)
in (uu____8548)::pat_binders)
in (aux uu____8545 formals1 t_res args2))
end))
end
| ([], args2) -> begin
(

let uu____8572 = (

let uu____8585 = (FStar_TypeChecker_Normalize.unfold_whnf env t_res)
in (FStar_Syntax_Util.arrow_formals uu____8585))
in (match (uu____8572) with
| (more_formals, t_res1) -> begin
(match (more_formals) with
| [] -> begin
FStar_Pervasives_Native.None
end
| uu____8636 -> begin
(aux pat_binders more_formals t_res1 args2)
end)
end))
end))
in (match (args) with
| [] -> begin
FStar_Pervasives_Native.Some ((([]), (t_hd)))
end
| uu____8663 -> begin
(

let uu____8664 = (FStar_Syntax_Util.arrow_formals t_hd)
in (match (uu____8664) with
| (formals, t_res) -> begin
(aux [] formals t_res args)
end))
end)))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____8936 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____8936) with
| true -> begin
(

let uu____8937 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" uu____8937))
end
| uu____8938 -> begin
()
end));
(

let uu____8939 = (next_prob probs)
in (match (uu____8939) with
| FStar_Pervasives_Native.Some (hd1, tl1, rank1) -> begin
(

let probs1 = (

let uu___141_8966 = probs
in {attempting = tl1; wl_deferred = uu___141_8966.wl_deferred; ctr = uu___141_8966.ctr; defer_ok = uu___141_8966.defer_ok; smt_ok = uu___141_8966.smt_ok; tcenv = uu___141_8966.tcenv; wl_implicits = uu___141_8966.wl_implicits})
in (match (hd1) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs1)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____8973 = (FStar_Util.physical_equality tp.FStar_TypeChecker_Common.lhs tp.FStar_TypeChecker_Common.rhs)
in (match (uu____8973) with
| true -> begin
(

let uu____8974 = (solve_prob hd1 FStar_Pervasives_Native.None [] probs1)
in (solve env uu____8974))
end
| uu____8975 -> begin
(match (((Prims.op_Equality rank1 FStar_TypeChecker_Common.Rigid_rigid) || ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) && (Prims.op_disEquality rank1 FStar_TypeChecker_Common.Flex_flex)))) with
| true -> begin
(solve_t' env tp probs1)
end
| uu____8976 -> begin
(match (probs1.defer_ok) with
| true -> begin
(solve env (defer "deferring flex_rigid or flex_flex subtyping" hd1 probs1))
end
| uu____8977 -> begin
(match ((Prims.op_Equality rank1 FStar_TypeChecker_Common.Flex_flex)) with
| true -> begin
(solve_t' env (

let uu___142_8979 = tp
in {FStar_TypeChecker_Common.pid = uu___142_8979.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___142_8979.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___142_8979.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___142_8979.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___142_8979.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___142_8979.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___142_8979.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___142_8979.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___142_8979.FStar_TypeChecker_Common.rank}) probs1)
end
| uu____8982 -> begin
(solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp probs1)
end)
end)
end)
end))
end))
end
| FStar_Pervasives_Native.None -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ((([]), (probs.wl_implicits)))
end
| uu____9001 -> begin
(

let uu____9010 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____9069 -> (match (uu____9069) with
| (c, uu____9077, uu____9078) -> begin
(c < probs.ctr)
end))))
in (match (uu____9010) with
| (attempt1, rest) -> begin
(match (attempt1) with
| [] -> begin
(

let uu____9119 = (

let uu____9124 = (FStar_List.map (fun uu____9139 -> (match (uu____9139) with
| (uu____9150, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in ((uu____9124), (probs.wl_implicits)))
in Success (uu____9119))
end
| uu____9153 -> begin
(

let uu____9162 = (

let uu___143_9163 = probs
in (

let uu____9164 = (FStar_All.pipe_right attempt1 (FStar_List.map (fun uu____9183 -> (match (uu____9183) with
| (uu____9190, uu____9191, y) -> begin
y
end))))
in {attempting = uu____9164; wl_deferred = rest; ctr = uu___143_9163.ctr; defer_ok = uu___143_9163.defer_ok; smt_ok = uu___143_9163.smt_ok; tcenv = uu___143_9163.tcenv; wl_implicits = uu___143_9163.wl_implicits}))
in (solve env uu____9162))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____9198 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____9198) with
| USolved (wl1) -> begin
(

let uu____9200 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____9200))
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

let uu____9252 = (solve_universe_eq (p_pid orig) wl1 u1 u2)
in (match (uu____9252) with
| USolved (wl2) -> begin
(aux wl2 us11 us21)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____9255 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t11 = (whnf env t1)
in (

let t21 = (whnf env t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.pos = uu____9267; FStar_Syntax_Syntax.vars = uu____9268}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.pos = uu____9271; FStar_Syntax_Syntax.vars = uu____9272}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____9284), uu____9285) -> begin
(failwith "Impossible: expect head symbols to match")
end
| (uu____9292, FStar_Syntax_Syntax.Tm_uinst (uu____9293)) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____9300 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____9310 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9310) with
| true -> begin
(

let uu____9311 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" uu____9311 msg))
end
| uu____9312 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____9313 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_or_flex_rigid_subtyping : FStar_TypeChecker_Common.rank_t  ->  FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun rank1 env tp wl -> (

let flip = (Prims.op_Equality rank1 FStar_TypeChecker_Common.Flex_rigid)
in (

let meet_or_join = (fun op ts env1 wl1 -> (

let eq_prob = (fun t1 t2 wl2 -> (

let uu____9396 = (new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos "join/meet refinements")
in (match (uu____9396) with
| (p, wl3) -> begin
((FStar_TypeChecker_Common.TProb (p)), (wl3))
end)))
in (

let pairwise = (fun t1 t2 wl2 -> ((

let uu____9448 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("RelCheck")))
in (match (uu____9448) with
| true -> begin
(

let uu____9449 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____9450 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "pairwise: %s and %s" uu____9449 uu____9450)))
end
| uu____9451 -> begin
()
end));
(

let uu____9452 = (head_matches_delta env1 () t1 t2)
in (match (uu____9452) with
| (mr, ts1) -> begin
(match (mr) with
| MisMatch (uu____9497) -> begin
(

let uu____9506 = (eq_prob t1 t2 wl2)
in (match (uu____9506) with
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
| HeadMatch -> begin
(

let uu____9553 = (match (ts1) with
| FStar_Pervasives_Native.Some (t11, t21) -> begin
(

let uu____9568 = (FStar_Syntax_Subst.compress t11)
in (

let uu____9569 = (FStar_Syntax_Subst.compress t21)
in ((uu____9568), (uu____9569))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____9574 = (FStar_Syntax_Subst.compress t1)
in (

let uu____9575 = (FStar_Syntax_Subst.compress t2)
in ((uu____9574), (uu____9575))))
end)
in (match (uu____9553) with
| (t11, t21) -> begin
(

let try_eq = (fun t12 t22 wl3 -> (

let uu____9606 = (FStar_Syntax_Util.term_eq t12 t22)
in (match (uu____9606) with
| true -> begin
FStar_Pervasives_Native.Some (wl3)
end
| uu____9609 -> begin
(

let uu____9610 = (FStar_Syntax_Util.head_and_args t12)
in (match (uu____9610) with
| (_t1_hd, t1_args) -> begin
(

let uu____9649 = (FStar_Syntax_Util.head_and_args t22)
in (match (uu____9649) with
| (_t2_hd, t2_args) -> begin
(match ((Prims.op_disEquality (FStar_List.length t1_args) (FStar_List.length t2_args))) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____9702 -> begin
(

let uu____9703 = (FStar_List.fold_left2 (fun uu____9738 uu____9739 uu____9740 -> (match (((uu____9738), (uu____9739), (uu____9740))) with
| ((probs, wl4), (a1, uu____9782), (a2, uu____9784)) -> begin
(

let uu____9809 = (eq_prob a1 a2 wl4)
in (match (uu____9809) with
| (p, wl5) -> begin
(((p)::probs), (wl5))
end))
end)) (([]), (wl3)) t1_args t2_args)
in (match (uu____9703) with
| (probs, wl4) -> begin
(

let wl' = (

let uu___144_9835 = wl4
in {attempting = probs; wl_deferred = []; ctr = uu___144_9835.ctr; defer_ok = false; smt_ok = false; tcenv = uu___144_9835.tcenv; wl_implicits = []})
in (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____9853 = (solve env1 wl')
in (match (uu____9853) with
| Success (uu____9856, imps) -> begin
((FStar_Syntax_Unionfind.commit tx);
FStar_Pervasives_Native.Some ((

let uu___145_9860 = wl4
in {attempting = uu___145_9860.attempting; wl_deferred = uu___145_9860.wl_deferred; ctr = uu___145_9860.ctr; defer_ok = uu___145_9860.defer_ok; smt_ok = uu___145_9860.smt_ok; tcenv = uu___145_9860.tcenv; wl_implicits = (FStar_List.append wl4.wl_implicits imps)}));
)
end
| Failed (uu____9871) -> begin
((FStar_Syntax_Unionfind.rollback tx);
FStar_Pervasives_Native.None;
)
end))))
end))
end)
end))
end))
end)))
in (

let combine = (fun t12 t22 wl3 -> (

let uu____9903 = (FStar_Syntax_Util.term_eq t12 t22)
in (match (uu____9903) with
| true -> begin
((t12), ([]), (wl3))
end
| uu____9918 -> begin
(

let uu____9919 = (base_and_refinement_maybe_delta false env1 t12)
in (match (uu____9919) with
| (t1_base, p1_opt) -> begin
(

let uu____9960 = (base_and_refinement_maybe_delta false env1 t22)
in (match (uu____9960) with
| (t2_base, p2_opt) -> begin
(

let combine_refinements = (fun t_base p1_opt1 p2_opt1 -> (match (((p1_opt1), (p2_opt1))) with
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

let uu____10091 = (op phi11 phi21)
in (FStar_Syntax_Util.refine x1 uu____10091))))))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (x, phi)) -> begin
(

let x1 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let subst1 = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x1))))::[]
in (

let phi1 = (FStar_Syntax_Subst.subst subst1 phi)
in (

let uu____10121 = (op FStar_Syntax_Util.t_true phi1)
in (FStar_Syntax_Util.refine x1 uu____10121)))))
end
| (FStar_Pervasives_Native.Some (x, phi), FStar_Pervasives_Native.None) -> begin
(

let x1 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let subst1 = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x1))))::[]
in (

let phi1 = (FStar_Syntax_Subst.subst subst1 phi)
in (

let uu____10151 = (op FStar_Syntax_Util.t_true phi1)
in (FStar_Syntax_Util.refine x1 uu____10151)))))
end
| uu____10154 -> begin
t_base
end))
in (

let uu____10171 = (try_eq t1_base t2_base wl3)
in (match (uu____10171) with
| FStar_Pervasives_Native.Some (wl4) -> begin
(

let uu____10185 = (combine_refinements t1_base p1_opt p2_opt)
in ((uu____10185), ([]), (wl4)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____10192 = (base_and_refinement_maybe_delta true env1 t12)
in (match (uu____10192) with
| (t1_base1, p1_opt1) -> begin
(

let uu____10233 = (base_and_refinement_maybe_delta true env1 t22)
in (match (uu____10233) with
| (t2_base1, p2_opt1) -> begin
(

let uu____10274 = (eq_prob t1_base1 t2_base1 wl3)
in (match (uu____10274) with
| (p, wl4) -> begin
(

let t = (combine_refinements t1_base1 p1_opt1 p2_opt1)
in ((t), ((p)::[]), (wl4)))
end))
end))
end))
end)))
end))
end))
end)))
in (

let uu____10298 = (combine t11 t21 wl2)
in (match (uu____10298) with
| (t12, ps, wl3) -> begin
((

let uu____10331 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("RelCheck")))
in (match (uu____10331) with
| true -> begin
(

let uu____10332 = (FStar_Syntax_Print.term_to_string t12)
in (FStar_Util.print1 "pairwise fallback2 succeeded: %s" uu____10332))
end
| uu____10333 -> begin
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

let rec aux = (fun uu____10371 ts1 -> (match (uu____10371) with
| (out, probs, wl2) -> begin
(match (ts1) with
| [] -> begin
((out), (probs), (wl2))
end
| (t)::ts2 -> begin
(

let uu____10434 = (pairwise out t wl2)
in (match (uu____10434) with
| (out1, probs', wl3) -> begin
(aux ((out1), ((FStar_List.append probs probs')), (wl3)) ts2)
end))
end)
end))
in (

let uu____10470 = (

let uu____10481 = (FStar_List.hd ts)
in ((uu____10481), ([]), (wl1)))
in (

let uu____10490 = (FStar_List.tl ts)
in (aux uu____10470 uu____10490)))))))
in (

let uu____10497 = (match (flip) with
| true -> begin
((tp.FStar_TypeChecker_Common.lhs), (tp.FStar_TypeChecker_Common.rhs))
end
| uu____10506 -> begin
((tp.FStar_TypeChecker_Common.rhs), (tp.FStar_TypeChecker_Common.lhs))
end)
in (match (uu____10497) with
| (this_flex, this_rigid) -> begin
(

let uu____10509 = (

let uu____10510 = (FStar_Syntax_Subst.compress this_rigid)
in uu____10510.FStar_Syntax_Syntax.n)
in (match (uu____10509) with
| FStar_Syntax_Syntax.Tm_arrow (_bs, comp) -> begin
(

let uu____10531 = (FStar_Syntax_Util.is_tot_or_gtot_comp comp)
in (match (uu____10531) with
| true -> begin
(

let flex = (destruct_flex_t this_flex)
in (

let uu____10533 = (quasi_pattern env flex)
in (match (uu____10533) with
| FStar_Pervasives_Native.None -> begin
(giveup env "flex-arrow subtyping, not a quasi pattern" (FStar_TypeChecker_Common.TProb (tp)))
end
| FStar_Pervasives_Native.Some (flex_bs, flex_t) -> begin
((

let uu____10551 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____10551) with
| true -> begin
(

let uu____10552 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by imitating arrow:%s\n" uu____10552))
end
| uu____10553 -> begin
()
end));
(imitate_arrow (FStar_TypeChecker_Common.TProb (tp)) env wl flex flex_bs flex_t tp.FStar_TypeChecker_Common.relation this_rigid);
)
end)))
end
| uu____10554 -> begin
(solve env (attempt ((FStar_TypeChecker_Common.TProb ((

let uu___146_10557 = tp
in {FStar_TypeChecker_Common.pid = uu___146_10557.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___146_10557.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___146_10557.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___146_10557.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___146_10557.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___146_10557.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___146_10557.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___146_10557.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___146_10557.FStar_TypeChecker_Common.rank})))::[]) wl))
end))
end
| uu____10558 -> begin
((

let uu____10560 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____10560) with
| true -> begin
(

let uu____10561 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" uu____10561))
end
| uu____10562 -> begin
()
end));
(

let uu____10563 = (FStar_Syntax_Util.head_and_args this_flex)
in (match (uu____10563) with
| (u, _args) -> begin
(

let uu____10600 = (

let uu____10601 = (FStar_Syntax_Subst.compress u)
in uu____10601.FStar_Syntax_Syntax.n)
in (match (uu____10600) with
| FStar_Syntax_Syntax.Tm_uvar (ctx_uvar) -> begin
(

let equiv1 = (fun t -> (

let uu____10611 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____10611) with
| (u', uu____10627) -> begin
(

let uu____10648 = (

let uu____10649 = (whnf env u')
in uu____10649.FStar_Syntax_Syntax.n)
in (match (uu____10648) with
| FStar_Syntax_Syntax.Tm_uvar (ctx_uvar') -> begin
(FStar_Syntax_Unionfind.equiv ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head)
end
| uu____10653 -> begin
false
end))
end)))
in (

let uu____10654 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___112_10677 -> (match (uu___112_10677) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(

let tp2 = (maybe_invert tp1)
in (match (tp2.FStar_TypeChecker_Common.rank) with
| FStar_Pervasives_Native.Some (rank') when (Prims.op_Equality rank1 rank') -> begin
(match (flip) with
| true -> begin
(equiv1 tp2.FStar_TypeChecker_Common.lhs)
end
| uu____10685 -> begin
(equiv1 tp2.FStar_TypeChecker_Common.rhs)
end)
end
| uu____10686 -> begin
false
end))
end
| uu____10689 -> begin
false
end))))
in (match (uu____10654) with
| (bounds_probs, rest) -> begin
(

let bounds_typs = (

let uu____10703 = (whnf env this_rigid)
in (

let uu____10704 = (FStar_List.collect (fun uu___113_10710 -> (match (uu___113_10710) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____10716 = (match (flip) with
| true -> begin
(whnf env (maybe_invert p).FStar_TypeChecker_Common.rhs)
end
| uu____10717 -> begin
(whnf env (maybe_invert p).FStar_TypeChecker_Common.lhs)
end)
in (uu____10716)::[])
end
| uu____10718 -> begin
[]
end)) bounds_probs)
in (uu____10703)::uu____10704))
in (

let uu____10719 = (meet_or_join (match (flip) with
| true -> begin
FStar_Syntax_Util.mk_conj
end
| uu____10738 -> begin
FStar_Syntax_Util.mk_disj
end) bounds_typs env wl)
in (match (uu____10719) with
| (bound, sub_probs, wl1) -> begin
(

let uu____10750 = (

let uu____10757 = (destruct_flex_t this_flex)
in (match (uu____10757) with
| (uu____10764, flex_u, uu____10766) -> begin
(

let bound1 = (

let uu____10768 = (

let uu____10769 = (FStar_Syntax_Subst.compress bound)
in uu____10769.FStar_Syntax_Syntax.n)
in (match (uu____10768) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) when ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB) && (

let uu____10779 = (occurs flex_u x.FStar_Syntax_Syntax.sort)
in (FStar_Pervasives_Native.snd uu____10779))) -> begin
x.FStar_Syntax_Syntax.sort
end
| uu____10788 -> begin
bound
end))
in (new_problem wl1 env bound1 FStar_TypeChecker_Common.EQ this_flex FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc (match (flip) with
| true -> begin
"joining refinements"
end
| uu____10789 -> begin
"meeting refinements"
end)))
end))
in (match (uu____10750) with
| (eq_prob, wl2) -> begin
((

let uu____10797 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____10797) with
| true -> begin
(

let wl' = (

let uu___147_10799 = wl2
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___147_10799.wl_deferred; ctr = uu___147_10799.ctr; defer_ok = uu___147_10799.defer_ok; smt_ok = uu___147_10799.smt_ok; tcenv = uu___147_10799.tcenv; wl_implicits = uu___147_10799.wl_implicits})
in (

let uu____10800 = (wl_to_string wl')
in (FStar_Util.print1 "After meet/join refinements: %s\n" uu____10800)))
end
| uu____10801 -> begin
()
end));
(

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____10803 = (solve_t env eq_prob (

let uu___148_10805 = wl2
in {attempting = sub_probs; wl_deferred = uu___148_10805.wl_deferred; ctr = uu___148_10805.ctr; defer_ok = uu___148_10805.defer_ok; smt_ok = uu___148_10805.smt_ok; tcenv = uu___148_10805.tcenv; wl_implicits = uu___148_10805.wl_implicits}))
in (match (uu____10803) with
| Success (uu____10806) -> begin
(

let wl3 = (

let uu___149_10812 = wl2
in {attempting = rest; wl_deferred = uu___149_10812.wl_deferred; ctr = uu___149_10812.ctr; defer_ok = uu___149_10812.defer_ok; smt_ok = uu___149_10812.smt_ok; tcenv = uu___149_10812.tcenv; wl_implicits = uu___149_10812.wl_implicits})
in (

let wl4 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) FStar_Pervasives_Native.None [] wl3)
in (

let uu____10816 = (FStar_List.fold_left (fun wl5 p -> (solve_prob' true p FStar_Pervasives_Native.None [] wl5)) wl4 bounds_probs)
in ((FStar_Syntax_Unionfind.commit tx);
(solve env wl4);
))))
end
| Failed (p, msg) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(giveup env (Prims.strcat "failed to solve sub-problems: " msg) p);
)
end)));
)
end))
end)))
end)))
end
| uu____10827 when flip -> begin
(

let uu____10828 = (

let uu____10829 = (prob_to_string env (FStar_TypeChecker_Common.TProb (tp)))
in (FStar_Util.format1 "Impossible: Not a flex-rigid: %s" uu____10829))
in (failwith uu____10828))
end
| uu____10830 -> begin
(

let uu____10831 = (

let uu____10832 = (prob_to_string env (FStar_TypeChecker_Common.TProb (tp)))
in (FStar_Util.format1 "Impossible: Not a rigid-flex: %s" uu____10832))
in (failwith uu____10831))
end))
end));
)
end))
end)))))
and imitate_arrow : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Env.env  ->  worklist  ->  flex_t  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  solution = (fun orig env wl lhs bs_lhs t_res_lhs rel arrow1 -> (

let bs_lhs_args = (FStar_List.map (fun uu____10860 -> (match (uu____10860) with
| (x, i) -> begin
(

let uu____10871 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____10871), (i)))
end)) bs_lhs)
in (

let uu____10872 = lhs
in (match (uu____10872) with
| (uu____10873, u_lhs, uu____10875) -> begin
(

let imitate_comp = (fun bs bs_terms c wl1 -> (

let imitate_tot_or_gtot = (fun t uopt f wl2 -> (

let uu____10988 = (match (uopt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Util.type_u ())
end
| FStar_Pervasives_Native.Some (univ) -> begin
(

let uu____10998 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (univ)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in ((uu____10998), (univ)))
end)
in (match (uu____10988) with
| (k, univ) -> begin
(

let uu____11011 = (

let uu____11018 = (

let uu____11021 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow (FStar_List.append bs_lhs bs) uu____11021))
in (copy_uvar u_lhs uu____11018 wl2))
in (match (uu____11011) with
| (uu____11034, u, wl3) -> begin
(

let uu____11037 = (

let uu____11040 = (FStar_Syntax_Syntax.mk_Tm_app u (FStar_List.append bs_lhs_args bs_terms) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in (f uu____11040 (FStar_Pervasives_Native.Some (univ))))
in ((uu____11037), (wl3)))
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

let uu____11076 = (

let uu____11089 = (

let uu____11098 = (FStar_Syntax_Syntax.as_arg ct.FStar_Syntax_Syntax.result_typ)
in (uu____11098)::ct.FStar_Syntax_Syntax.effect_args)
in (FStar_List.fold_right (fun uu____11144 uu____11145 -> (match (((uu____11144), (uu____11145))) with
| ((a, i), (out_args, wl2)) -> begin
(

let uu____11236 = (

let uu____11243 = (

let uu____11246 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11246))
in (copy_uvar u_lhs uu____11243 wl2))
in (match (uu____11236) with
| (uu____11269, t_a, wl3) -> begin
(

let uu____11272 = (

let uu____11279 = (

let uu____11282 = (FStar_Syntax_Syntax.mk_Total t_a)
in (FStar_Syntax_Util.arrow bs uu____11282))
in (copy_uvar u_lhs uu____11279 wl3))
in (match (uu____11272) with
| (uu____11297, a', wl4) -> begin
(

let a'1 = (FStar_Syntax_Syntax.mk_Tm_app a' bs_terms FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos)
in (((((a'1), (i)))::out_args), (wl4)))
end))
end))
end)) uu____11089 (([]), (wl1))))
in (match (uu____11076) with
| (out_args, wl2) -> begin
(

let ct' = (

let uu___150_11358 = ct
in (

let uu____11359 = (

let uu____11362 = (FStar_List.hd out_args)
in (FStar_Pervasives_Native.fst uu____11362))
in (

let uu____11377 = (FStar_List.tl out_args)
in {FStar_Syntax_Syntax.comp_univs = uu___150_11358.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___150_11358.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____11359; FStar_Syntax_Syntax.effect_args = uu____11377; FStar_Syntax_Syntax.flags = uu___150_11358.FStar_Syntax_Syntax.flags})))
in (((

let uu___151_11395 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct'); FStar_Syntax_Syntax.pos = uu___151_11395.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___151_11395.FStar_Syntax_Syntax.vars})), (wl2)))
end))
end)))
in (

let uu____11398 = (FStar_Syntax_Util.arrow_formals_comp arrow1)
in (match (uu____11398) with
| (formals, c) -> begin
(

let rec aux = (fun bs bs_terms formals1 wl1 -> (match (formals1) with
| [] -> begin
(

let uu____11452 = (imitate_comp bs bs_terms c wl1)
in (match (uu____11452) with
| (c', wl2) -> begin
(

let lhs' = (FStar_Syntax_Util.arrow bs c')
in (

let sol = (

let uu____11469 = (

let uu____11474 = (FStar_Syntax_Util.abs bs_lhs lhs' (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot t_res_lhs))))
in ((u_lhs), (uu____11474)))
in TERM (uu____11469))
in (

let uu____11475 = (mk_t_problem wl2 [] orig lhs' rel arrow1 FStar_Pervasives_Native.None "arrow imitation")
in (match (uu____11475) with
| (sub_prob, wl3) -> begin
(

let uu____11486 = (

let uu____11487 = (solve_prob orig FStar_Pervasives_Native.None ((sol)::[]) wl3)
in (attempt ((sub_prob)::[]) uu____11487))
in (solve env uu____11486))
end))))
end))
end
| ((x, imp))::formals2 -> begin
(

let uu____11501 = (

let uu____11508 = (

let uu____11511 = (

let uu____11514 = (

let uu____11515 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____11515 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.mk_Total uu____11514))
in (FStar_Syntax_Util.arrow (FStar_List.append bs_lhs bs) uu____11511))
in (copy_uvar u_lhs uu____11508 wl1))
in (match (uu____11501) with
| (_ctx_u_x, u_x, wl2) -> begin
(

let t_y = (FStar_Syntax_Syntax.mk_Tm_app u_x (FStar_List.append bs_lhs_args bs_terms) FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos)
in (

let y = (

let uu____11539 = (

let uu____11542 = (FStar_Syntax_Syntax.range_of_bv x)
in FStar_Pervasives_Native.Some (uu____11542))
in (FStar_Syntax_Syntax.new_bv uu____11539 t_y))
in (

let uu____11543 = (

let uu____11546 = (

let uu____11549 = (

let uu____11550 = (FStar_Syntax_Syntax.bv_to_name y)
in ((uu____11550), (imp)))
in (uu____11549)::[])
in (FStar_List.append bs_terms uu____11546))
in (aux (FStar_List.append bs ((((y), (imp)))::[])) uu____11543 formals2 wl2))))
end))
end))
in (aux [] [] formals wl))
end)))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (worklist  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  (FStar_TypeChecker_Common.prob * worklist))  ->  solution = (fun env bs1 bs2 orig wl rhs -> ((

let uu____11592 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11592) with
| true -> begin
(

let uu____11593 = (FStar_Syntax_Print.binders_to_string ", " bs1)
in (

let uu____11594 = (FStar_Syntax_Print.binders_to_string ", " bs2)
in (FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n" uu____11593 (rel_to_string (p_rel orig)) uu____11594)))
end
| uu____11595 -> begin
()
end));
(

let rec aux = (fun wl1 scope env1 subst1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
(

let uu____11699 = (rhs wl1 scope env1 subst1)
in (match (uu____11699) with
| (rhs_prob, wl2) -> begin
((

let uu____11719 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____11719) with
| true -> begin
(

let uu____11720 = (prob_to_string env1 rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" uu____11720))
end
| uu____11721 -> begin
()
end));
(

let formula = (p_guard rhs_prob)
in ((FStar_Util.Inl ((((rhs_prob)::[]), (formula)))), (wl2)));
)
end))
end
| (((hd1, imp))::xs1, ((hd2, imp'))::ys1) when (Prims.op_Equality imp imp') -> begin
(

let hd11 = (

let uu___152_11774 = hd1
in (

let uu____11775 = (FStar_Syntax_Subst.subst subst1 hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___152_11774.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___152_11774.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____11775}))
in (

let hd21 = (

let uu___153_11779 = hd2
in (

let uu____11780 = (FStar_Syntax_Subst.subst subst1 hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___153_11779.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___153_11779.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____11780}))
in (

let uu____11783 = (

let uu____11788 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_t_problem wl1 scope orig hd11.FStar_Syntax_Syntax.sort uu____11788 hd21.FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None "Formal parameter"))
in (match (uu____11783) with
| (prob, wl2) -> begin
(

let hd12 = (FStar_Syntax_Syntax.freshen_bv hd11)
in (

let subst2 = (

let uu____11807 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd12))))::uu____11807)
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 hd12)
in (

let uu____11811 = (aux wl2 (FStar_List.append scope ((((hd12), (imp)))::[])) env2 subst2 xs1 ys1)
in (match (uu____11811) with
| (FStar_Util.Inl (sub_probs, phi), wl3) -> begin
(

let phi1 = (

let uu____11866 = (close_forall env2 ((((hd12), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj (p_guard prob) uu____11866))
in ((

let uu____11878 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____11878) with
| true -> begin
(

let uu____11879 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____11880 = (FStar_Syntax_Print.bv_to_string hd12)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" uu____11879 uu____11880)))
end
| uu____11881 -> begin
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
| uu____11907 -> begin
((FStar_Util.Inr ("arity or argument-qualifier mismatch")), (wl1))
end))
in (

let uu____11936 = (aux wl [] env [] bs1 bs2)
in (match (uu____11936) with
| (FStar_Util.Inr (msg), wl1) -> begin
(giveup env msg orig)
end
| (FStar_Util.Inl (sub_probs, phi), wl1) -> begin
(

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some (phi)) [] wl1)
in (solve env (attempt sub_probs wl2)))
end)));
))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> ((def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb (problem)));
(

let uu____11987 = (compress_tprob wl.tcenv problem)
in (solve_t' env uu____11987 wl));
))
and solve_t_flex_rigid_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  flex_t  ->  FStar_Syntax_Syntax.term  ->  solution = (fun env orig wl lhs rhs -> (

let binders_as_bv_set = (fun bs -> (

let uu____12001 = (FStar_List.map FStar_Pervasives_Native.fst bs)
in (FStar_Util.as_set uu____12001 FStar_Syntax_Syntax.order_bv)))
in (

let mk_solution = (fun env1 lhs1 bs rhs1 -> (

let uu____12031 = lhs1
in (match (uu____12031) with
| (uu____12034, ctx_u, uu____12036) -> begin
(

let sol = (match (bs) with
| [] -> begin
rhs1
end
| uu____12042 -> begin
(

let uu____12043 = (sn_binders env1 bs)
in (u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ uu____12043 rhs1))
end)
in (TERM (((ctx_u), (sol))))::[])
end)))
in (

let try_quasi_pattern = (fun orig1 env1 wl1 lhs1 rhs1 -> (

let uu____12090 = (quasi_pattern env1 lhs1)
in (match (uu____12090) with
| FStar_Pervasives_Native.None -> begin
((FStar_Util.Inl ("Not a quasi-pattern")), (wl1))
end
| FStar_Pervasives_Native.Some (bs, uu____12120) -> begin
(

let uu____12125 = lhs1
in (match (uu____12125) with
| (t_lhs, ctx_u, args) -> begin
(

let uu____12139 = (occurs_check ctx_u rhs1)
in (match (uu____12139) with
| (uvars1, occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____12181 = (

let uu____12188 = (

let uu____12189 = (FStar_Option.get msg)
in (Prims.strcat "quasi-pattern, occurs-check failed: " uu____12189))
in FStar_Util.Inl (uu____12188))
in ((uu____12181), (wl1)))
end
| uu____12198 -> begin
(

let fvs_lhs = (binders_as_bv_set (FStar_List.append ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders bs))
in (

let fvs_rhs = (FStar_Syntax_Free.names rhs1)
in (

let uu____12209 = (

let uu____12210 = (FStar_Util.set_is_subset_of fvs_rhs fvs_lhs)
in (not (uu____12210)))
in (match (uu____12209) with
| true -> begin
((FStar_Util.Inl ("quasi-pattern, free names on the RHS are not included in the LHS")), (wl1))
end
| uu____12229 -> begin
(

let uu____12230 = (

let uu____12237 = (mk_solution env1 lhs1 bs rhs1)
in FStar_Util.Inr (uu____12237))
in (

let uu____12242 = (restrict_all_uvars ctx_u uvars1 wl1)
in ((uu____12230), (uu____12242))))
end))))
end)
end))
end))
end)))
in (

let imitate_app = (fun orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 -> (

let bs_lhs_args = (FStar_List.map (fun uu____12304 -> (match (uu____12304) with
| (x, i) -> begin
(

let uu____12315 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____12315), (i)))
end)) bs_lhs)
in (

let uu____12316 = (FStar_Syntax_Util.head_and_args rhs1)
in (match (uu____12316) with
| (rhs_hd, args) -> begin
(

let uu____12353 = (FStar_Util.prefix args)
in (match (uu____12353) with
| (args_rhs, last_arg_rhs) -> begin
(

let rhs' = (FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs FStar_Pervasives_Native.None rhs1.FStar_Syntax_Syntax.pos)
in (

let uu____12411 = lhs1
in (match (uu____12411) with
| (t_lhs, u_lhs, _lhs_args) -> begin
(

let uu____12415 = (

let uu____12426 = (

let uu____12433 = (

let uu____12436 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12436))
in (copy_uvar u_lhs uu____12433 wl1))
in (match (uu____12426) with
| (uu____12457, t_last_arg, wl2) -> begin
(

let uu____12460 = (

let uu____12467 = (

let uu____12470 = (

let uu____12477 = (

let uu____12484 = (FStar_Syntax_Syntax.null_binder t_last_arg)
in (uu____12484)::[])
in (FStar_List.append bs_lhs uu____12477))
in (

let uu____12501 = (FStar_Syntax_Syntax.mk_Total t_res_lhs)
in (FStar_Syntax_Util.arrow uu____12470 uu____12501)))
in (copy_uvar u_lhs uu____12467 wl2))
in (match (uu____12460) with
| (uu____12514, u_lhs', wl3) -> begin
(

let lhs' = (FStar_Syntax_Syntax.mk_Tm_app u_lhs' bs_lhs_args FStar_Pervasives_Native.None t_lhs.FStar_Syntax_Syntax.pos)
in (

let uu____12520 = (

let uu____12527 = (

let uu____12530 = (FStar_Syntax_Syntax.mk_Total t_last_arg)
in (FStar_Syntax_Util.arrow bs_lhs uu____12530))
in (copy_uvar u_lhs uu____12527 wl3))
in (match (uu____12520) with
| (uu____12543, u_lhs'_last_arg, wl4) -> begin
(

let lhs'_last_arg = (FStar_Syntax_Syntax.mk_Tm_app u_lhs'_last_arg bs_lhs_args FStar_Pervasives_Native.None t_lhs.FStar_Syntax_Syntax.pos)
in ((lhs'), (lhs'_last_arg), (wl4)))
end)))
end))
end))
in (match (uu____12415) with
| (lhs', lhs'_last_arg, wl2) -> begin
(

let sol = (

let uu____12567 = (

let uu____12568 = (

let uu____12573 = (

let uu____12574 = (

let uu____12577 = (

let uu____12582 = (

let uu____12583 = (FStar_Syntax_Syntax.as_arg lhs'_last_arg)
in (uu____12583)::[])
in (FStar_Syntax_Syntax.mk_Tm_app lhs' uu____12582))
in (uu____12577 FStar_Pervasives_Native.None t_lhs.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.abs bs_lhs uu____12574 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot t_res_lhs)))))
in ((u_lhs), (uu____12573)))
in TERM (uu____12568))
in (uu____12567)::[])
in (

let uu____12604 = (

let uu____12611 = (mk_t_problem wl2 [] orig1 lhs' FStar_TypeChecker_Common.EQ rhs' FStar_Pervasives_Native.None "first-order lhs")
in (match (uu____12611) with
| (p1, wl3) -> begin
(

let uu____12628 = (mk_t_problem wl3 [] orig1 lhs'_last_arg FStar_TypeChecker_Common.EQ (FStar_Pervasives_Native.fst last_arg_rhs) FStar_Pervasives_Native.None "first-order rhs")
in (match (uu____12628) with
| (p2, wl4) -> begin
(((p1)::(p2)::[]), (wl4))
end))
end))
in (match (uu____12604) with
| (sub_probs, wl3) -> begin
(

let uu____12655 = (

let uu____12656 = (solve_prob orig1 FStar_Pervasives_Native.None sol wl3)
in (attempt sub_probs uu____12656))
in (solve env1 uu____12655))
end)))
end))
end)))
end))
end))))
in (

let first_order = (fun orig1 env1 wl1 lhs1 rhs1 -> (

let is_app = (fun rhs2 -> (

let uu____12689 = (FStar_Syntax_Util.head_and_args rhs2)
in (match (uu____12689) with
| (uu____12704, args) -> begin
(match (args) with
| [] -> begin
false
end
| uu____12732 -> begin
true
end)
end)))
in (

let is_arrow = (fun rhs2 -> (

let uu____12747 = (

let uu____12748 = (FStar_Syntax_Subst.compress rhs2)
in uu____12748.FStar_Syntax_Syntax.n)
in (match (uu____12747) with
| FStar_Syntax_Syntax.Tm_arrow (uu____12751) -> begin
true
end
| uu____12764 -> begin
false
end)))
in (

let uu____12765 = (quasi_pattern env1 lhs1)
in (match (uu____12765) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12776 = (

let uu____12777 = (prob_to_string env1 orig1)
in (FStar_Util.format1 "first_order heursitic cannot solve %s; lhs not a quasi-pattern" uu____12777))
in (giveup_or_defer env1 orig1 wl1 uu____12776))
end
| FStar_Pervasives_Native.Some (bs_lhs, t_res_lhs) -> begin
(

let uu____12784 = (is_app rhs1)
in (match (uu____12784) with
| true -> begin
(imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1)
end
| uu____12785 -> begin
(

let uu____12786 = (is_arrow rhs1)
in (match (uu____12786) with
| true -> begin
(imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs FStar_TypeChecker_Common.EQ rhs1)
end
| uu____12787 -> begin
(

let uu____12788 = (

let uu____12789 = (prob_to_string env1 orig1)
in (FStar_Util.format1 "first_order heursitic cannot solve %s; rhs not an app or arrow" uu____12789))
in (giveup_or_defer env1 orig1 wl1 uu____12788))
end))
end))
end)))))
in (match ((p_rel orig)) with
| FStar_TypeChecker_Common.SUB -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer env orig wl "flex-rigid subtyping")
end
| uu____12790 -> begin
(solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.SUBINV -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer env orig wl "flex-rigid subtyping")
end
| uu____12791 -> begin
(solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.EQ -> begin
(

let uu____12792 = lhs
in (match (uu____12792) with
| (_t1, ctx_uv, args_lhs) -> begin
(

let uu____12796 = (pat_vars env ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs)
in (match (uu____12796) with
| FStar_Pervasives_Native.Some (lhs_binders) -> begin
(

let rhs1 = (sn env rhs)
in (

let names_to_string1 = (fun fvs -> (

let uu____12811 = (

let uu____12814 = (FStar_Util.set_elements fvs)
in (FStar_List.map FStar_Syntax_Print.bv_to_string uu____12814))
in (FStar_All.pipe_right uu____12811 (FStar_String.concat ", "))))
in (

let fvs1 = (binders_as_bv_set (FStar_List.append ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders lhs_binders))
in (

let fvs2 = (FStar_Syntax_Free.names rhs1)
in (

let uu____12829 = (occurs_check ctx_uv rhs1)
in (match (uu____12829) with
| (uvars1, occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____12851 = (

let uu____12852 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____12852))
in (giveup_or_defer env orig wl uu____12851))
end
| uu____12853 -> begin
(

let uu____12854 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____12854) with
| true -> begin
(

let sol = (mk_solution env lhs lhs_binders rhs1)
in (

let wl1 = (restrict_all_uvars ctx_uv uvars1 wl)
in (

let uu____12859 = (solve_prob orig FStar_Pervasives_Native.None sol wl1)
in (solve env uu____12859))))
end
| uu____12860 -> begin
(match (wl.defer_ok) with
| true -> begin
(

let uu____12861 = (

let uu____12862 = (names_to_string1 fvs2)
in (

let uu____12863 = (names_to_string1 fvs1)
in (

let uu____12864 = (FStar_Syntax_Print.binders_to_string ", " (FStar_List.append ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders lhs_binders))
in (FStar_Util.format3 "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}" uu____12862 uu____12863 uu____12864))))
in (giveup_or_defer env orig wl uu____12861))
end
| uu____12869 -> begin
(first_order orig env wl lhs rhs1)
end)
end))
end)
end))))))
end
| uu____12870 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer env orig wl "Not a pattern")
end
| uu____12873 -> begin
(

let uu____12874 = (try_quasi_pattern orig env wl lhs rhs)
in (match (uu____12874) with
| (FStar_Util.Inr (sol), wl1) -> begin
(

let uu____12897 = (solve_prob orig FStar_Pervasives_Native.None sol wl1)
in (solve env uu____12897))
end
| (FStar_Util.Inl (msg), uu____12899) -> begin
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
| uu____12913 -> begin
(solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.SUBINV -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer env orig wl "flex-flex subtyping")
end
| uu____12914 -> begin
(solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.EQ -> begin
(match ((wl.defer_ok && ((not ((is_flex_pat lhs))) || (not ((is_flex_pat rhs)))))) with
| true -> begin
(giveup_or_defer env orig wl "flex-flex non-pattern")
end
| uu____12927 -> begin
(

let uu____12928 = (

let uu____12945 = (quasi_pattern env lhs)
in (

let uu____12952 = (quasi_pattern env rhs)
in ((uu____12945), (uu____12952))))
in (match (uu____12928) with
| (FStar_Pervasives_Native.Some (binders_lhs, t_res_lhs), FStar_Pervasives_Native.Some (binders_rhs, t_res_rhs)) -> begin
(

let uu____12995 = lhs
in (match (uu____12995) with
| ({FStar_Syntax_Syntax.n = uu____12996; FStar_Syntax_Syntax.pos = range; FStar_Syntax_Syntax.vars = uu____12998}, u_lhs, uu____13000) -> begin
(

let uu____13003 = rhs
in (match (uu____13003) with
| (uu____13004, u_rhs, uu____13006) -> begin
(

let uu____13007 = ((FStar_Syntax_Unionfind.equiv u_lhs.FStar_Syntax_Syntax.ctx_uvar_head u_rhs.FStar_Syntax_Syntax.ctx_uvar_head) && (binders_eq binders_lhs binders_rhs))
in (match (uu____13007) with
| true -> begin
(

let uu____13008 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____13008))
end
| uu____13009 -> begin
(

let uu____13010 = (mk_t_problem wl [] orig t_res_lhs FStar_TypeChecker_Common.EQ t_res_rhs FStar_Pervasives_Native.None "flex-flex typing")
in (match (uu____13010) with
| (sub_prob, wl1) -> begin
(

let uu____13021 = (maximal_prefix u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders)
in (match (uu____13021) with
| (ctx_w, (ctx_l, ctx_r)) -> begin
(

let gamma_w = (gamma_until u_lhs.FStar_Syntax_Syntax.ctx_uvar_gamma ctx_w)
in (

let zs = (intersect_binders (FStar_List.append ctx_l binders_lhs) (FStar_List.append ctx_r binders_rhs))
in (

let uu____13049 = (

let uu____13056 = (

let uu____13059 = (FStar_Syntax_Syntax.mk_Total t_res_lhs)
in (FStar_Syntax_Util.arrow zs uu____13059))
in (new_uvar (Prims.strcat "flex-flex quasi: lhs=" (Prims.strcat u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason (Prims.strcat ", rhs=" u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))) wl1 range gamma_w ctx_w uu____13056 (u_lhs.FStar_Syntax_Syntax.ctx_uvar_should_check || u_rhs.FStar_Syntax_Syntax.ctx_uvar_should_check)))
in (match (uu____13049) with
| (uu____13062, w, wl2) -> begin
(

let w_app = (

let uu____13068 = (

let uu____13073 = (FStar_List.map (fun uu____13082 -> (match (uu____13082) with
| (z, uu____13088) -> begin
(

let uu____13089 = (FStar_Syntax_Syntax.bv_to_name z)
in (FStar_Syntax_Syntax.as_arg uu____13089))
end)) zs)
in (FStar_Syntax_Syntax.mk_Tm_app w uu____13073))
in (uu____13068 FStar_Pervasives_Native.None w.FStar_Syntax_Syntax.pos))
in ((

let uu____13093 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____13093) with
| true -> begin
(

let uu____13094 = (flex_t_to_string lhs)
in (

let uu____13095 = (flex_t_to_string rhs)
in (

let uu____13096 = (

let uu____13097 = (destruct_flex_t w)
in (flex_t_to_string uu____13097))
in (FStar_Util.print3 "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s" uu____13094 uu____13095 uu____13096))))
end
| uu____13104 -> begin
()
end));
(

let sol = (

let s1 = (

let uu____13109 = (

let uu____13114 = (FStar_Syntax_Util.abs binders_lhs w_app (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot t_res_lhs))))
in ((u_lhs), (uu____13114)))
in TERM (uu____13109))
in (

let uu____13115 = (FStar_Syntax_Unionfind.equiv u_lhs.FStar_Syntax_Syntax.ctx_uvar_head u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____13115) with
| true -> begin
(s1)::[]
end
| uu____13118 -> begin
(

let s2 = (

let uu____13120 = (

let uu____13125 = (FStar_Syntax_Util.abs binders_rhs w_app (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot t_res_lhs))))
in ((u_rhs), (uu____13125)))
in TERM (uu____13120))
in (s1)::(s2)::[])
end)))
in (

let uu____13126 = (

let uu____13127 = (solve_prob orig FStar_Pervasives_Native.None sol wl2)
in (attempt ((sub_prob)::[]) uu____13127))
in (solve env uu____13126)));
))
end))))
end))
end))
end))
end))
end))
end
| uu____13128 -> begin
(giveup_or_defer env orig wl "flex-flex: non-patterns")
end))
end)
end))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> ((def_check_prob "solve_t\'.1" (FStar_TypeChecker_Common.TProb (problem)));
(

let giveup_or_defer1 = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env1 orig wl1 head1 head2 t1 t2 -> (

let uu____13196 = (head_matches_delta env1 wl1 t1 t2)
in (match (uu____13196) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____13227), uu____13228) -> begin
(

let rec may_relate = (fun head3 -> (

let uu____13255 = (

let uu____13256 = (FStar_Syntax_Subst.compress head3)
in uu____13256.FStar_Syntax_Syntax.n)
in (match (uu____13255) with
| FStar_Syntax_Syntax.Tm_name (uu____13259) -> begin
true
end
| FStar_Syntax_Syntax.Tm_match (uu____13260) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____13283; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational; FStar_Syntax_Syntax.fv_qual = uu____13284}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____13287; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (uu____13288); FStar_Syntax_Syntax.fv_qual = uu____13289}) -> begin
(Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____13293, uu____13294) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____13336) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____13342) -> begin
(may_relate t)
end
| uu____13347 -> begin
false
end)))
in (

let uu____13348 = (((may_relate head1) || (may_relate head2)) && wl1.smt_ok)
in (match (uu____13348) with
| true -> begin
(

let uu____13349 = (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_eq2 wl1 orig t1 t2)
end
| uu____13358 -> begin
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

let uu____13381 = (

let uu____13382 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t11 uu____13382 t21))
in (FStar_Syntax_Util.mk_forall u_x x uu____13381))))
end))
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB)) with
| true -> begin
(

let uu____13387 = (has_type_guard t1 t2)
in ((uu____13387), (wl1)))
end
| uu____13392 -> begin
(

let uu____13393 = (has_type_guard t2 t1)
in ((uu____13393), (wl1)))
end))
end)
in (match (uu____13349) with
| (guard, wl2) -> begin
(

let uu____13400 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl2)
in (solve env1 uu____13400))
end))
end
| uu____13401 -> begin
(

let uu____13402 = (

let uu____13403 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____13404 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.format2 "head mismatch (%s vs %s)" uu____13403 uu____13404)))
in (giveup env1 uu____13402 orig))
end)))
end
| (uu____13405, FStar_Pervasives_Native.Some (t11, t21)) -> begin
(solve_t env1 (

let uu___154_13419 = problem
in {FStar_TypeChecker_Common.pid = uu___154_13419.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___154_13419.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___154_13419.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___154_13419.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___154_13419.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___154_13419.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___154_13419.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___154_13419.FStar_TypeChecker_Common.rank}) wl1)
end
| (uu____13420, FStar_Pervasives_Native.None) -> begin
((

let uu____13432 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____13432) with
| true -> begin
(

let uu____13433 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____13434 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____13435 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____13436 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" uu____13433 uu____13434 uu____13435 uu____13436)))))
end
| uu____13437 -> begin
()
end));
(

let uu____13438 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____13438) with
| (head11, args1) -> begin
(

let uu____13475 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____13475) with
| (head21, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((Prims.op_disEquality nargs (FStar_List.length args2))) with
| true -> begin
(

let uu____13529 = (

let uu____13530 = (FStar_Syntax_Print.term_to_string head11)
in (

let uu____13531 = (args_to_string args1)
in (

let uu____13532 = (FStar_Syntax_Print.term_to_string head21)
in (

let uu____13533 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____13530 uu____13531 uu____13532 uu____13533)))))
in (giveup env1 uu____13529 orig))
end
| uu____13534 -> begin
(

let uu____13535 = ((Prims.op_Equality nargs (Prims.parse_int "0")) || (

let uu____13542 = (FStar_Syntax_Util.eq_args args1 args2)
in (Prims.op_Equality uu____13542 FStar_Syntax_Util.Equal)))
in (match (uu____13535) with
| true -> begin
(

let uu____13543 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____13543) with
| USolved (wl2) -> begin
(

let uu____13545 = (solve_prob orig FStar_Pervasives_Native.None [] wl2)
in (solve env1 uu____13545))
end
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end))
end
| uu____13548 -> begin
(

let uu____13549 = (base_and_refinement env1 t1)
in (match (uu____13549) with
| (base1, refinement1) -> begin
(

let uu____13574 = (base_and_refinement env1 t2)
in (match (uu____13574) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(

let uu____13631 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____13631) with
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end
| USolved (wl2) -> begin
(

let uu____13635 = (FStar_List.fold_right2 (fun uu____13668 uu____13669 uu____13670 -> (match (((uu____13668), (uu____13669), (uu____13670))) with
| ((a, uu____13706), (a', uu____13708), (subprobs, wl3)) -> begin
(

let uu____13729 = (mk_t_problem wl3 [] orig a FStar_TypeChecker_Common.EQ a' FStar_Pervasives_Native.None "index")
in (match (uu____13729) with
| (p, wl4) -> begin
(((p)::subprobs), (wl4))
end))
end)) args1 args2 (([]), (wl2)))
in (match (uu____13635) with
| (subprobs, wl3) -> begin
(

let formula = (

let uu____13759 = (FStar_List.map (fun p -> (p_guard p)) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____13759))
in (

let wl4 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) [] wl3)
in (solve env1 (attempt subprobs wl4))))
end))
end))
end
| uu____13767 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env1 (

let uu___155_13807 = problem
in {FStar_TypeChecker_Common.pid = uu___155_13807.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___155_13807.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___155_13807.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___155_13807.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___155_13807.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___155_13807.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___155_13807.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___155_13807.FStar_TypeChecker_Common.rank}) wl1)))
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

let orig = FStar_TypeChecker_Common.TProb (problem)
in ((def_check_prob "solve_t\'.2" orig);
(

let uu____13810 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____13810) with
| true -> begin
(

let uu____13811 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____13811))
end
| uu____13812 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in ((

let uu____13816 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____13816) with
| true -> begin
(

let uu____13817 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____13818 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____13819 = (prob_to_string env orig)
in (FStar_Util.print3 "Attempting (%s - %s)\n%s\n" uu____13817 uu____13818 uu____13819))))
end
| uu____13820 -> begin
()
end));
(

let r = (FStar_TypeChecker_Env.get_range env)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_delayed (uu____13822), uu____13823) -> begin
(failwith "Impossible: terms were not compressed")
end
| (uu____13848, FStar_Syntax_Syntax.Tm_delayed (uu____13849)) -> begin
(failwith "Impossible: terms were not compressed")
end
| (FStar_Syntax_Syntax.Tm_ascribed (uu____13874), uu____13875) -> begin
(

let uu____13902 = (

let uu___156_13903 = problem
in (

let uu____13904 = (FStar_Syntax_Util.unascribe t1)
in {FStar_TypeChecker_Common.pid = uu___156_13903.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____13904; FStar_TypeChecker_Common.relation = uu___156_13903.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___156_13903.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___156_13903.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___156_13903.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___156_13903.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___156_13903.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___156_13903.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___156_13903.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____13902 wl))
end
| (FStar_Syntax_Syntax.Tm_meta (uu____13905), uu____13906) -> begin
(

let uu____13913 = (

let uu___157_13914 = problem
in (

let uu____13915 = (FStar_Syntax_Util.unmeta t1)
in {FStar_TypeChecker_Common.pid = uu___157_13914.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____13915; FStar_TypeChecker_Common.relation = uu___157_13914.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___157_13914.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___157_13914.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___157_13914.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___157_13914.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___157_13914.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___157_13914.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___157_13914.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____13913 wl))
end
| (uu____13916, FStar_Syntax_Syntax.Tm_ascribed (uu____13917)) -> begin
(

let uu____13944 = (

let uu___158_13945 = problem
in (

let uu____13946 = (FStar_Syntax_Util.unascribe t2)
in {FStar_TypeChecker_Common.pid = uu___158_13945.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___158_13945.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___158_13945.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____13946; FStar_TypeChecker_Common.element = uu___158_13945.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___158_13945.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___158_13945.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___158_13945.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___158_13945.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___158_13945.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____13944 wl))
end
| (uu____13947, FStar_Syntax_Syntax.Tm_meta (uu____13948)) -> begin
(

let uu____13955 = (

let uu___159_13956 = problem
in (

let uu____13957 = (FStar_Syntax_Util.unmeta t2)
in {FStar_TypeChecker_Common.pid = uu___159_13956.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___159_13956.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___159_13956.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____13957; FStar_TypeChecker_Common.element = uu___159_13956.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___159_13956.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___159_13956.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___159_13956.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___159_13956.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___159_13956.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____13955 wl))
end
| (FStar_Syntax_Syntax.Tm_quoted (t11, uu____13959), FStar_Syntax_Syntax.Tm_quoted (t21, uu____13961)) -> begin
(

let uu____13970 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____13970))
end
| (FStar_Syntax_Syntax.Tm_bvar (uu____13971), uu____13972) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (uu____13973, FStar_Syntax_Syntax.Tm_bvar (uu____13974)) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (FStar_Syntax_Syntax.Tm_type (u1), FStar_Syntax_Syntax.Tm_type (u2)) -> begin
(solve_one_universe_eq env orig u1 u2 wl)
end
| (FStar_Syntax_Syntax.Tm_arrow (bs1, c1), FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) -> begin
(

let mk_c = (fun c uu___114_14033 -> (match (uu___114_14033) with
| [] -> begin
c
end
| bs -> begin
(

let uu____14055 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____14055))
end))
in (

let uu____14064 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____14064) with
| ((bs11, c11), (bs21, c21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun wl1 scope env1 subst1 -> (

let c12 = (FStar_Syntax_Subst.subst_comp subst1 c11)
in (

let c22 = (FStar_Syntax_Subst.subst_comp subst1 c21)
in (

let rel = (

let uu____14187 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____14187) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____14188 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (mk_c_problem wl1 scope orig c12 rel c22 FStar_Pervasives_Native.None "function co-domain"))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___115_14262 -> (match (uu___115_14262) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____14296 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____14296) with
| ((bs11, tbody11), (bs21, tbody21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun wl1 scope env1 subst1 -> (

let uu____14415 = (FStar_Syntax_Subst.subst subst1 tbody11)
in (

let uu____14416 = (FStar_Syntax_Subst.subst subst1 tbody21)
in (mk_t_problem wl1 scope orig uu____14415 problem.FStar_TypeChecker_Common.relation uu____14416 FStar_Pervasives_Native.None "lambda co-domain")))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (uu____14417), uu____14418) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____14445) -> begin
true
end
| uu____14462 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____14481 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____14487 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let force_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
t
end
| uu____14502 -> begin
(

let uu____14503 = (env.FStar_TypeChecker_Env.type_of (

let uu___160_14511 = env
in {FStar_TypeChecker_Env.solver = uu___160_14511.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___160_14511.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___160_14511.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___160_14511.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___160_14511.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___160_14511.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___160_14511.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___160_14511.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___160_14511.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___160_14511.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___160_14511.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___160_14511.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___160_14511.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___160_14511.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___160_14511.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___160_14511.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___160_14511.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___160_14511.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___160_14511.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___160_14511.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___160_14511.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___160_14511.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___160_14511.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___160_14511.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___160_14511.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___160_14511.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___160_14511.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___160_14511.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___160_14511.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___160_14511.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___160_14511.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___160_14511.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___160_14511.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___160_14511.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___160_14511.FStar_TypeChecker_Env.dep_graph}) t)
in (match (uu____14503) with
| (uu____14514, ty, uu____14516) -> begin
(

let uu____14517 = (FStar_TypeChecker_Normalize.unfold_whnf env ty)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env t uu____14517))
end))
end))
in (

let uu____14518 = (

let uu____14531 = (maybe_eta t1)
in (

let uu____14536 = (maybe_eta t2)
in ((uu____14531), (uu____14536))))
in (match (uu____14518) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___161_14560 = problem
in {FStar_TypeChecker_Common.pid = uu___161_14560.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___161_14560.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___161_14560.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___161_14560.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___161_14560.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___161_14560.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___161_14560.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___161_14560.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____14571 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____14571) with
| true -> begin
(

let uu____14572 = (destruct_flex_t not_abs)
in (solve_t_flex_rigid_eq env orig wl uu____14572 t_abs))
end
| uu____14573 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___162_14581 = problem
in {FStar_TypeChecker_Common.pid = uu___162_14581.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___162_14581.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___162_14581.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_14581.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___162_14581.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___162_14581.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_14581.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_14581.FStar_TypeChecker_Common.rank}) wl)
end
| uu____14582 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____14593 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____14593) with
| true -> begin
(

let uu____14594 = (destruct_flex_t not_abs)
in (solve_t_flex_rigid_eq env orig wl uu____14594 t_abs))
end
| uu____14595 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___162_14603 = problem
in {FStar_TypeChecker_Common.pid = uu___162_14603.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___162_14603.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___162_14603.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_14603.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___162_14603.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___162_14603.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_14603.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_14603.FStar_TypeChecker_Common.rank}) wl)
end
| uu____14604 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| uu____14605 -> begin
(failwith "Impossible: at least one side is an abstraction")
end)))))
end
| (uu____14618, FStar_Syntax_Syntax.Tm_abs (uu____14619)) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____14646) -> begin
true
end
| uu____14663 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____14682 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____14688 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let force_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
t
end
| uu____14703 -> begin
(

let uu____14704 = (env.FStar_TypeChecker_Env.type_of (

let uu___160_14712 = env
in {FStar_TypeChecker_Env.solver = uu___160_14712.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___160_14712.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___160_14712.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___160_14712.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___160_14712.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___160_14712.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___160_14712.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___160_14712.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___160_14712.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___160_14712.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___160_14712.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___160_14712.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___160_14712.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___160_14712.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___160_14712.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___160_14712.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___160_14712.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___160_14712.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___160_14712.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___160_14712.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___160_14712.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___160_14712.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___160_14712.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___160_14712.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___160_14712.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___160_14712.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___160_14712.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___160_14712.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___160_14712.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___160_14712.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___160_14712.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___160_14712.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___160_14712.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___160_14712.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___160_14712.FStar_TypeChecker_Env.dep_graph}) t)
in (match (uu____14704) with
| (uu____14715, ty, uu____14717) -> begin
(

let uu____14718 = (FStar_TypeChecker_Normalize.unfold_whnf env ty)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env t uu____14718))
end))
end))
in (

let uu____14719 = (

let uu____14732 = (maybe_eta t1)
in (

let uu____14737 = (maybe_eta t2)
in ((uu____14732), (uu____14737))))
in (match (uu____14719) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___161_14761 = problem
in {FStar_TypeChecker_Common.pid = uu___161_14761.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___161_14761.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___161_14761.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___161_14761.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___161_14761.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___161_14761.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___161_14761.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___161_14761.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____14772 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____14772) with
| true -> begin
(

let uu____14773 = (destruct_flex_t not_abs)
in (solve_t_flex_rigid_eq env orig wl uu____14773 t_abs))
end
| uu____14774 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___162_14782 = problem
in {FStar_TypeChecker_Common.pid = uu___162_14782.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___162_14782.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___162_14782.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_14782.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___162_14782.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___162_14782.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_14782.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_14782.FStar_TypeChecker_Common.rank}) wl)
end
| uu____14783 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____14794 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____14794) with
| true -> begin
(

let uu____14795 = (destruct_flex_t not_abs)
in (solve_t_flex_rigid_eq env orig wl uu____14795 t_abs))
end
| uu____14796 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___162_14804 = problem
in {FStar_TypeChecker_Common.pid = uu___162_14804.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___162_14804.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___162_14804.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_14804.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___162_14804.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___162_14804.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_14804.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_14804.FStar_TypeChecker_Common.rank}) wl)
end
| uu____14805 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| uu____14806 -> begin
(failwith "Impossible: at least one side is an abstraction")
end)))))
end
| (FStar_Syntax_Syntax.Tm_refine (x1, ph1), FStar_Syntax_Syntax.Tm_refine (x2, phi2)) -> begin
(

let should_delta = (((

let uu____14834 = (FStar_Syntax_Free.uvars t1)
in (FStar_Util.set_is_empty uu____14834)) && (

let uu____14838 = (FStar_Syntax_Free.uvars t2)
in (FStar_Util.set_is_empty uu____14838))) && (

let uu____14845 = (head_matches env x1.FStar_Syntax_Syntax.sort x2.FStar_Syntax_Syntax.sort)
in (match (uu____14845) with
| MisMatch (FStar_Pervasives_Native.Some (d1), FStar_Pervasives_Native.Some (d2)) -> begin
(

let is_unfoldable = (fun uu___116_14857 -> (match (uu___116_14857) with
| FStar_Syntax_Syntax.Delta_constant -> begin
true
end
| FStar_Syntax_Syntax.Delta_defined_at_level (uu____14858) -> begin
true
end
| uu____14859 -> begin
false
end))
in ((is_unfoldable d1) && (is_unfoldable d2)))
end
| uu____14860 -> begin
false
end)))
in (

let uu____14861 = (as_refinement should_delta env wl t1)
in (match (uu____14861) with
| (x11, phi1) -> begin
(

let uu____14868 = (as_refinement should_delta env wl t2)
in (match (uu____14868) with
| (x21, phi21) -> begin
(

let uu____14875 = (mk_t_problem wl [] orig x11.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x21.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (match (uu____14875) with
| (base_prob, wl1) -> begin
(

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

let uu____14941 = (imp phi12 phi23)
in (FStar_All.pipe_right uu____14941 (guard_on_element wl1 problem x12))))
in (

let fallback = (fun uu____14953 -> (

let impl = (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp1 FStar_Syntax_Util.mk_iff phi11 phi22)
end
| uu____14959 -> begin
(mk_imp1 FStar_Syntax_Util.mk_imp phi11 phi22)
end)
in (

let guard = (FStar_Syntax_Util.mk_conj (p_guard base_prob) impl)
in (

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl1)
in (solve env1 (attempt ((base_prob)::[]) wl2))))))
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____14964 = (

let uu____14969 = (

let uu____14976 = (FStar_Syntax_Syntax.mk_binder x12)
in (uu____14976)::[])
in (mk_t_problem wl1 uu____14969 orig phi11 FStar_TypeChecker_Common.EQ phi22 FStar_Pervasives_Native.None "refinement formula"))
in (match (uu____14964) with
| (ref_prob, wl2) -> begin
(

let uu____14991 = (solve env1 (

let uu___163_14993 = wl2
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___163_14993.ctr; defer_ok = false; smt_ok = uu___163_14993.smt_ok; tcenv = uu___163_14993.tcenv; wl_implicits = uu___163_14993.wl_implicits}))
in (match (uu____14991) with
| Failed (uu____15000) -> begin
(fallback ())
end
| Success (uu____15005) -> begin
(

let guard = (

let uu____15013 = (FStar_All.pipe_right (p_guard ref_prob) (guard_on_element wl2 problem x12))
in (FStar_Syntax_Util.mk_conj (p_guard base_prob) uu____15013))
in (

let wl3 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl2)
in (

let wl4 = (

let uu___164_15022 = wl3
in {attempting = uu___164_15022.attempting; wl_deferred = uu___164_15022.wl_deferred; ctr = (wl3.ctr + (Prims.parse_int "1")); defer_ok = uu___164_15022.defer_ok; smt_ok = uu___164_15022.smt_ok; tcenv = uu___164_15022.tcenv; wl_implicits = uu___164_15022.wl_implicits})
in (solve env1 (attempt ((base_prob)::[]) wl4)))))
end))
end))
end
| uu____15023 -> begin
(fallback ())
end))))))))
end))
end))
end)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____15024), FStar_Syntax_Syntax.Tm_uvar (uu____15025)) -> begin
(

let uu____15026 = (destruct_flex_t t1)
in (

let uu____15027 = (destruct_flex_t t2)
in (solve_t_flex_flex env orig wl uu____15026 uu____15027)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____15028); FStar_Syntax_Syntax.pos = uu____15029; FStar_Syntax_Syntax.vars = uu____15030}, uu____15031), FStar_Syntax_Syntax.Tm_uvar (uu____15032)) -> begin
(

let uu____15053 = (destruct_flex_t t1)
in (

let uu____15054 = (destruct_flex_t t2)
in (solve_t_flex_flex env orig wl uu____15053 uu____15054)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____15055), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____15056); FStar_Syntax_Syntax.pos = uu____15057; FStar_Syntax_Syntax.vars = uu____15058}, uu____15059)) -> begin
(

let uu____15080 = (destruct_flex_t t1)
in (

let uu____15081 = (destruct_flex_t t2)
in (solve_t_flex_flex env orig wl uu____15080 uu____15081)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____15082); FStar_Syntax_Syntax.pos = uu____15083; FStar_Syntax_Syntax.vars = uu____15084}, uu____15085), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____15086); FStar_Syntax_Syntax.pos = uu____15087; FStar_Syntax_Syntax.vars = uu____15088}, uu____15089)) -> begin
(

let uu____15130 = (destruct_flex_t t1)
in (

let uu____15131 = (destruct_flex_t t2)
in (solve_t_flex_flex env orig wl uu____15130 uu____15131)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____15132), uu____15133) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(

let uu____15134 = (destruct_flex_t t1)
in (solve_t_flex_rigid_eq env orig wl uu____15134 t2))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____15135); FStar_Syntax_Syntax.pos = uu____15136; FStar_Syntax_Syntax.vars = uu____15137}, uu____15138), uu____15139) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(

let uu____15160 = (destruct_flex_t t1)
in (solve_t_flex_rigid_eq env orig wl uu____15160 t2))
end
| (uu____15161, FStar_Syntax_Syntax.Tm_uvar (uu____15162)) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (uu____15163, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____15164); FStar_Syntax_Syntax.pos = uu____15165; FStar_Syntax_Syntax.vars = uu____15166}, uu____15167)) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____15188), FStar_Syntax_Syntax.Tm_arrow (uu____15189)) -> begin
(solve_t' env (

let uu___165_15203 = problem
in {FStar_TypeChecker_Common.pid = uu___165_15203.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___165_15203.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___165_15203.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___165_15203.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___165_15203.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___165_15203.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___165_15203.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___165_15203.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___165_15203.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____15204); FStar_Syntax_Syntax.pos = uu____15205; FStar_Syntax_Syntax.vars = uu____15206}, uu____15207), FStar_Syntax_Syntax.Tm_arrow (uu____15208)) -> begin
(solve_t' env (

let uu___165_15242 = problem
in {FStar_TypeChecker_Common.pid = uu___165_15242.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___165_15242.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___165_15242.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___165_15242.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___165_15242.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___165_15242.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___165_15242.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___165_15242.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___165_15242.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____15243, FStar_Syntax_Syntax.Tm_uvar (uu____15244)) -> begin
(solve env (attempt ((FStar_TypeChecker_Common.TProb (problem))::[]) wl))
end
| (uu____15245, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____15246); FStar_Syntax_Syntax.pos = uu____15247; FStar_Syntax_Syntax.vars = uu____15248}, uu____15249)) -> begin
(solve env (attempt ((FStar_TypeChecker_Common.TProb (problem))::[]) wl))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____15270), uu____15271) -> begin
(solve env (attempt ((FStar_TypeChecker_Common.TProb (problem))::[]) wl))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____15272); FStar_Syntax_Syntax.pos = uu____15273; FStar_Syntax_Syntax.vars = uu____15274}, uu____15275), uu____15276) -> begin
(solve env (attempt ((FStar_TypeChecker_Common.TProb (problem))::[]) wl))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____15297), uu____15298) -> begin
(

let t21 = (

let uu____15306 = (base_and_refinement env t2)
in (FStar_All.pipe_left force_refinement uu____15306))
in (solve_t env (

let uu___166_15332 = problem
in {FStar_TypeChecker_Common.pid = uu___166_15332.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___166_15332.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___166_15332.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___166_15332.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_15332.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___166_15332.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___166_15332.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_15332.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_15332.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____15333, FStar_Syntax_Syntax.Tm_refine (uu____15334)) -> begin
(

let t11 = (

let uu____15342 = (base_and_refinement env t1)
in (FStar_All.pipe_left force_refinement uu____15342))
in (solve_t env (

let uu___167_15368 = problem
in {FStar_TypeChecker_Common.pid = uu___167_15368.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___167_15368.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___167_15368.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___167_15368.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___167_15368.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___167_15368.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___167_15368.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___167_15368.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___167_15368.FStar_TypeChecker_Common.rank}) wl))
end
| (FStar_Syntax_Syntax.Tm_match (t11, brs1), FStar_Syntax_Syntax.Tm_match (t21, brs2)) -> begin
(

let uu____15445 = (mk_t_problem wl [] orig t11 FStar_TypeChecker_Common.EQ t21 FStar_Pervasives_Native.None "match scrutinee")
in (match (uu____15445) with
| (sc_prob, wl1) -> begin
(

let rec solve_branches = (fun wl2 brs11 brs21 -> (match (((brs11), (brs21))) with
| ((br1)::rs1, (br2)::rs2) -> begin
(

let uu____15666 = br1
in (match (uu____15666) with
| (p1, w1, uu____15691) -> begin
(

let uu____15708 = br2
in (match (uu____15708) with
| (p2, w2, uu____15727) -> begin
(

let uu____15732 = (

let uu____15733 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (not (uu____15733)))
in (match (uu____15732) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____15748 -> begin
(

let uu____15749 = (FStar_Syntax_Subst.open_branch' br1)
in (match (uu____15749) with
| ((p11, w11, e1), s) -> begin
(

let uu____15782 = br2
in (match (uu____15782) with
| (p21, w21, e2) -> begin
(

let w22 = (FStar_Util.map_opt w21 (FStar_Syntax_Subst.subst s))
in (

let e21 = (FStar_Syntax_Subst.subst s e2)
in (

let scope = (

let uu____15817 = (FStar_Syntax_Syntax.pat_bvs p11)
in (FStar_All.pipe_left (FStar_List.map FStar_Syntax_Syntax.mk_binder) uu____15817))
in (

let uu____15828 = (match (((w11), (w22))) with
| (FStar_Pervasives_Native.Some (uu____15851), FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (uu____15868)) -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.Some ((([]), (wl2)))
end
| (FStar_Pervasives_Native.Some (w12), FStar_Pervasives_Native.Some (w23)) -> begin
(

let uu____15911 = (mk_t_problem wl2 scope orig w12 FStar_TypeChecker_Common.EQ w23 FStar_Pervasives_Native.None "when clause")
in (match (uu____15911) with
| (p, wl3) -> begin
FStar_Pervasives_Native.Some ((((p)::[]), (wl3)))
end))
end)
in (FStar_Util.bind_opt uu____15828 (fun uu____15953 -> (match (uu____15953) with
| (wprobs, wl3) -> begin
(

let uu____15974 = (mk_t_problem wl3 scope orig e1 FStar_TypeChecker_Common.EQ e21 FStar_Pervasives_Native.None "branch body")
in (match (uu____15974) with
| (prob, wl4) -> begin
(

let uu____15989 = (solve_branches wl4 rs1 rs2)
in (FStar_Util.bind_opt uu____15989 (fun uu____16013 -> (match (uu____16013) with
| (r1, wl5) -> begin
FStar_Pervasives_Native.Some ((((prob)::(FStar_List.append wprobs r1)), (wl5)))
end))))
end))
end)))))))
end))
end))
end))
end))
end))
end
| ([], []) -> begin
FStar_Pervasives_Native.Some ((([]), (wl2)))
end
| uu____16098 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____16135 = (solve_branches wl1 brs1 brs2)
in (match (uu____16135) with
| FStar_Pervasives_Native.None -> begin
(giveup env "Tm_match branches don\'t match" orig)
end
| FStar_Pervasives_Native.Some (sub_probs, wl2) -> begin
(

let sub_probs1 = (sc_prob)::sub_probs
in (

let wl3 = (solve_prob orig FStar_Pervasives_Native.None [] wl2)
in (solve env (attempt sub_probs1 wl3))))
end)))
end))
end
| (FStar_Syntax_Syntax.Tm_match (uu____16166), uu____16167) -> begin
(

let head1 = (

let uu____16191 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____16191 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____16231 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____16231 FStar_Pervasives_Native.fst))
in ((

let uu____16271 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____16271) with
| true -> begin
(

let uu____16272 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____16273 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____16274 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____16272 uu____16273 uu____16274))))
end
| uu____16275 -> begin
()
end));
(

let uu____16276 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____16276) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____16283 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____16283) with
| true -> begin
(

let uu____16284 = (

let uu____16291 = (

let uu____16292 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____16292 FStar_Syntax_Util.Equal))
in (match (uu____16291) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____16301 -> begin
(

let uu____16302 = (mk_eq2 wl orig t1 t2)
in (match (uu____16302) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____16284) with
| (guard, wl1) -> begin
(

let uu____16323 = (solve_prob orig guard [] wl1)
in (solve env uu____16323))
end))
end
| uu____16324 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____16325 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____16326), uu____16327) -> begin
(

let head1 = (

let uu____16335 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____16335 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____16375 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____16375 FStar_Pervasives_Native.fst))
in ((

let uu____16415 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____16415) with
| true -> begin
(

let uu____16416 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____16417 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____16418 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____16416 uu____16417 uu____16418))))
end
| uu____16419 -> begin
()
end));
(

let uu____16420 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____16420) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____16427 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____16427) with
| true -> begin
(

let uu____16428 = (

let uu____16435 = (

let uu____16436 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____16436 FStar_Syntax_Util.Equal))
in (match (uu____16435) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____16445 -> begin
(

let uu____16446 = (mk_eq2 wl orig t1 t2)
in (match (uu____16446) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____16428) with
| (guard, wl1) -> begin
(

let uu____16467 = (solve_prob orig guard [] wl1)
in (solve env uu____16467))
end))
end
| uu____16468 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____16469 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_name (uu____16470), uu____16471) -> begin
(

let head1 = (

let uu____16473 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____16473 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____16513 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____16513 FStar_Pervasives_Native.fst))
in ((

let uu____16553 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____16553) with
| true -> begin
(

let uu____16554 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____16555 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____16556 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____16554 uu____16555 uu____16556))))
end
| uu____16557 -> begin
()
end));
(

let uu____16558 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____16558) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____16565 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____16565) with
| true -> begin
(

let uu____16566 = (

let uu____16573 = (

let uu____16574 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____16574 FStar_Syntax_Util.Equal))
in (match (uu____16573) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____16583 -> begin
(

let uu____16584 = (mk_eq2 wl orig t1 t2)
in (match (uu____16584) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____16566) with
| (guard, wl1) -> begin
(

let uu____16605 = (solve_prob orig guard [] wl1)
in (solve env uu____16605))
end))
end
| uu____16606 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____16607 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_constant (uu____16608), uu____16609) -> begin
(

let head1 = (

let uu____16611 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____16611 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____16651 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____16651 FStar_Pervasives_Native.fst))
in ((

let uu____16691 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____16691) with
| true -> begin
(

let uu____16692 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____16693 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____16694 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____16692 uu____16693 uu____16694))))
end
| uu____16695 -> begin
()
end));
(

let uu____16696 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____16696) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____16703 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____16703) with
| true -> begin
(

let uu____16704 = (

let uu____16711 = (

let uu____16712 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____16712 FStar_Syntax_Util.Equal))
in (match (uu____16711) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____16721 -> begin
(

let uu____16722 = (mk_eq2 wl orig t1 t2)
in (match (uu____16722) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____16704) with
| (guard, wl1) -> begin
(

let uu____16743 = (solve_prob orig guard [] wl1)
in (solve env uu____16743))
end))
end
| uu____16744 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____16745 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____16746), uu____16747) -> begin
(

let head1 = (

let uu____16749 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____16749 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____16789 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____16789 FStar_Pervasives_Native.fst))
in ((

let uu____16829 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____16829) with
| true -> begin
(

let uu____16830 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____16831 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____16832 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____16830 uu____16831 uu____16832))))
end
| uu____16833 -> begin
()
end));
(

let uu____16834 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____16834) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____16841 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____16841) with
| true -> begin
(

let uu____16842 = (

let uu____16849 = (

let uu____16850 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____16850 FStar_Syntax_Util.Equal))
in (match (uu____16849) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____16859 -> begin
(

let uu____16860 = (mk_eq2 wl orig t1 t2)
in (match (uu____16860) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____16842) with
| (guard, wl1) -> begin
(

let uu____16881 = (solve_prob orig guard [] wl1)
in (solve env uu____16881))
end))
end
| uu____16882 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____16883 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_app (uu____16884), uu____16885) -> begin
(

let head1 = (

let uu____16901 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____16901 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____16941 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____16941 FStar_Pervasives_Native.fst))
in ((

let uu____16981 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____16981) with
| true -> begin
(

let uu____16982 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____16983 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____16984 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____16982 uu____16983 uu____16984))))
end
| uu____16985 -> begin
()
end));
(

let uu____16986 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____16986) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____16993 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____16993) with
| true -> begin
(

let uu____16994 = (

let uu____17001 = (

let uu____17002 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____17002 FStar_Syntax_Util.Equal))
in (match (uu____17001) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____17011 -> begin
(

let uu____17012 = (mk_eq2 wl orig t1 t2)
in (match (uu____17012) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____16994) with
| (guard, wl1) -> begin
(

let uu____17033 = (solve_prob orig guard [] wl1)
in (solve env uu____17033))
end))
end
| uu____17034 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____17035 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____17036, FStar_Syntax_Syntax.Tm_match (uu____17037)) -> begin
(

let head1 = (

let uu____17061 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____17061 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____17101 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____17101 FStar_Pervasives_Native.fst))
in ((

let uu____17141 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____17141) with
| true -> begin
(

let uu____17142 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____17143 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____17144 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____17142 uu____17143 uu____17144))))
end
| uu____17145 -> begin
()
end));
(

let uu____17146 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____17146) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____17153 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____17153) with
| true -> begin
(

let uu____17154 = (

let uu____17161 = (

let uu____17162 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____17162 FStar_Syntax_Util.Equal))
in (match (uu____17161) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____17171 -> begin
(

let uu____17172 = (mk_eq2 wl orig t1 t2)
in (match (uu____17172) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____17154) with
| (guard, wl1) -> begin
(

let uu____17193 = (solve_prob orig guard [] wl1)
in (solve env uu____17193))
end))
end
| uu____17194 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____17195 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____17196, FStar_Syntax_Syntax.Tm_uinst (uu____17197)) -> begin
(

let head1 = (

let uu____17205 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____17205 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____17245 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____17245 FStar_Pervasives_Native.fst))
in ((

let uu____17285 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____17285) with
| true -> begin
(

let uu____17286 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____17287 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____17288 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____17286 uu____17287 uu____17288))))
end
| uu____17289 -> begin
()
end));
(

let uu____17290 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____17290) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____17297 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____17297) with
| true -> begin
(

let uu____17298 = (

let uu____17305 = (

let uu____17306 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____17306 FStar_Syntax_Util.Equal))
in (match (uu____17305) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____17315 -> begin
(

let uu____17316 = (mk_eq2 wl orig t1 t2)
in (match (uu____17316) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____17298) with
| (guard, wl1) -> begin
(

let uu____17337 = (solve_prob orig guard [] wl1)
in (solve env uu____17337))
end))
end
| uu____17338 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____17339 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____17340, FStar_Syntax_Syntax.Tm_name (uu____17341)) -> begin
(

let head1 = (

let uu____17343 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____17343 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____17383 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____17383 FStar_Pervasives_Native.fst))
in ((

let uu____17423 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____17423) with
| true -> begin
(

let uu____17424 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____17425 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____17426 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____17424 uu____17425 uu____17426))))
end
| uu____17427 -> begin
()
end));
(

let uu____17428 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____17428) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____17435 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____17435) with
| true -> begin
(

let uu____17436 = (

let uu____17443 = (

let uu____17444 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____17444 FStar_Syntax_Util.Equal))
in (match (uu____17443) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____17453 -> begin
(

let uu____17454 = (mk_eq2 wl orig t1 t2)
in (match (uu____17454) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____17436) with
| (guard, wl1) -> begin
(

let uu____17475 = (solve_prob orig guard [] wl1)
in (solve env uu____17475))
end))
end
| uu____17476 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____17477 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____17478, FStar_Syntax_Syntax.Tm_constant (uu____17479)) -> begin
(

let head1 = (

let uu____17481 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____17481 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____17521 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____17521 FStar_Pervasives_Native.fst))
in ((

let uu____17561 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____17561) with
| true -> begin
(

let uu____17562 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____17563 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____17564 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____17562 uu____17563 uu____17564))))
end
| uu____17565 -> begin
()
end));
(

let uu____17566 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____17566) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____17573 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____17573) with
| true -> begin
(

let uu____17574 = (

let uu____17581 = (

let uu____17582 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____17582 FStar_Syntax_Util.Equal))
in (match (uu____17581) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____17591 -> begin
(

let uu____17592 = (mk_eq2 wl orig t1 t2)
in (match (uu____17592) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____17574) with
| (guard, wl1) -> begin
(

let uu____17613 = (solve_prob orig guard [] wl1)
in (solve env uu____17613))
end))
end
| uu____17614 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____17615 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____17616, FStar_Syntax_Syntax.Tm_fvar (uu____17617)) -> begin
(

let head1 = (

let uu____17619 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____17619 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____17659 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____17659 FStar_Pervasives_Native.fst))
in ((

let uu____17699 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____17699) with
| true -> begin
(

let uu____17700 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____17701 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____17702 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____17700 uu____17701 uu____17702))))
end
| uu____17703 -> begin
()
end));
(

let uu____17704 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____17704) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____17711 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____17711) with
| true -> begin
(

let uu____17712 = (

let uu____17719 = (

let uu____17720 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____17720 FStar_Syntax_Util.Equal))
in (match (uu____17719) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____17729 -> begin
(

let uu____17730 = (mk_eq2 wl orig t1 t2)
in (match (uu____17730) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____17712) with
| (guard, wl1) -> begin
(

let uu____17751 = (solve_prob orig guard [] wl1)
in (solve env uu____17751))
end))
end
| uu____17752 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____17753 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____17754, FStar_Syntax_Syntax.Tm_app (uu____17755)) -> begin
(

let head1 = (

let uu____17771 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____17771 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____17811 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____17811 FStar_Pervasives_Native.fst))
in ((

let uu____17851 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____17851) with
| true -> begin
(

let uu____17852 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____17853 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____17854 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____17852 uu____17853 uu____17854))))
end
| uu____17855 -> begin
()
end));
(

let uu____17856 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____17856) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____17863 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____17863) with
| true -> begin
(

let uu____17864 = (

let uu____17871 = (

let uu____17872 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____17872 FStar_Syntax_Util.Equal))
in (match (uu____17871) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____17881 -> begin
(

let uu____17882 = (mk_eq2 wl orig t1 t2)
in (match (uu____17882) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____17864) with
| (guard, wl1) -> begin
(

let uu____17903 = (solve_prob orig guard [] wl1)
in (solve env uu____17903))
end))
end
| uu____17904 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____17905 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_let (uu____17906), FStar_Syntax_Syntax.Tm_let (uu____17907)) -> begin
(

let uu____17932 = (FStar_Syntax_Util.term_eq t1 t2)
in (match (uu____17932) with
| true -> begin
(

let uu____17933 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____17933))
end
| uu____17934 -> begin
(giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig)
end))
end
| (FStar_Syntax_Syntax.Tm_let (uu____17935), uu____17936) -> begin
(

let uu____17949 = (

let uu____17954 = (

let uu____17955 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____17956 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____17957 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____17958 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)" uu____17955 uu____17956 uu____17957 uu____17958)))))
in ((FStar_Errors.Fatal_UnificationNotWellFormed), (uu____17954)))
in (FStar_Errors.raise_error uu____17949 t1.FStar_Syntax_Syntax.pos))
end
| (uu____17959, FStar_Syntax_Syntax.Tm_let (uu____17960)) -> begin
(

let uu____17973 = (

let uu____17978 = (

let uu____17979 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____17980 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____17981 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____17982 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)" uu____17979 uu____17980 uu____17981 uu____17982)))))
in ((FStar_Errors.Fatal_UnificationNotWellFormed), (uu____17978)))
in (FStar_Errors.raise_error uu____17973 t1.FStar_Syntax_Syntax.pos))
end
| uu____17983 -> begin
(giveup env "head tag mismatch" orig)
end));
)))
end));
))));
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

let uu____18042 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____18042) with
| true -> begin
(

let uu____18043 = (

let uu____18044 = (FStar_Syntax_Syntax.mk_Comp c1_comp)
in (FStar_Syntax_Print.comp_to_string uu____18044))
in (

let uu____18045 = (

let uu____18046 = (FStar_Syntax_Syntax.mk_Comp c2_comp)
in (FStar_Syntax_Print.comp_to_string uu____18046))
in (FStar_Util.print2 "solve_c is using an equality constraint (%s vs %s)\n" uu____18043 uu____18045)))
end
| uu____18047 -> begin
()
end));
(

let uu____18048 = (

let uu____18049 = (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)
in (not (uu____18049)))
in (match (uu____18048) with
| true -> begin
(

let uu____18050 = (

let uu____18051 = (FStar_Syntax_Print.lid_to_string c1_comp.FStar_Syntax_Syntax.effect_name)
in (

let uu____18052 = (FStar_Syntax_Print.lid_to_string c2_comp.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible effects: %s <> %s" uu____18051 uu____18052)))
in (giveup env uu____18050 orig))
end
| uu____18053 -> begin
(

let uu____18054 = (sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ FStar_TypeChecker_Common.EQ c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type")
in (match (uu____18054) with
| (ret_sub_prob, wl1) -> begin
(

let uu____18061 = (FStar_List.fold_right2 (fun uu____18094 uu____18095 uu____18096 -> (match (((uu____18094), (uu____18095), (uu____18096))) with
| ((a1, uu____18132), (a2, uu____18134), (arg_sub_probs, wl2)) -> begin
(

let uu____18155 = (sub_prob wl2 a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (match (uu____18155) with
| (p, wl3) -> begin
(((p)::arg_sub_probs), (wl3))
end))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args (([]), (wl1)))
in (match (uu____18061) with
| (arg_sub_probs, wl2) -> begin
(

let sub_probs = (ret_sub_prob)::arg_sub_probs
in (

let guard = (

let uu____18184 = (FStar_List.map p_guard sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____18184))
in (

let wl3 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl2)
in (solve env (attempt sub_probs wl3)))))
end))
end))
end));
))
in (

let solve_sub = (fun c11 edge c21 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let lift_c1 = (fun uu____18214 -> (

let wp = (match (c11.FStar_Syntax_Syntax.effect_args) with
| ((wp1, uu____18217))::[] -> begin
wp1
end
| uu____18234 -> begin
(

let uu____18243 = (

let uu____18244 = (

let uu____18245 = (FStar_Ident.range_of_lid c11.FStar_Syntax_Syntax.effect_name)
in (FStar_Range.string_of_range uu____18245))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" uu____18244))
in (failwith uu____18243))
end)
in (

let univs1 = (match (c11.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
(

let uu____18251 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (uu____18251)::[])
end
| x -> begin
x
end)
in (

let uu____18253 = (

let uu____18262 = (

let uu____18269 = (

let uu____18270 = (FStar_List.hd univs1)
in (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp uu____18270 c11.FStar_Syntax_Syntax.result_typ wp))
in (FStar_Syntax_Syntax.as_arg uu____18269))
in (uu____18262)::[])
in {FStar_Syntax_Syntax.comp_univs = univs1; FStar_Syntax_Syntax.effect_name = c21.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c11.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____18253; FStar_Syntax_Syntax.flags = c11.FStar_Syntax_Syntax.flags}))))
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____18283 = (lift_c1 ())
in (solve_eq uu____18283 c21))
end
| uu____18284 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___117_18289 -> (match (uu___117_18289) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| uu____18290 -> begin
false
end))))
in (

let uu____18291 = (match (((c11.FStar_Syntax_Syntax.effect_args), (c21.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____18325))::uu____18326, ((wp2, uu____18328))::uu____18329) -> begin
((wp1), (wp2))
end
| uu____18386 -> begin
(

let uu____18407 = (

let uu____18412 = (

let uu____18413 = (FStar_Syntax_Print.lid_to_string c11.FStar_Syntax_Syntax.effect_name)
in (

let uu____18414 = (FStar_Syntax_Print.lid_to_string c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____18413 uu____18414)))
in ((FStar_Errors.Fatal_ExpectNormalizedEffect), (uu____18412)))
in (FStar_Errors.raise_error uu____18407 env.FStar_TypeChecker_Env.range))
end)
in (match (uu____18291) with
| (wpc1, wpc2) -> begin
(

let uu____18433 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____18433) with
| true -> begin
(

let uu____18436 = (problem_using_guard orig c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ FStar_Pervasives_Native.None "result type")
in (solve_t env uu____18436 wl))
end
| uu____18437 -> begin
(

let uu____18438 = (

let uu____18445 = (FStar_TypeChecker_Env.effect_decl_opt env c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.must uu____18445))
in (match (uu____18438) with
| (c2_decl, qualifiers) -> begin
(

let uu____18466 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____18466) with
| true -> begin
(

let c1_repr = (

let uu____18470 = (

let uu____18471 = (

let uu____18472 = (lift_c1 ())
in (FStar_Syntax_Syntax.mk_Comp uu____18472))
in (

let uu____18473 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____18471 uu____18473)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env uu____18470))
in (

let c2_repr = (

let uu____18475 = (

let uu____18476 = (FStar_Syntax_Syntax.mk_Comp c21)
in (

let uu____18477 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____18476 uu____18477)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env uu____18475))
in (

let uu____18478 = (

let uu____18483 = (

let uu____18484 = (FStar_Syntax_Print.term_to_string c1_repr)
in (

let uu____18485 = (FStar_Syntax_Print.term_to_string c2_repr)
in (FStar_Util.format2 "sub effect repr: %s <: %s" uu____18484 uu____18485)))
in (sub_prob wl c1_repr problem.FStar_TypeChecker_Common.relation c2_repr uu____18483))
in (match (uu____18478) with
| (prob, wl1) -> begin
(

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some ((p_guard prob))) [] wl1)
in (solve env (attempt ((prob)::[]) wl2)))
end))))
end
| uu____18489 -> begin
(

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____18495 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____18499 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____18499) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____18500 -> begin
()
end));
(

let c1_univ = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____18502 = (

let uu____18509 = (

let uu____18510 = (

let uu____18525 = (FStar_TypeChecker_Env.inst_effect_fun_with ((c1_univ)::[]) env c2_decl c2_decl.FStar_Syntax_Syntax.trivial)
in (

let uu____18528 = (

let uu____18537 = (FStar_Syntax_Syntax.as_arg c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____18544 = (

let uu____18553 = (

let uu____18560 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c1_univ c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____18560))
in (uu____18553)::[])
in (uu____18537)::uu____18544))
in ((uu____18525), (uu____18528))))
in FStar_Syntax_Syntax.Tm_app (uu____18510))
in (FStar_Syntax_Syntax.mk uu____18509))
in (uu____18502 FStar_Pervasives_Native.None r)));
)
end
| uu____18598 -> begin
(

let c1_univ = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (

let c2_univ = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____18601 = (

let uu____18608 = (

let uu____18609 = (

let uu____18624 = (FStar_TypeChecker_Env.inst_effect_fun_with ((c2_univ)::[]) env c2_decl c2_decl.FStar_Syntax_Syntax.stronger)
in (

let uu____18627 = (

let uu____18636 = (FStar_Syntax_Syntax.as_arg c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____18643 = (

let uu____18652 = (FStar_Syntax_Syntax.as_arg wpc2)
in (

let uu____18659 = (

let uu____18668 = (

let uu____18675 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c1_univ c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____18675))
in (uu____18668)::[])
in (uu____18652)::uu____18659))
in (uu____18636)::uu____18643))
in ((uu____18624), (uu____18627))))
in FStar_Syntax_Syntax.Tm_app (uu____18609))
in (FStar_Syntax_Syntax.mk uu____18608))
in (uu____18601 FStar_Pervasives_Native.None r))))
end)
end)
in (

let uu____18719 = (sub_prob wl c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ "result type")
in (match (uu____18719) with
| (base_prob, wl1) -> begin
(

let wl2 = (

let uu____18727 = (

let uu____18730 = (FStar_Syntax_Util.mk_conj (p_guard base_prob) g)
in (FStar_All.pipe_left (fun _0_26 -> FStar_Pervasives_Native.Some (_0_26)) uu____18730))
in (solve_prob orig uu____18727 [] wl1))
in (solve env (attempt ((base_prob)::[]) wl2)))
end)))
end))
end))
end))
end)))
end))))
in (

let uu____18733 = (FStar_Util.physical_equality c1 c2)
in (match (uu____18733) with
| true -> begin
(

let uu____18734 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____18734))
end
| uu____18735 -> begin
((

let uu____18737 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____18737) with
| true -> begin
(

let uu____18738 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____18739 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____18738 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____18739)))
end
| uu____18740 -> begin
()
end));
(

let uu____18741 = (

let uu____18750 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____18753 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____18750), (uu____18753))))
in (match (uu____18741) with
| (c11, c21) -> begin
(match (((c11.FStar_Syntax_Syntax.n), (c21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____18771), FStar_Syntax_Syntax.Total (t2, uu____18773)) when (FStar_Syntax_Util.non_informative t2) -> begin
(

let uu____18790 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____18790 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____18791), FStar_Syntax_Syntax.Total (uu____18792)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| (FStar_Syntax_Syntax.Total (t1, uu____18810), FStar_Syntax_Syntax.Total (t2, uu____18812)) -> begin
(

let uu____18829 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____18829 wl))
end
| (FStar_Syntax_Syntax.GTotal (t1, uu____18831), FStar_Syntax_Syntax.GTotal (t2, uu____18833)) -> begin
(

let uu____18850 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____18850 wl))
end
| (FStar_Syntax_Syntax.Total (t1, uu____18852), FStar_Syntax_Syntax.GTotal (t2, uu____18854)) -> begin
(

let uu____18871 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____18871 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____18872), FStar_Syntax_Syntax.Comp (uu____18873)) -> begin
(

let uu____18882 = (

let uu___168_18885 = problem
in (

let uu____18888 = (

let uu____18889 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____18889))
in {FStar_TypeChecker_Common.pid = uu___168_18885.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____18888; FStar_TypeChecker_Common.relation = uu___168_18885.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___168_18885.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___168_18885.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___168_18885.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___168_18885.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___168_18885.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___168_18885.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___168_18885.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____18882 wl))
end
| (FStar_Syntax_Syntax.Total (uu____18890), FStar_Syntax_Syntax.Comp (uu____18891)) -> begin
(

let uu____18900 = (

let uu___168_18903 = problem
in (

let uu____18906 = (

let uu____18907 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____18907))
in {FStar_TypeChecker_Common.pid = uu___168_18903.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____18906; FStar_TypeChecker_Common.relation = uu___168_18903.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___168_18903.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___168_18903.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___168_18903.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___168_18903.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___168_18903.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___168_18903.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___168_18903.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____18900 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____18908), FStar_Syntax_Syntax.GTotal (uu____18909)) -> begin
(

let uu____18918 = (

let uu___169_18921 = problem
in (

let uu____18924 = (

let uu____18925 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____18925))
in {FStar_TypeChecker_Common.pid = uu___169_18921.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___169_18921.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___169_18921.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____18924; FStar_TypeChecker_Common.element = uu___169_18921.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___169_18921.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___169_18921.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___169_18921.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___169_18921.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___169_18921.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____18918 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____18926), FStar_Syntax_Syntax.Total (uu____18927)) -> begin
(

let uu____18936 = (

let uu___169_18939 = problem
in (

let uu____18942 = (

let uu____18943 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____18943))
in {FStar_TypeChecker_Common.pid = uu___169_18939.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___169_18939.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___169_18939.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____18942; FStar_TypeChecker_Common.element = uu___169_18939.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___169_18939.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___169_18939.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.reason = uu___169_18939.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___169_18939.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___169_18939.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____18936 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____18944), FStar_Syntax_Syntax.Comp (uu____18945)) -> begin
(

let uu____18946 = ((((FStar_Syntax_Util.is_ml_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) || ((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_total_comp c21))) || (((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB)))
in (match (uu____18946) with
| true -> begin
(

let uu____18947 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c11) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c21) FStar_Pervasives_Native.None "result type")
in (solve_t env uu____18947 wl))
end
| uu____18948 -> begin
(

let c1_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (

let c2_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____18951 = (

let uu____18956 = (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)
in (match (uu____18956) with
| true -> begin
((c1_comp), (c2_comp))
end
| uu____18961 -> begin
(

let uu____18962 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let uu____18963 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((uu____18962), (uu____18963))))
end))
in (match (uu____18951) with
| (c1_comp1, c2_comp1) -> begin
(solve_eq c1_comp1 c2_comp1)
end))
end
| uu____18966 -> begin
(

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((

let uu____18970 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____18970) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c12.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c22.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____18971 -> begin
()
end));
(

let uu____18972 = (FStar_TypeChecker_Env.monad_leq env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____18972) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18975 = (

let uu____18976 = (FStar_Syntax_Print.lid_to_string c12.FStar_Syntax_Syntax.effect_name)
in (

let uu____18977 = (FStar_Syntax_Print.lid_to_string c22.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____18976 uu____18977)))
in (giveup env uu____18975 orig))
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

let uu____18984 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____19017 -> (match (uu____19017) with
| (uu____19028, tm, uu____19030, uu____19031, uu____19032) -> begin
(FStar_Syntax_Print.term_to_string tm)
end))))
in (FStar_All.pipe_right uu____18984 (FStar_String.concat ", "))))


let ineqs_to_string : (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.string = (fun ineqs -> (

let vars = (

let uu____19065 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs) (FStar_List.map FStar_Syntax_Print.univ_to_string))
in (FStar_All.pipe_right uu____19065 (FStar_String.concat ", ")))
in (

let ineqs1 = (

let uu____19083 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs) (FStar_List.map (fun uu____19111 -> (match (uu____19111) with
| (u1, u2) -> begin
(

let uu____19118 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____19119 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "%s < %s" uu____19118 uu____19119)))
end))))
in (FStar_All.pipe_right uu____19083 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred), (g.FStar_TypeChecker_Env.univ_ineqs))) with
| (FStar_TypeChecker_Common.Trivial, [], (uu____19146, [])) -> begin
"{}"
end
| uu____19171 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____19194 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____19194) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____19195 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____19197 = (FStar_List.map (fun uu____19207 -> (match (uu____19207) with
| (uu____19212, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right uu____19197 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (

let uu____19217 = (ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs)
in (FStar_Util.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n" form carry uu____19217 imps)))))
end))


let new_t_problem : worklist  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  (FStar_TypeChecker_Common.prob * worklist) = (fun wl env lhs rel rhs elt loc -> (

let reason = (

let uu____19270 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____19270) with
| true -> begin
(

let uu____19271 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____19272 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____19271 (rel_to_string rel) uu____19272)))
end
| uu____19273 -> begin
"TOP"
end))
in (

let uu____19274 = (new_problem wl env lhs rel rhs elt loc reason)
in (match (uu____19274) with
| (p, wl1) -> begin
((FStar_TypeChecker_Common.TProb (p)), (wl1))
end))))


let new_t_prob : worklist  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv * worklist) = (fun wl env t1 rel t2 -> (

let x = (

let uu____19331 = (

let uu____19334 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_27 -> FStar_Pervasives_Native.Some (_0_27)) uu____19334))
in (FStar_Syntax_Syntax.new_bv uu____19331 t1))
in (

let uu____19337 = (

let uu____19342 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some (x)) uu____19342))
in (match (uu____19337) with
| (p, wl1) -> begin
((p), (x), (wl1))
end))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits) FStar_Pervasives_Native.option)  ->  (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits) FStar_Pervasives_Native.option = (fun env probs err -> (

let probs1 = (

let uu____19398 = (FStar_Options.eager_inference ())
in (match (uu____19398) with
| true -> begin
(

let uu___170_19399 = probs
in {attempting = uu___170_19399.attempting; wl_deferred = uu___170_19399.wl_deferred; ctr = uu___170_19399.ctr; defer_ok = false; smt_ok = uu___170_19399.smt_ok; tcenv = uu___170_19399.tcenv; wl_implicits = uu___170_19399.wl_implicits})
end
| uu____19400 -> begin
probs
end))
in (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let sol = (solve env probs1)
in (match (sol) with
| Success (deferred, implicits) -> begin
((FStar_Syntax_Unionfind.commit tx);
FStar_Pervasives_Native.Some (((deferred), (implicits)));
)
end
| Failed (d, s) -> begin
((

let uu____19419 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____19419) with
| true -> begin
(

let uu____19420 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____19420))
end
| uu____19421 -> begin
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

let uu____19442 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____19442) with
| true -> begin
(

let uu____19443 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____19443))
end
| uu____19444 -> begin
()
end));
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env f)
in ((

let uu____19447 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____19447) with
| true -> begin
(

let uu____19448 = (FStar_Syntax_Print.term_to_string f1)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____19448))
end
| uu____19449 -> begin
()
end));
(

let f2 = (

let uu____19451 = (

let uu____19452 = (FStar_Syntax_Util.unmeta f1)
in uu____19452.FStar_Syntax_Syntax.n)
in (match (uu____19451) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____19456 -> begin
FStar_TypeChecker_Common.NonTrivial (f1)
end))
in (

let uu___171_19457 = g
in {FStar_TypeChecker_Env.guard_f = f2; FStar_TypeChecker_Env.deferred = uu___171_19457.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___171_19457.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___171_19457.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  (FStar_TypeChecker_Common.deferred * (Prims.string * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar * FStar_Range.range * Prims.bool) Prims.list) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (deferred, implicits) -> begin
(

let uu____19571 = (

let uu____19572 = (

let uu____19573 = (FStar_All.pipe_right (p_guard prob) (fun _0_28 -> FStar_TypeChecker_Common.NonTrivial (_0_28)))
in {FStar_TypeChecker_Env.guard_f = uu____19573; FStar_TypeChecker_Env.deferred = deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = implicits})
in (simplify_guard env uu____19572))
in (FStar_All.pipe_left (fun _0_29 -> FStar_Pervasives_Native.Some (_0_29)) uu____19571))
end))


let with_guard_no_simp : 'Auu____19588 . 'Auu____19588  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____19611 = (

let uu____19612 = (FStar_All.pipe_right (p_guard prob) (fun _0_30 -> FStar_TypeChecker_Common.NonTrivial (_0_30)))
in {FStar_TypeChecker_Env.guard_f = uu____19612; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in FStar_Pervasives_Native.Some (uu____19611))
end))


let try_teq : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun smt_ok env t1 t2 -> ((

let uu____19652 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____19652) with
| true -> begin
(

let uu____19653 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____19654 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" uu____19653 uu____19654)))
end
| uu____19655 -> begin
()
end));
(

let uu____19656 = (

let uu____19661 = (empty_worklist env)
in (

let uu____19662 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem uu____19661 env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None uu____19662)))
in (match (uu____19656) with
| (prob, wl) -> begin
(

let g = (

let uu____19670 = (solve_and_commit env (singleton wl prob smt_ok) (fun uu____19690 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob) uu____19670))
in g)
end));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____19734 = (try_teq true env t1 t2)
in (match (uu____19734) with
| FStar_Pervasives_Native.None -> begin
((

let uu____19738 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____19739 = (FStar_TypeChecker_Err.basic_type_error env FStar_Pervasives_Native.None t2 t1)
in (FStar_Errors.log_issue uu____19738 uu____19739)));
trivial_guard;
)
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____19746 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____19746) with
| true -> begin
(

let uu____19747 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____19748 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____19749 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____19747 uu____19748 uu____19749))))
end
| uu____19750 -> begin
()
end));
g;
)
end)))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun env e t1 t2 -> (

let uu____19771 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____19772 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t2 t1)
in (FStar_Errors.log_issue uu____19771 uu____19772))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env c1 c2 -> (

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____19795 -> begin
FStar_TypeChecker_Common.SUB
end)
in ((

let uu____19797 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____19797) with
| true -> begin
(

let uu____19798 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____19799 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n" uu____19798 uu____19799 (match ((Prims.op_Equality rel FStar_TypeChecker_Common.EQ)) with
| true -> begin
"EQ"
end
| uu____19800 -> begin
"SUB"
end))))
end
| uu____19801 -> begin
()
end));
(

let uu____19802 = (

let uu____19809 = (empty_worklist env)
in (

let uu____19810 = (FStar_TypeChecker_Env.get_range env)
in (new_problem uu____19809 env c1 rel c2 FStar_Pervasives_Native.None uu____19810 "sub_comp")))
in (match (uu____19802) with
| (prob, wl) -> begin
(

let prob1 = FStar_TypeChecker_Common.CProb (prob)
in (

let uu____19820 = (solve_and_commit env (singleton wl prob1 true) (fun uu____19840 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob1) uu____19820)))
end));
)))


let solve_universe_inequalities' : FStar_Syntax_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  unit = (fun tx env uu____19895 -> (match (uu____19895) with
| (variables, ineqs) -> begin
(

let fail1 = (fun u1 u2 -> ((FStar_Syntax_Unionfind.rollback tx);
(

let uu____19938 = (

let uu____19943 = (

let uu____19944 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____19945 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Universe %s and %s are incompatible" uu____19944 uu____19945)))
in ((FStar_Errors.Fatal_IncompatibleUniverse), (uu____19943)))
in (

let uu____19946 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____19938 uu____19946)));
))
in (

let equiv1 = (fun v1 v' -> (

let uu____19958 = (

let uu____19963 = (FStar_Syntax_Subst.compress_univ v1)
in (

let uu____19964 = (FStar_Syntax_Subst.compress_univ v')
in ((uu____19963), (uu____19964))))
in (match (uu____19958) with
| (FStar_Syntax_Syntax.U_unif (v0), FStar_Syntax_Syntax.U_unif (v0')) -> begin
(FStar_Syntax_Unionfind.univ_equiv v0 v0')
end
| uu____19983 -> begin
false
end)))
in (

let sols = (FStar_All.pipe_right variables (FStar_List.collect (fun v1 -> (

let uu____20013 = (FStar_Syntax_Subst.compress_univ v1)
in (match (uu____20013) with
| FStar_Syntax_Syntax.U_unif (uu____20020) -> begin
(

let lower_bounds_of_v = (FStar_All.pipe_right ineqs (FStar_List.collect (fun uu____20049 -> (match (uu____20049) with
| (u, v') -> begin
(

let uu____20058 = (equiv1 v1 v')
in (match (uu____20058) with
| true -> begin
(

let uu____20061 = (FStar_All.pipe_right variables (FStar_Util.for_some (equiv1 u)))
in (match (uu____20061) with
| true -> begin
[]
end
| uu____20066 -> begin
(u)::[]
end))
end
| uu____20067 -> begin
[]
end))
end))))
in (

let lb = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max (lower_bounds_of_v)))
in (((lb), (v1)))::[]))
end
| uu____20077 -> begin
[]
end)))))
in (

let uu____20082 = (

let wl = (

let uu___172_20086 = (empty_worklist env)
in {attempting = uu___172_20086.attempting; wl_deferred = uu___172_20086.wl_deferred; ctr = uu___172_20086.ctr; defer_ok = false; smt_ok = uu___172_20086.smt_ok; tcenv = uu___172_20086.tcenv; wl_implicits = uu___172_20086.wl_implicits})
in (FStar_All.pipe_right sols (FStar_List.map (fun uu____20104 -> (match (uu____20104) with
| (lb, v1) -> begin
(

let uu____20111 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl lb v1)
in (match (uu____20111) with
| USolved (wl1) -> begin
()
end
| uu____20113 -> begin
(fail1 lb v1)
end))
end)))))
in (

let rec check_ineq = (fun uu____20123 -> (match (uu____20123) with
| (u, v1) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u)
in (

let v2 = (FStar_TypeChecker_Normalize.normalize_universe env v1)
in (match (((u1), (v2))) with
| (FStar_Syntax_Syntax.U_zero, uu____20132) -> begin
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
| (FStar_Syntax_Syntax.U_name (uu____20155), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_unif (uu____20157), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_max (us), uu____20168) -> begin
(FStar_All.pipe_right us (FStar_Util.for_all (fun u2 -> (check_ineq ((u2), (v2))))))
end
| (uu____20175, FStar_Syntax_Syntax.U_max (vs)) -> begin
(FStar_All.pipe_right vs (FStar_Util.for_some (fun v3 -> (check_ineq ((u1), (v3))))))
end
| uu____20183 -> begin
false
end)))
end))
in (

let uu____20188 = (FStar_All.pipe_right ineqs (FStar_Util.for_all (fun uu____20203 -> (match (uu____20203) with
| (u, v1) -> begin
(

let uu____20210 = (check_ineq ((u), (v1)))
in (match (uu____20210) with
| true -> begin
true
end
| uu____20211 -> begin
((

let uu____20213 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____20213) with
| true -> begin
(

let uu____20214 = (FStar_Syntax_Print.univ_to_string u)
in (

let uu____20215 = (FStar_Syntax_Print.univ_to_string v1)
in (FStar_Util.print2 "%s </= %s" uu____20214 uu____20215)))
end
| uu____20216 -> begin
()
end));
false;
)
end))
end))))
in (match (uu____20188) with
| true -> begin
()
end
| uu____20217 -> begin
((

let uu____20219 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____20219) with
| true -> begin
((

let uu____20221 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Partially solved inequality constraints are: %s\n" uu____20221));
(FStar_Syntax_Unionfind.rollback tx);
(

let uu____20231 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Original solved inequality constraints are: %s\n" uu____20231));
)
end
| uu____20240 -> begin
()
end));
(

let uu____20241 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_FailToSolveUniverseInEquality), ("Failed to solve universe inequalities for inductives")) uu____20241));
)
end)))))))
end))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  unit = (fun env ineqs -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Syntax_Unionfind.commit tx);
)))


let try_solve_deferred_constraints : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun defer_ok env g -> (

let fail1 = (fun uu____20308 -> (match (uu____20308) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ErrorInSolveDeferredConstraints), (msg)) (p_loc d)))
end))
in (

let wl = (

let uu___173_20329 = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in {attempting = uu___173_20329.attempting; wl_deferred = uu___173_20329.wl_deferred; ctr = uu___173_20329.ctr; defer_ok = defer_ok; smt_ok = uu___173_20329.smt_ok; tcenv = uu___173_20329.tcenv; wl_implicits = uu___173_20329.wl_implicits})
in ((

let uu____20331 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____20331) with
| true -> begin
(

let uu____20332 = (FStar_Util.string_of_bool defer_ok)
in (

let uu____20333 = (wl_to_string wl)
in (

let uu____20334 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print3 "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n" uu____20332 uu____20333 uu____20334))))
end
| uu____20345 -> begin
()
end));
(

let g1 = (

let uu____20347 = (solve_and_commit env wl fail1)
in (match (uu____20347) with
| FStar_Pervasives_Native.Some ((uu____20354)::uu____20355, uu____20356) when (not (defer_ok)) -> begin
(failwith "Impossible: Unexpected deferred constraints remain")
end
| FStar_Pervasives_Native.Some (deferred, imps) -> begin
(

let uu___174_20381 = g
in {FStar_TypeChecker_Env.guard_f = uu___174_20381.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = deferred; FStar_TypeChecker_Env.univ_ineqs = uu___174_20381.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)})
end
| uu____20392 -> begin
(failwith "Impossible: should have raised a failure already")
end))
in ((solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___175_20400 = g1
in {FStar_TypeChecker_Env.guard_f = uu___175_20400.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___175_20400.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = uu___175_20400.FStar_TypeChecker_Env.implicits});
));
))))


let solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (try_solve_deferred_constraints false env g))


let solve_some_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (try_solve_deferred_constraints true env g))


let last_proof_ns : FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let maybe_update_proof_ns : FStar_TypeChecker_Env.env  ->  unit = (fun env -> (

let pns = env.FStar_TypeChecker_Env.proof_ns
in (

let uu____20448 = (FStar_ST.op_Bang last_proof_ns)
in (match (uu____20448) with
| FStar_Pervasives_Native.None -> begin
(FStar_ST.op_Colon_Equals last_proof_ns (FStar_Pervasives_Native.Some (pns)))
end
| FStar_Pervasives_Native.Some (old) -> begin
(match ((Prims.op_Equality old pns)) with
| true -> begin
()
end
| uu____20506 -> begin
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

let uu___176_20571 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___176_20571.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___176_20571.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___176_20571.FStar_TypeChecker_Env.implicits})
in (

let uu____20572 = (

let uu____20573 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____20573)))
in (match (uu____20572) with
| true -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| uu____20576 -> begin
(match (g1.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((match (debug1) with
| true -> begin
(

let uu____20581 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____20582 = (

let uu____20583 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____20583))
in (FStar_Errors.diag uu____20581 uu____20582)))
end
| uu____20584 -> begin
()
end);
(

let vc1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env vc)
in ((match (debug1) with
| true -> begin
(

let uu____20587 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____20588 = (

let uu____20589 = (FStar_Syntax_Print.term_to_string vc1)
in (FStar_Util.format1 "After normalization VC=\n%s\n" uu____20589))
in (FStar_Errors.diag uu____20587 uu____20588)))
end
| uu____20590 -> begin
()
end);
(

let uu____20592 = (FStar_TypeChecker_Env.get_range env)
in (def_check_closed_in_env uu____20592 "discharge_guard\'" env vc1));
(

let uu____20593 = (check_trivial vc1)
in (match (uu____20593) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc2) -> begin
(match ((not (use_smt))) with
| true -> begin
((match (debug1) with
| true -> begin
(

let uu____20600 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____20601 = (

let uu____20602 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Cannot solve without SMT : %s\n" uu____20602))
in (FStar_Errors.diag uu____20600 uu____20601)))
end
| uu____20603 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end
| uu____20604 -> begin
((match (debug1) with
| true -> begin
(

let uu____20607 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____20608 = (

let uu____20609 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____20609))
in (FStar_Errors.diag uu____20607 uu____20608)))
end
| uu____20610 -> begin
()
end);
(

let vcs = (

let uu____20620 = (FStar_Options.use_tactics ())
in (match (uu____20620) with
| true -> begin
(FStar_Options.with_saved_options (fun uu____20639 -> ((

let uu____20641 = (FStar_Options.set_options FStar_Options.Set "--no_tactics")
in (FStar_All.pipe_left (fun a238 -> ()) uu____20641));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.preprocess env vc2);
)))
end
| uu____20642 -> begin
(

let uu____20643 = (

let uu____20650 = (FStar_Options.peek ())
in ((env), (vc2), (uu____20650)))
in (uu____20643)::[])
end))
in (FStar_All.pipe_right vcs (FStar_List.iter (fun uu____20684 -> (match (uu____20684) with
| (env1, goal, opts) -> begin
(

let goal1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env1 goal)
in (

let uu____20695 = (check_trivial goal1)
in (match (uu____20695) with
| FStar_TypeChecker_Common.Trivial -> begin
(match (debug1) with
| true -> begin
(FStar_Util.print_string "Goal completely solved by tactic\n")
end
| uu____20697 -> begin
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

let uu____20703 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____20704 = (

let uu____20705 = (FStar_Syntax_Print.term_to_string goal2)
in (

let uu____20706 = (FStar_TypeChecker_Env.string_of_proof_ns env1)
in (FStar_Util.format2 "Trying to solve:\n> %s\nWith proof_ns:\n %s\n" uu____20705 uu____20706)))
in (FStar_Errors.diag uu____20703 uu____20704)))
end
| uu____20707 -> begin
()
end);
(match (debug1) with
| true -> begin
(

let uu____20709 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____20710 = (

let uu____20711 = (FStar_Syntax_Print.term_to_string goal2)
in (FStar_Util.format1 "Before calling solver VC=\n%s\n" uu____20711))
in (FStar_Errors.diag uu____20709 uu____20710)))
end
| uu____20712 -> begin
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

let uu____20725 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____20725) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____20732 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ExpectTrivialPreCondition), ("Expected a trivial pre-condition")) uu____20732))
end)))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let uu____20743 = (discharge_guard' FStar_Pervasives_Native.None env g true)
in (match (uu____20743) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end)))


let resolve_implicits' : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env must_total forcelax g -> (

let unresolved = (fun u -> (

let uu____20776 = (FStar_Syntax_Util.head_and_args u)
in (match (uu____20776) with
| (hd1, uu____20792) -> begin
(

let uu____20813 = (

let uu____20814 = (FStar_Syntax_Subst.compress u)
in uu____20814.FStar_Syntax_Syntax.n)
in (match (uu____20813) with
| FStar_Syntax_Syntax.Tm_uvar (uu____20817) -> begin
true
end
| uu____20818 -> begin
false
end))
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____20838 = acc
in (match (uu____20838) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____20855 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd1)::tl1 -> begin
(

let uu____20900 = hd1
in (match (uu____20900) with
| (reason, tm, ctx_u, r, should_check) -> begin
(match ((not (should_check))) with
| true -> begin
(until_fixpoint ((out), (true)) tl1)
end
| uu____20916 -> begin
(

let uu____20917 = (unresolved tm)
in (match (uu____20917) with
| true -> begin
(until_fixpoint (((hd1)::out), (changed)) tl1)
end
| uu____20928 -> begin
(

let env1 = (

let uu___177_20930 = env
in {FStar_TypeChecker_Env.solver = uu___177_20930.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___177_20930.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___177_20930.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_TypeChecker_Env.gamma_sig = uu___177_20930.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___177_20930.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___177_20930.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___177_20930.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___177_20930.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___177_20930.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___177_20930.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___177_20930.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___177_20930.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___177_20930.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___177_20930.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___177_20930.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___177_20930.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___177_20930.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___177_20930.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___177_20930.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___177_20930.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___177_20930.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___177_20930.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___177_20930.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___177_20930.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___177_20930.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___177_20930.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___177_20930.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___177_20930.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___177_20930.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___177_20930.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___177_20930.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___177_20930.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___177_20930.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___177_20930.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___177_20930.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___177_20930.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___177_20930.FStar_TypeChecker_Env.dep_graph})
in (

let tm1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 tm)
in (

let env2 = (match (forcelax) with
| true -> begin
(

let uu___178_20933 = env1
in {FStar_TypeChecker_Env.solver = uu___178_20933.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___178_20933.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___178_20933.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___178_20933.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___178_20933.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___178_20933.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___178_20933.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___178_20933.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___178_20933.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___178_20933.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___178_20933.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___178_20933.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___178_20933.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___178_20933.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___178_20933.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___178_20933.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___178_20933.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___178_20933.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___178_20933.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___178_20933.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___178_20933.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___178_20933.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___178_20933.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___178_20933.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___178_20933.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___178_20933.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___178_20933.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___178_20933.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___178_20933.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___178_20933.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___178_20933.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___178_20933.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___178_20933.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___178_20933.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___178_20933.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___178_20933.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___178_20933.FStar_TypeChecker_Env.dep_graph})
end
| uu____20934 -> begin
env1
end)
in ((

let uu____20936 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("RelCheck")))
in (match (uu____20936) with
| true -> begin
(

let uu____20937 = (FStar_Syntax_Print.uvar_to_string ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____20938 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____20939 = (FStar_Syntax_Print.term_to_string ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (

let uu____20940 = (FStar_Range.string_of_range r)
in (FStar_Util.print5 "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n" uu____20937 uu____20938 uu____20939 reason uu____20940)))))
end
| uu____20941 -> begin
()
end));
(

let g1 = (FStar_All.try_with (fun uu___180_20944 -> (match (()) with
| () -> begin
(env2.FStar_TypeChecker_Env.check_type_of must_total env2 tm1 ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
end)) (fun uu___179_20948 -> (match (uu___179_20948) with
| e -> begin
((

let uu____20951 = (

let uu____20960 = (

let uu____20967 = (

let uu____20968 = (FStar_Syntax_Print.uvar_to_string ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____20969 = (FStar_TypeChecker_Normalize.term_to_string env2 tm1)
in (FStar_Util.format2 "Failed while checking implicit %s set to %s" uu____20968 uu____20969)))
in ((FStar_Errors.Error_BadImplicit), (uu____20967), (r)))
in (uu____20960)::[])
in (FStar_Errors.add_errors uu____20951));
(FStar_Exn.raise e);
)
end)))
in (

let g2 = (match (env2.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___181_20983 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___181_20983.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___181_20983.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___181_20983.FStar_TypeChecker_Env.implicits})
end
| uu____20984 -> begin
g1
end)
in (

let g' = (

let uu____20986 = (discharge_guard' (FStar_Pervasives_Native.Some ((fun uu____20993 -> (FStar_Syntax_Print.term_to_string tm1)))) env2 g2 true)
in (match (uu____20986) with
| FStar_Pervasives_Native.Some (g3) -> begin
g3
end
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end))
in (until_fixpoint (((FStar_List.append g'.FStar_TypeChecker_Env.implicits out)), (true)) tl1))));
))))
end))
end)
end))
end)
end)))
in (

let uu___182_21005 = g
in (

let uu____21006 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___182_21005.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___182_21005.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___182_21005.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____21006})))))


let resolve_implicits : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (resolve_implicits' env true false g))


let resolve_implicits_tac : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (resolve_implicits' env false true g))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  unit = (fun env g -> (

let g1 = (

let uu____21060 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____21060 (resolve_implicits env)))
in (match (g1.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(

let uu____21071 = (discharge_guard env g1)
in (FStar_All.pipe_left (fun a239 -> ()) uu____21071))
end
| ((reason, e, ctx_u, r, should_check))::uu____21077 -> begin
(

let uu____21100 = (

let uu____21105 = (

let uu____21106 = (FStar_Syntax_Print.uvar_to_string ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____21107 = (FStar_TypeChecker_Normalize.term_to_string env ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (

let uu____21108 = (FStar_Util.string_of_bool should_check)
in (FStar_Util.format4 "Failed to resolve implicit argument %s of type %s introduced for %s (should check=%s)" uu____21106 uu____21107 reason uu____21108))))
in ((FStar_Errors.Fatal_FailToResolveImplicitArgument), (uu____21105)))
in (FStar_Errors.raise_error uu____21100 r))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___183_21119 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___183_21119.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___183_21119.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ((((u1), (u2)))::[])); FStar_TypeChecker_Env.implicits = uu___183_21119.FStar_TypeChecker_Env.implicits}))


let discharge_guard_nosmt : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun env g -> (

let uu____21134 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____21134) with
| FStar_Pervasives_Native.Some (uu____21140) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end)))


let teq_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____21156 = (try_teq false env t1 t2)
in (match (uu____21156) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g) -> begin
(discharge_guard_nosmt env g)
end)))


let check_subtyping : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.option = (fun env t1 t2 -> ((

let uu____21190 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____21190) with
| true -> begin
(

let uu____21191 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____21192 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "check_subtyping of %s and %s\n" uu____21191 uu____21192)))
end
| uu____21193 -> begin
()
end));
(

let uu____21194 = (

let uu____21201 = (empty_worklist env)
in (new_t_prob uu____21201 env t1 FStar_TypeChecker_Common.SUB t2))
in (match (uu____21194) with
| (prob, x, wl) -> begin
(

let g = (

let uu____21214 = (solve_and_commit env (singleton wl prob true) (fun uu____21234 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob) uu____21214))
in ((

let uu____21264 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____21264) with
| true -> begin
(

let uu____21265 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____21266 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____21267 = (

let uu____21268 = (FStar_Util.must g)
in (guard_to_string env uu____21268))
in (FStar_Util.print3 "check_subtyping succeeded: %s <: %s\n\tguard is %s\n" uu____21265 uu____21266 uu____21267))))
end
| uu____21269 -> begin
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

let uu____21302 = (check_subtyping env t1 t2)
in (match (uu____21302) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (x, g) -> begin
(

let uu____21321 = (

let uu____21322 = (FStar_Syntax_Syntax.mk_binder x)
in (abstract_guard uu____21322 g))
in FStar_Pervasives_Native.Some (uu____21321))
end)))


let get_subtyping_prop : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> (

let uu____21340 = (check_subtyping env t1 t2)
in (match (uu____21340) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (x, g) -> begin
(

let uu____21359 = (

let uu____21360 = (

let uu____21361 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____21361)::[])
in (close_guard env uu____21360 g))
in FStar_Pervasives_Native.Some (uu____21359))
end)))


let subtype_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> ((

let uu____21390 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____21390) with
| true -> begin
(

let uu____21391 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____21392 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____21391 uu____21392)))
end
| uu____21393 -> begin
()
end));
(

let uu____21394 = (

let uu____21401 = (empty_worklist env)
in (new_t_prob uu____21401 env t1 FStar_TypeChecker_Common.SUB t2))
in (match (uu____21394) with
| (prob, x, wl) -> begin
(

let g = (

let uu____21408 = (solve_and_commit env (singleton wl prob false) (fun uu____21428 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob) uu____21408))
in (match (g) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g1) -> begin
(

let g2 = (

let uu____21459 = (

let uu____21460 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____21460)::[])
in (close_guard env uu____21459 g1))
in (discharge_guard_nosmt env g2))
end))
end));
))





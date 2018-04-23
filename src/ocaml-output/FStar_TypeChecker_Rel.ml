
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

let uu___110_102 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.NonTrivial (f'); FStar_TypeChecker_Env.deferred = uu___110_102.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___110_102.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___110_102.FStar_TypeChecker_Env.implicits}))
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

let uu___111_248 = g
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
in {FStar_TypeChecker_Env.guard_f = uu____249; FStar_TypeChecker_Env.deferred = uu___111_248.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___111_248.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___111_248.FStar_TypeChecker_Env.implicits}))
end))


let map_guard : FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  FStar_TypeChecker_Env.guard_t = (fun g map1 -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___112_313 = g
in (

let uu____314 = (

let uu____315 = (map1 f)
in FStar_TypeChecker_Common.NonTrivial (uu____315))
in {FStar_TypeChecker_Env.guard_f = uu____314; FStar_TypeChecker_Env.deferred = uu___112_313.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___112_313.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___112_313.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____321) -> begin
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

let uu____336 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (uu____336))
end))


let check_trivial : FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (

let uu____342 = (

let uu____343 = (FStar_Syntax_Util.unmeta t)
in uu____343.FStar_Syntax_Syntax.n)
in (match (uu____342) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____347 -> begin
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

let uu____388 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = uu____388; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (((FStar_List.append (FStar_Pervasives_Native.fst g1.FStar_TypeChecker_Env.univ_ineqs) (FStar_Pervasives_Native.fst g2.FStar_TypeChecker_Env.univ_ineqs))), ((FStar_List.append (FStar_Pervasives_Native.snd g1.FStar_TypeChecker_Env.univ_ineqs) (FStar_Pervasives_Native.snd g2.FStar_TypeChecker_Env.univ_ineqs)))); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard_univs : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun us bs g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let f1 = (FStar_List.fold_right2 (fun u b f1 -> (

let uu____467 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____467) with
| true -> begin
f1
end
| uu____468 -> begin
(FStar_Syntax_Util.mk_forall u (FStar_Pervasives_Native.fst b) f1)
end))) us bs f)
in (

let uu___113_469 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.NonTrivial (f1); FStar_TypeChecker_Env.deferred = uu___113_469.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___113_469.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___113_469.FStar_TypeChecker_Env.implicits}))
end))


let close_forall : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____494 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____494) with
| true -> begin
f1
end
| uu____495 -> begin
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

let uu___114_513 = g
in (

let uu____514 = (

let uu____515 = (close_forall env binders f)
in FStar_TypeChecker_Common.NonTrivial (uu____515))
in {FStar_TypeChecker_Env.guard_f = uu____514; FStar_TypeChecker_Env.deferred = uu___114_513.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___114_513.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___114_513.FStar_TypeChecker_Env.implicits}))
end))

type uvi =
| TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)


let uu___is_TERM : uvi  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TERM (_0) -> begin
true
end
| uu____544 -> begin
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
| uu____574 -> begin
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


let new_uvar : Prims.string  ->  worklist  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.binding Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term * worklist) = (fun reason wl r gamma binders k should_check -> (

let ctx_uvar = (

let uu____849 = (FStar_Syntax_Unionfind.fresh ())
in {FStar_Syntax_Syntax.ctx_uvar_head = uu____849; FStar_Syntax_Syntax.ctx_uvar_gamma = gamma; FStar_Syntax_Syntax.ctx_uvar_binders = binders; FStar_Syntax_Syntax.ctx_uvar_typ = k; FStar_Syntax_Syntax.ctx_uvar_reason = reason; FStar_Syntax_Syntax.ctx_uvar_should_check = should_check; FStar_Syntax_Syntax.ctx_uvar_range = r})
in ((FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r should_check gamma binders);
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (ctx_uvar)) FStar_Pervasives_Native.None r)
in ((ctx_uvar), (t), ((

let uu___115_865 = wl
in {attempting = uu___115_865.attempting; wl_deferred = uu___115_865.wl_deferred; ctr = uu___115_865.ctr; defer_ok = uu___115_865.defer_ok; smt_ok = uu___115_865.smt_ok; tcenv = uu___115_865.tcenv; wl_implicits = (((reason), (t), (ctx_uvar), (r), (should_check)))::wl.wl_implicits}))));
)))

type solution =
| Success of (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits)
| Failed of (FStar_TypeChecker_Common.prob * Prims.string)


let uu___is_Success : solution  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
true
end
| uu____906 -> begin
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
| uu____936 -> begin
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
| uu____961 -> begin
false
end))


let uu___is_CONTRAVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CONTRAVARIANT -> begin
true
end
| uu____967 -> begin
false
end))


let uu___is_INVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| INVARIANT -> begin
true
end
| uu____973 -> begin
false
end))


type tprob =
FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem


type cprob =
FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem


type 'a problem_t =
'a FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun uu___85_988 -> (match (uu___85_988) with
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

let uu____994 = (

let uu____995 = (FStar_Syntax_Subst.compress t)
in uu____995.FStar_Syntax_Syntax.n)
in (match (uu____994) with
| FStar_Syntax_Syntax.Tm_uvar (u) -> begin
(print_ctx_uvar u)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u); FStar_Syntax_Syntax.pos = uu____1000; FStar_Syntax_Syntax.vars = uu____1001}, args) -> begin
(

let uu____1023 = (print_ctx_uvar u)
in (

let uu____1024 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "%s [%s]" uu____1023 uu____1024)))
end
| uu____1025 -> begin
(FStar_Syntax_Print.term_to_string t)
end)))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env uu___86_1035 -> (match (uu___86_1035) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____1039 = (

let uu____1042 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1043 = (

let uu____1046 = (term_to_string p.FStar_TypeChecker_Common.lhs)
in (

let uu____1047 = (

let uu____1050 = (

let uu____1053 = (term_to_string p.FStar_TypeChecker_Common.rhs)
in (uu____1053)::[])
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::uu____1050)
in (uu____1046)::uu____1047))
in (uu____1042)::uu____1043))
in (FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____1039))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____1057 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1058 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____1059 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1057 uu____1058 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1059))))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env uu___87_1069 -> (match (uu___87_1069) with
| UNIV (u, t) -> begin
(

let x = (

let uu____1073 = (FStar_Options.hide_uvar_nums ())
in (match (uu____1073) with
| true -> begin
"?"
end
| uu____1074 -> begin
(

let uu____1075 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____1075 FStar_Util.string_of_int))
end))
in (

let uu____1076 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x uu____1076)))
end
| TERM (u, t) -> begin
(

let x = (

let uu____1080 = (FStar_Options.hide_uvar_nums ())
in (match (uu____1080) with
| true -> begin
"?"
end
| uu____1081 -> begin
(

let uu____1082 = (FStar_Syntax_Unionfind.uvar_id u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_right uu____1082 FStar_Util.string_of_int))
end))
in (

let uu____1083 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x uu____1083)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (

let uu____1098 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right uu____1098 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (

let uu____1112 = (

let uu____1115 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right uu____1115 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right uu____1112 (FStar_String.concat ", "))))


let args_to_string : 'Auu____1128 . (FStar_Syntax_Syntax.term * 'Auu____1128) Prims.list  ->  Prims.string = (fun args -> (

let uu____1146 = (FStar_All.pipe_right args (FStar_List.map (fun uu____1164 -> (match (uu____1164) with
| (x, uu____1170) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____1146 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> (

let uu____1178 = (

let uu____1179 = (FStar_Options.eager_inference ())
in (not (uu____1179)))
in {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = uu____1178; smt_ok = true; tcenv = env; wl_implicits = []}))


let singleton : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun wl prob smt_ok -> (

let uu___116_1211 = wl
in {attempting = (prob)::[]; wl_deferred = uu___116_1211.wl_deferred; ctr = uu___116_1211.ctr; defer_ok = uu___116_1211.defer_ok; smt_ok = smt_ok; tcenv = uu___116_1211.tcenv; wl_implicits = uu___116_1211.wl_implicits}))


let wl_of_guard : 'Auu____1218 . FStar_TypeChecker_Env.env  ->  ('Auu____1218 * FStar_TypeChecker_Common.prob) Prims.list  ->  worklist = (fun env g -> (

let uu___117_1241 = (empty_worklist env)
in (

let uu____1242 = (FStar_List.map FStar_Pervasives_Native.snd g)
in {attempting = uu____1242; wl_deferred = uu___117_1241.wl_deferred; ctr = uu___117_1241.ctr; defer_ok = uu___117_1241.defer_ok; smt_ok = uu___117_1241.smt_ok; tcenv = uu___117_1241.tcenv; wl_implicits = uu___117_1241.wl_implicits})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu___118_1262 = wl
in {attempting = uu___118_1262.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = uu___118_1262.ctr; defer_ok = uu___118_1262.defer_ok; smt_ok = uu___118_1262.smt_ok; tcenv = uu___118_1262.tcenv; wl_implicits = uu___118_1262.wl_implicits}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let uu___119_1283 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = uu___119_1283.wl_deferred; ctr = uu___119_1283.ctr; defer_ok = uu___119_1283.defer_ok; smt_ok = uu___119_1283.smt_ok; tcenv = uu___119_1283.tcenv; wl_implicits = uu___119_1283.wl_implicits}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> ((

let uu____1300 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____1300) with
| true -> begin
(

let uu____1301 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1301))
end
| uu____1302 -> begin
()
end));
Failed (((prob), (reason)));
))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun uu___88_1307 -> (match (uu___88_1307) with
| FStar_TypeChecker_Common.EQ -> begin
FStar_TypeChecker_Common.EQ
end
| FStar_TypeChecker_Common.SUB -> begin
FStar_TypeChecker_Common.SUBINV
end
| FStar_TypeChecker_Common.SUBINV -> begin
FStar_TypeChecker_Common.SUB
end))


let invert : 'Auu____1312 . 'Auu____1312 FStar_TypeChecker_Common.problem  ->  'Auu____1312 FStar_TypeChecker_Common.problem = (fun p -> (

let uu___120_1324 = p
in {FStar_TypeChecker_Common.pid = uu___120_1324.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = uu___120_1324.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___120_1324.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___120_1324.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___120_1324.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___120_1324.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___120_1324.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___120_1324.FStar_TypeChecker_Common.rank}))


let maybe_invert : 'Auu____1331 . 'Auu____1331 FStar_TypeChecker_Common.problem  ->  'Auu____1331 FStar_TypeChecker_Common.problem = (fun p -> (match ((Prims.op_Equality p.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUBINV)) with
| true -> begin
(invert p)
end
| uu____1343 -> begin
p
end))


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___89_1348 -> (match (uu___89_1348) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_18 -> FStar_TypeChecker_Common.TProb (_0_18)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_19 -> FStar_TypeChecker_Common.CProb (_0_19)))
end))


let make_prob_eq : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___90_1363 -> (match (uu___90_1363) with
| FStar_TypeChecker_Common.TProb (p) -> begin
FStar_TypeChecker_Common.TProb ((

let uu___121_1369 = p
in {FStar_TypeChecker_Common.pid = uu___121_1369.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___121_1369.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___121_1369.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___121_1369.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___121_1369.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___121_1369.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___121_1369.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___121_1369.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___121_1369.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___121_1369.FStar_TypeChecker_Common.rank}))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
FStar_TypeChecker_Common.CProb ((

let uu___122_1377 = p
in {FStar_TypeChecker_Common.pid = uu___122_1377.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___122_1377.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___122_1377.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___122_1377.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___122_1377.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___122_1377.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___122_1377.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___122_1377.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___122_1377.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___122_1377.FStar_TypeChecker_Common.rank}))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel uu___91_1389 -> (match (uu___91_1389) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun uu___92_1394 -> (match (uu___92_1394) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun uu___93_1405 -> (match (uu___93_1405) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun uu___94_1418 -> (match (uu___94_1418) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun uu___95_1431 -> (match (uu___95_1431) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term = (fun uu___96_1442 -> (match (uu___96_1442) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_guard_uvar : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option * FStar_Syntax_Syntax.ctx_uvar) = (fun uu___97_1459 -> (match (uu___97_1459) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard_uvar
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard_uvar
end))


let def_scope_wf : 'Auu____1480 . Prims.string  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.bv * 'Auu____1480) Prims.list  ->  unit = (fun msg rng r -> (

let uu____1508 = (

let uu____1509 = (FStar_Options.defensive ())
in (not (uu____1509)))
in (match (uu____1508) with
| true -> begin
()
end
| uu____1510 -> begin
(

let rec aux = (fun prev next -> (match (next) with
| [] -> begin
()
end
| ((bv, uu____1543))::bs -> begin
((def_check_closed_in rng msg prev bv.FStar_Syntax_Syntax.sort);
(aux (FStar_List.append prev ((bv)::[])) bs);
)
end))
in (aux [] r))
end)))


let p_scope : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun prob -> (

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

let uu____1602 = (

let uu____1603 = (FStar_Options.defensive ())
in (not (uu____1603)))
in (match (uu____1602) with
| true -> begin
()
end
| uu____1604 -> begin
(

let uu____1605 = (

let uu____1608 = (p_scope prob)
in (FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst) uu____1608))
in (def_check_closed_in (p_loc prob) msg uu____1605 phi))
end)))


let def_check_prob : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  unit = (fun msg prob -> ((

let uu____1638 = (

let uu____1639 = (FStar_Options.defensive ())
in (not (uu____1639)))
in (match (uu____1638) with
| true -> begin
()
end
| uu____1640 -> begin
(

let uu____1641 = (p_scope prob)
in (def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1641))
end));
(def_check_scoped (Prims.strcat msg ".guard") prob (p_guard prob));
(match (prob) with
| FStar_TypeChecker_Common.TProb (p) -> begin
((def_check_scoped (Prims.strcat msg ".lhs") prob p.FStar_TypeChecker_Common.lhs);
(def_check_scoped (Prims.strcat msg ".rhs") prob p.FStar_TypeChecker_Common.rhs);
)
end
| uu____1653 -> begin
()
end);
))


let mk_eq2 : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * worklist) = (fun wl prob t1 t2 -> (

let uu____1683 = (FStar_Syntax_Util.type_u ())
in (match (uu____1683) with
| (t_type, u) -> begin
(

let uu____1694 = (

let uu____1701 = (p_scope prob)
in (new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos wl.tcenv.FStar_TypeChecker_Env.gamma uu____1701 t_type false))
in (match (uu____1694) with
| (uu____1706, tt, wl1) -> begin
(

let uu____1709 = (FStar_Syntax_Util.mk_eq2 u tt t1 t2)
in ((uu____1709), (wl1)))
end))
end)))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___98_1714 -> (match (uu___98_1714) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _0_20 -> FStar_TypeChecker_Common.TProb (_0_20)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _0_21 -> FStar_TypeChecker_Common.CProb (_0_21)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> (

let uu____1730 = (FStar_All.pipe_right (p_reason p) FStar_List.length)
in (Prims.op_Equality uu____1730 (Prims.parse_int "1"))))


let next_pid : unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____1740 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
)))


let mk_problem : 'Auu____1838 . worklist  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  'Auu____1838  ->  FStar_TypeChecker_Common.rel  ->  'Auu____1838  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  Prims.string  ->  ('Auu____1838 FStar_TypeChecker_Common.problem * worklist) = (fun wl scope orig lhs rel rhs elt reason -> (

let uu____1889 = (new_uvar (Prims.strcat "mk_problem: logical guard for " reason) wl FStar_Range.dummyRange wl.tcenv.FStar_TypeChecker_Env.gamma scope FStar_Syntax_Util.ktype0 false)
in (match (uu____1889) with
| (ctx_uvar, lg, wl1) -> begin
(

let uu____1905 = (

let uu____1908 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____1908; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = lg; FStar_TypeChecker_Common.logical_guard_uvar = ((FStar_Pervasives_Native.None), (ctx_uvar)); FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})
in ((uu____1905), (wl1)))
end)))


let mk_t_problem : worklist  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_TypeChecker_Common.prob * worklist) = (fun wl scope orig lhs rel rhs elt reason -> (

let uu____1961 = (mk_problem wl scope orig lhs rel rhs elt reason)
in (match (uu____1961) with
| (p, wl1) -> begin
((FStar_TypeChecker_Common.TProb (p)), (wl1))
end)))


let mk_c_problem : worklist  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_TypeChecker_Common.prob * worklist) = (fun wl scope orig lhs rel rhs elt reason -> (

let uu____2026 = (mk_problem wl scope orig lhs rel rhs elt reason)
in (match (uu____2026) with
| (p, wl1) -> begin
((FStar_TypeChecker_Common.CProb (p)), (wl1))
end)))


let new_problem : 'Auu____2061 . worklist  ->  FStar_TypeChecker_Env.env  ->  'Auu____2061  ->  FStar_TypeChecker_Common.rel  ->  'Auu____2061  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  Prims.string  ->  ('Auu____2061 FStar_TypeChecker_Common.problem * worklist) = (fun wl env lhs rel rhs subject loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (

let uu____2113 = (match (subject) with
| FStar_Pervasives_Native.None -> begin
((FStar_Syntax_Util.ktype0), (FStar_Pervasives_Native.None))
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____2135 = (

let uu____2138 = (

let uu____2145 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2145)::[])
in (

let uu____2158 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____2138 uu____2158)))
in (

let uu____2161 = (

let uu____2164 = (FStar_Syntax_Syntax.bv_to_name x)
in FStar_Pervasives_Native.Some (uu____2164))
in ((uu____2135), (uu____2161))))
end)
in (match (uu____2113) with
| (lg_ty, elt) -> begin
(

let uu____2185 = (new_uvar (Prims.strcat "new_problem: logical guard for " reason) (

let uu___123_2193 = wl
in {attempting = uu___123_2193.attempting; wl_deferred = uu___123_2193.wl_deferred; ctr = uu___123_2193.ctr; defer_ok = uu___123_2193.defer_ok; smt_ok = uu___123_2193.smt_ok; tcenv = env; wl_implicits = uu___123_2193.wl_implicits}) loc env.FStar_TypeChecker_Env.gamma scope lg_ty false)
in (match (uu____2185) with
| (ctx_uvar, lg, wl1) -> begin
(

let lg1 = (match (elt) with
| FStar_Pervasives_Native.None -> begin
lg
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____2205 = (

let uu____2210 = (

let uu____2211 = (FStar_Syntax_Syntax.as_arg x)
in (uu____2211)::[])
in (FStar_Syntax_Syntax.mk_Tm_app lg uu____2210))
in (uu____2205 FStar_Pervasives_Native.None loc))
end)
in (

let uu____2232 = (

let uu____2235 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____2235; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = lg1; FStar_TypeChecker_Common.logical_guard_uvar = ((subject), (ctx_uvar)); FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})
in ((uu____2232), (wl1))))
end))
end))))


let problem_using_guard : 'Auu____2254 . FStar_TypeChecker_Common.prob  ->  'Auu____2254  ->  FStar_TypeChecker_Common.rel  ->  'Auu____2254  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  Prims.string  ->  'Auu____2254 FStar_TypeChecker_Common.problem = (fun orig lhs rel rhs elt reason -> (

let uu____2291 = (next_pid ())
in (

let uu____2292 = (p_scope orig)
in {FStar_TypeChecker_Common.pid = uu____2291; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.logical_guard_uvar = (p_guard_uvar orig); FStar_TypeChecker_Common.scope = uu____2292; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})))


let guard_on_element : 'Auu____2303 . worklist  ->  'Auu____2303 FStar_TypeChecker_Common.problem  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ = (fun wl problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| FStar_Pervasives_Native.None -> begin
(

let u = (wl.tcenv.FStar_TypeChecker_Env.universe_of wl.tcenv x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Util.mk_forall u x phi))
end
| FStar_Pervasives_Native.Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (

let uu____2347 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____2347) with
| true -> begin
(

let uu____2348 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (

let uu____2349 = (prob_to_string env d)
in (

let uu____2350 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" uu____2348 uu____2349 uu____2350 s))))
end
| uu____2353 -> begin
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
| uu____2356 -> begin
(failwith "impossible")
end)
in (

let uu____2357 = (match (d1) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____2369 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (

let uu____2370 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((uu____2369), (uu____2370))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____2374 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (

let uu____2375 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((uu____2374), (uu____2375))))
end)
in (match (uu____2357) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___99_2393 -> (match (uu___99_2393) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Syntax_Unionfind.univ_union u u')
end
| uu____2405 -> begin
(FStar_Syntax_Unionfind.univ_change u t)
end)
end
| TERM (u, t) -> begin
((def_check_closed t.FStar_Syntax_Syntax.pos "commit" t);
(FStar_Syntax_Util.set_uvar u.FStar_Syntax_Syntax.ctx_uvar_head t);
)
end)))))


let find_term_uvar : FStar_Syntax_Syntax.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun uv s -> (FStar_Util.find_map s (fun uu___100_2427 -> (match (uu___100_2427) with
| UNIV (uu____2430) -> begin
FStar_Pervasives_Native.None
end
| TERM (u, t) -> begin
(

let uu____2437 = (FStar_Syntax_Unionfind.equiv uv u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____2437) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____2440 -> begin
FStar_Pervasives_Native.None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe_uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun u s -> (FStar_Util.find_map s (fun uu___101_2461 -> (match (uu___101_2461) with
| UNIV (u', t) -> begin
(

let uu____2466 = (FStar_Syntax_Unionfind.univ_equiv u u')
in (match (uu____2466) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____2469 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____2470 -> begin
FStar_Pervasives_Native.None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____2481 = (

let uu____2482 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env uu____2482))
in (FStar_Syntax_Subst.compress uu____2481)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____2493 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress uu____2493)))


let norm_arg : 'Auu____2500 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * 'Auu____2500)  ->  (FStar_Syntax_Syntax.term * 'Auu____2500) = (fun env t -> (

let uu____2523 = (sn env (FStar_Pervasives_Native.fst t))
in ((uu____2523), ((FStar_Pervasives_Native.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____2564 -> (match (uu____2564) with
| (x, imp) -> begin
(

let uu____2575 = (

let uu___124_2576 = x
in (

let uu____2577 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___124_2576.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___124_2576.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2577}))
in ((uu____2575), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____2598 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____2598))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____2602 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____2602))
end
| uu____2605 -> begin
u2
end)))
in (

let uu____2606 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2606))))


let base_and_refinement_maybe_delta : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option) = (fun should_delta env t1 -> (

let norm_refinement = (fun env1 t -> (

let steps = (match (should_delta) with
| true -> begin
(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]
end
| uu____2648 -> begin
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
| uu____2727 -> begin
(

let uu____2728 = (norm_refinement env t12)
in (match (uu____2728) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x1, phi1); FStar_Syntax_Syntax.pos = uu____2745; FStar_Syntax_Syntax.vars = uu____2746} -> begin
((x1.FStar_Syntax_Syntax.sort), (FStar_Pervasives_Native.Some (((x1), (phi1)))))
end
| tt -> begin
(

let uu____2772 = (

let uu____2773 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____2774 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" uu____2773 uu____2774)))
in (failwith uu____2772))
end))
end)
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____2790 = (FStar_Syntax_Util.unfold_lazy i)
in (aux norm1 uu____2790))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____2791) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____2826 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____2828 = (

let uu____2829 = (FStar_Syntax_Subst.compress t1')
in uu____2829.FStar_Syntax_Syntax.n)
in (match (uu____2828) with
| FStar_Syntax_Syntax.Tm_refine (uu____2846) -> begin
(aux true t1')
end
| uu____2853 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2868) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____2897 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____2899 = (

let uu____2900 = (FStar_Syntax_Subst.compress t1')
in uu____2900.FStar_Syntax_Syntax.n)
in (match (uu____2899) with
| FStar_Syntax_Syntax.Tm_refine (uu____2917) -> begin
(aux true t1')
end
| uu____2924 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_app (uu____2939) -> begin
(match (norm1) with
| true -> begin
((t12), (FStar_Pervasives_Native.None))
end
| uu____2982 -> begin
(

let t1' = (norm_refinement env t12)
in (

let uu____2984 = (

let uu____2985 = (FStar_Syntax_Subst.compress t1')
in uu____2985.FStar_Syntax_Syntax.n)
in (match (uu____2984) with
| FStar_Syntax_Syntax.Tm_refine (uu____3002) -> begin
(aux true t1')
end
| uu____3009 -> begin
((t12), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_type (uu____3024) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_constant (uu____3039) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_name (uu____3054) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3069) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3084) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_abs (uu____3111) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_quoted (uu____3142) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3163) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_let (uu____3178) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_match (uu____3205) -> begin
((t12), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_meta (uu____3242) -> begin
(

let uu____3249 = (

let uu____3250 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3251 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3250 uu____3251)))
in (failwith uu____3249))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3266) -> begin
(

let uu____3293 = (

let uu____3294 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3295 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3294 uu____3295)))
in (failwith uu____3293))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____3310) -> begin
(

let uu____3335 = (

let uu____3336 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3337 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3336 uu____3337)))
in (failwith uu____3335))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____3352 = (

let uu____3353 = (FStar_Syntax_Print.term_to_string t12)
in (

let uu____3354 = (FStar_Syntax_Print.tag_of_term t12)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____3353 uu____3354)))
in (failwith uu____3352))
end)))
in (

let uu____3369 = (whnf env t1)
in (aux false uu____3369)))))


let base_and_refinement : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option) = (fun env t -> (base_and_refinement_maybe_delta false env t))


let normalize_refinement : 'Auu____3400 . FStar_TypeChecker_Normalize.steps  ->  FStar_TypeChecker_Env.env  ->  'Auu____3400  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____3431 = (base_and_refinement env t)
in (FStar_All.pipe_right uu____3431 FStar_Pervasives_Native.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (

let uu____3467 = (FStar_Syntax_Syntax.null_bv t)
in ((uu____3467), (FStar_Syntax_Util.t_true))))


let as_refinement : 'Auu____3478 . Prims.bool  ->  FStar_TypeChecker_Env.env  ->  'Auu____3478  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun delta1 env wl t -> (

let uu____3503 = (base_and_refinement_maybe_delta delta1 env t)
in (match (uu____3503) with
| (t_base, refinement) -> begin
(match (refinement) with
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end
| FStar_Pervasives_Native.Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement : (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun uu____3586 -> (match (uu____3586) with
| (t_base, refopt) -> begin
(

let uu____3619 = (match (refopt) with
| FStar_Pervasives_Native.Some (y, phi) -> begin
((y), (phi))
end
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end)
in (match (uu____3619) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl prob -> (prob_to_string wl.tcenv prob))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (

let uu____3677 = (

let uu____3680 = (

let uu____3683 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____3706 -> (match (uu____3706) with
| (uu____3713, uu____3714, x) -> begin
x
end))))
in (FStar_List.append wl.attempting uu____3683))
in (FStar_List.map (wl_prob_to_string wl) uu____3680))
in (FStar_All.pipe_right uu____3677 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____3733 = (

let uu____3746 = (

let uu____3747 = (FStar_Syntax_Subst.compress k)
in uu____3747.FStar_Syntax_Syntax.n)
in (match (uu____3746) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((Prims.op_Equality (FStar_List.length bs) (FStar_List.length ys))) with
| true -> begin
(

let uu____3800 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (uu____3800)))
end
| uu____3813 -> begin
(

let uu____3814 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____3814) with
| (ys', t1, uu____3837) -> begin
(

let uu____3842 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t1))), (uu____3842)))
end))
end)
end
| uu____3883 -> begin
(

let uu____3884 = (

let uu____3895 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____3895)))
in ((((ys), (t))), (uu____3884)))
end))
in (match (uu____3733) with
| ((ys1, t1), (xs, c)) -> begin
(match ((Prims.op_disEquality (FStar_List.length xs) (FStar_List.length ys1))) with
| true -> begin
(FStar_Syntax_Util.abs ys1 t1 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None []))))
end
| uu____3942 -> begin
(

let c1 = (

let uu____3944 = (FStar_Syntax_Util.rename_binders xs ys1)
in (FStar_Syntax_Subst.subst_comp uu____3944 c))
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

let uu____3983 = (p_guard_uvar prob)
in (match (uu____3983) with
| (xopt, uv) -> begin
((

let uu____3997 = (FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____3997) with
| FStar_Pervasives_Native.None -> begin
((

let uu____4001 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____4001) with
| true -> begin
(

let uu____4002 = (FStar_Util.string_of_int (p_pid prob))
in (

let uu____4003 = (print_ctx_uvar uv)
in (

let uu____4004 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" uu____4002 uu____4003 uu____4004))))
end
| uu____4005 -> begin
()
end));
(

let phi1 = (match (xopt) with
| FStar_Pervasives_Native.None -> begin
phi
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____4008 = (

let uu____4009 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4009)::[])
in (FStar_Syntax_Util.abs uu____4008 phi (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0)))))
end)
in ((def_check_closed (p_loc prob) "solve_prob\'" phi1);
(FStar_Syntax_Util.set_uvar uv.FStar_Syntax_Syntax.ctx_uvar_head phi1);
));
)
end
| FStar_Pervasives_Native.Some (uu____4023) -> begin
(match ((not (resolve_ok))) with
| true -> begin
(failwith "Impossible: this instance has already been assigned a solution")
end
| uu____4024 -> begin
()
end)
end));
(commit uvis);
(

let uu___125_4026 = wl
in {attempting = uu___125_4026.attempting; wl_deferred = uu___125_4026.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___125_4026.defer_ok; smt_ok = uu___125_4026.smt_ok; tcenv = uu___125_4026.tcenv; wl_implicits = uu___125_4026.wl_implicits});
)
end)));
))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____4047 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____4047) with
| true -> begin
(

let uu____4048 = (FStar_Util.string_of_int pid)
in (

let uu____4049 = (

let uu____4050 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right uu____4050 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with [%s]\n" uu____4048 uu____4049)))
end
| uu____4055 -> begin
()
end));
(commit sol);
(

let uu___126_4057 = wl
in {attempting = uu___126_4057.attempting; wl_deferred = uu___126_4057.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___126_4057.defer_ok; smt_ok = uu___126_4057.smt_ok; tcenv = uu___126_4057.tcenv; wl_implicits = uu___126_4057.wl_implicits});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> ((def_check_prob "solve_prob.prob" prob);
(FStar_Util.iter_opt logical_guard (def_check_scoped "solve_prob.guard" prob));
(

let conj_guard1 = (fun t g -> (match (((t), (g))) with
| (uu____4119, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (FStar_Pervasives_Native.None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
FStar_Pervasives_Native.Some (f)
end
| (FStar_Pervasives_Native.Some (t1), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(

let uu____4145 = (FStar_Syntax_Util.mk_conj t1 f)
in FStar_Pervasives_Native.Some (uu____4145))
end))
in ((

let uu____4151 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____4151) with
| true -> begin
(

let uu____4152 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (

let uu____4153 = (

let uu____4154 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right uu____4154 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____4152 uu____4153)))
end
| uu____4159 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
));
))


let occurs_check : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool * Prims.string FStar_Pervasives_Native.option) = (fun uk t -> (

let uvars1 = (

let uu____4183 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right uu____4183 FStar_Util.set_elements))
in (

let occurs_ok = (

let uu____4191 = (FStar_All.pipe_right uvars1 (FStar_Util.for_some (fun uv -> (FStar_Syntax_Unionfind.equiv uv.FStar_Syntax_Syntax.ctx_uvar_head uk.FStar_Syntax_Syntax.ctx_uvar_head))))
in (not (uu____4191)))
in (

let msg = (match (occurs_ok) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4201 -> begin
(

let uu____4202 = (

let uu____4203 = (FStar_Syntax_Print.uvar_to_string uk.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____4204 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" uu____4203 uu____4204)))
in FStar_Pervasives_Native.Some (uu____4202))
end)
in ((uvars1), (occurs_ok), (msg))))))


let rec maximal_prefix : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.binders)) = (fun bs bs' -> (match (((bs), (bs'))) with
| (((b, i))::bs_tail, ((b', i'))::bs'_tail) -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
(

let uu____4293 = (maximal_prefix bs_tail bs'_tail)
in (match (uu____4293) with
| (pfx, rest) -> begin
(((((b), (i)))::pfx), (rest))
end))
end
| uu____4328 -> begin
(([]), (((bs), (bs'))))
end)
end
| uu____4337 -> begin
(([]), (((bs), (bs'))))
end))


let extend_gamma : FStar_Syntax_Syntax.gamma  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binding Prims.list = (fun g bs -> (FStar_List.fold_left (fun g1 uu____4385 -> (match (uu____4385) with
| (x, uu____4395) -> begin
(FStar_Syntax_Syntax.Binding_var (x))::g1
end)) g bs))


let gamma_until : FStar_Syntax_Syntax.gamma  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binding Prims.list = (fun g bs -> (

let uu____4408 = (FStar_List.last bs)
in (match (uu____4408) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (x, uu____4426) -> begin
(

let uu____4431 = (FStar_Util.prefix_until (fun uu___102_4446 -> (match (uu___102_4446) with
| FStar_Syntax_Syntax.Binding_var (x') -> begin
(FStar_Syntax_Syntax.bv_eq x x')
end
| uu____4448 -> begin
false
end)) g)
in (match (uu____4431) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____4461, bx, rest) -> begin
(bx)::rest
end))
end)))


let restrict_ctx : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.ctx_uvar  ->  worklist  ->  worklist = (fun tgt src wl -> (

let uu____4497 = (maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders src.FStar_Syntax_Syntax.ctx_uvar_binders)
in (match (uu____4497) with
| (pfx, uu____4507) -> begin
(

let g = (gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx)
in (

let uu____4519 = (new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl src.FStar_Syntax_Syntax.ctx_uvar_range g pfx src.FStar_Syntax_Syntax.ctx_uvar_typ src.FStar_Syntax_Syntax.ctx_uvar_should_check)
in (match (uu____4519) with
| (uu____4526, src', wl1) -> begin
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

let uu____4606 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____4660 uu____4661 -> (match (((uu____4660), (uu____4661))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____4742 = (

let uu____4743 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation uu____4743))
in (match (uu____4742) with
| true -> begin
((isect), (isect_set))
end
| uu____4764 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____4768 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____4768) with
| true -> begin
(

let uu____4781 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (uu____4781)))
end
| uu____4796 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (uu____4606) with
| (isect, uu____4818) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq : 'Auu____4847 'Auu____4848 . (FStar_Syntax_Syntax.bv * 'Auu____4847) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____4848) Prims.list  ->  Prims.bool = (fun v1 v2 -> ((Prims.op_Equality (FStar_List.length v1) (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____4905 uu____4906 -> (match (((uu____4905), (uu____4906))) with
| ((a, uu____4924), (b, uu____4926)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let name_exists_in_binders : 'Auu____4941 . FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.bv * 'Auu____4941) Prims.list  ->  Prims.bool = (fun x bs -> (FStar_Util.for_some (fun uu____4971 -> (match (uu____4971) with
| (y, uu____4977) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end)) bs))


let pat_vars : 'Auu____4988 'Auu____4989 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____4988) Prims.list  ->  (FStar_Syntax_Syntax.term * 'Auu____4989) Prims.list  ->  FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option = (fun env ctx args -> (

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

let uu____5098 = ((name_exists_in_binders a seen) || (name_exists_in_binders a ctx))
in (match (uu____5098) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5105 -> begin
(

let uu____5106 = (

let uu____5109 = (FStar_Syntax_Syntax.mk_binder a)
in (uu____5109)::seen)
in (aux uu____5106 args2))
end))
end
| uu____5110 -> begin
FStar_Pervasives_Native.None
end))
end))
in (aux [] args)))


type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)


let flex_t_to_string : 'Auu____5123 . ('Auu____5123 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)  ->  Prims.string = (fun uu____5134 -> (match (uu____5134) with
| (uu____5141, c, args) -> begin
(

let uu____5144 = (print_ctx_uvar c)
in (

let uu____5145 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "%s [%s]" uu____5144 uu____5145)))
end))


let is_flex : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____5151 = (

let uu____5152 = (FStar_Syntax_Subst.compress t)
in uu____5152.FStar_Syntax_Syntax.n)
in (match (uu____5151) with
| FStar_Syntax_Syntax.Tm_uvar (uu____5155) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____5156); FStar_Syntax_Syntax.pos = uu____5157; FStar_Syntax_Syntax.vars = uu____5158}, uu____5159) -> begin
true
end
| uu____5180 -> begin
false
end)))


let destruct_flex_t : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv) -> begin
((t), (uv), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv); FStar_Syntax_Syntax.pos = uu____5198; FStar_Syntax_Syntax.vars = uu____5199}, args) -> begin
((t), (uv), (args))
end
| uu____5221 -> begin
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
| uu____5249 -> begin
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
| uu____5286 -> begin
false
end))


let uu___is_FullMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullMatch -> begin
true
end
| uu____5292 -> begin
false
end))


let string_of_option : 'Auu____5299 . ('Auu____5299  ->  Prims.string)  ->  'Auu____5299 FStar_Pervasives_Native.option  ->  Prims.string = (fun f uu___103_5314 -> (match (uu___103_5314) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____5320 = (f x)
in (Prims.strcat "Some " uu____5320))
end))


let string_of_match_result : match_result  ->  Prims.string = (fun uu___104_5325 -> (match (uu___104_5325) with
| MisMatch (d1, d2) -> begin
(

let uu____5336 = (

let uu____5337 = (string_of_option FStar_Syntax_Print.delta_depth_to_string d1)
in (

let uu____5338 = (

let uu____5339 = (

let uu____5340 = (string_of_option FStar_Syntax_Print.delta_depth_to_string d2)
in (Prims.strcat uu____5340 ")"))
in (Prims.strcat ") (" uu____5339))
in (Prims.strcat uu____5337 uu____5338)))
in (Prims.strcat "MisMatch (" uu____5336))
end
| HeadMatch -> begin
"HeadMatch"
end
| FullMatch -> begin
"FullMatch"
end))


let head_match : match_result  ->  match_result = (fun uu___105_5345 -> (match (uu___105_5345) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____5360 -> begin
HeadMatch
end))


let and_match : match_result  ->  (unit  ->  match_result)  ->  match_result = (fun m1 m2 -> (match (m1) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| HeadMatch -> begin
(

let uu____5390 = (m2 ())
in (match (uu____5390) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____5405 -> begin
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
| uu____5417 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
end
| FStar_Syntax_Syntax.Delta_defined_at_level (uu____5418) -> begin
(

let uu____5419 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5419) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Syntax.Delta_constant
end
| uu____5430 -> begin
fv.FStar_Syntax_Syntax.fv_delta
end))
end
| d -> begin
d
end))


let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____5453) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____5462) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____5490 = (FStar_Syntax_Util.unfold_lazy i)
in (delta_depth_of_term env uu____5490))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_bvar (uu____5491) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_name (uu____5492) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uvar (uu____5493) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_let (uu____5494) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_match (uu____5507) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____5531) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____5537, uu____5538) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____5580) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____5601; FStar_Syntax_Syntax.index = uu____5602; FStar_Syntax_Syntax.sort = t2}, uu____5604) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_constant (uu____5611) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_type (uu____5612) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____5613) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____5626) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_abs (uu____5633) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5651 = (fv_delta_depth env fv)
in FStar_Pervasives_Native.Some (uu____5651))
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
| uu____5671 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____5678 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____5678) with
| true -> begin
FullMatch
end
| uu____5679 -> begin
(

let uu____5680 = (

let uu____5689 = (

let uu____5692 = (fv_delta_depth env f)
in FStar_Pervasives_Native.Some (uu____5692))
in (

let uu____5693 = (

let uu____5696 = (fv_delta_depth env g)
in FStar_Pervasives_Native.Some (uu____5696))
in ((uu____5689), (uu____5693))))
in MisMatch (uu____5680))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____5702), FStar_Syntax_Syntax.Tm_uinst (g, uu____5704)) -> begin
(

let uu____5713 = (head_matches env f g)
in (FStar_All.pipe_right uu____5713 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____5716 = (FStar_Const.eq_const c d)
in (match (uu____5716) with
| true -> begin
FullMatch
end
| uu____5717 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (uv), FStar_Syntax_Syntax.Tm_uvar (uv')) -> begin
(

let uu____5724 = (FStar_Syntax_Unionfind.equiv uv.FStar_Syntax_Syntax.ctx_uvar_head uv'.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____5724) with
| true -> begin
FullMatch
end
| uu____5725 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____5731), FStar_Syntax_Syntax.Tm_refine (y, uu____5733)) -> begin
(

let uu____5742 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____5742 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____5744), uu____5745) -> begin
(

let uu____5750 = (head_matches env x.FStar_Syntax_Syntax.sort t21)
in (FStar_All.pipe_right uu____5750 head_match))
end
| (uu____5751, FStar_Syntax_Syntax.Tm_refine (x, uu____5753)) -> begin
(

let uu____5758 = (head_matches env t11 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____5758 head_match))
end
| (FStar_Syntax_Syntax.Tm_type (uu____5759), FStar_Syntax_Syntax.Tm_type (uu____5760)) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_arrow (uu____5761), FStar_Syntax_Syntax.Tm_arrow (uu____5762)) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____5788), FStar_Syntax_Syntax.Tm_app (head', uu____5790)) -> begin
(

let uu____5831 = (head_matches env head1 head')
in (FStar_All.pipe_right uu____5831 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____5833), uu____5834) -> begin
(

let uu____5855 = (head_matches env head1 t21)
in (FStar_All.pipe_right uu____5855 head_match))
end
| (uu____5856, FStar_Syntax_Syntax.Tm_app (head1, uu____5858)) -> begin
(

let uu____5879 = (head_matches env t11 head1)
in (FStar_All.pipe_right uu____5879 head_match))
end
| uu____5880 -> begin
(

let uu____5885 = (

let uu____5894 = (delta_depth_of_term env t11)
in (

let uu____5897 = (delta_depth_of_term env t21)
in ((uu____5894), (uu____5897))))
in MisMatch (uu____5885))
end))))


let head_matches_delta : 'Auu____5914 . FStar_TypeChecker_Env.env  ->  'Auu____5914  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (match_result * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) FStar_Pervasives_Native.option) = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let uu____5953 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____5953) with
| (head1, uu____5971) -> begin
(

let uu____5992 = (

let uu____5993 = (FStar_Syntax_Util.un_uinst head1)
in uu____5993.FStar_Syntax_Syntax.n)
in (match (uu____5992) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5999 = (

let uu____6000 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____6000 FStar_Option.isSome))
in (match (uu____5999) with
| true -> begin
(

let uu____6019 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right uu____6019 (fun _0_22 -> FStar_Pervasives_Native.Some (_0_22))))
end
| uu____6022 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____6023 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (

let success = (fun d r t11 t21 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (((t11), (t21)))
end
| uu____6071 -> begin
FStar_Pervasives_Native.None
end))))
in (

let fail1 = (fun r -> ((r), (FStar_Pervasives_Native.None)))
in (

let rec aux = (fun retry n_delta t11 t21 -> (

let r = (head_matches env t11 t21)
in (match (r) with
| MisMatch (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational), uu____6144) -> begin
(match ((not (retry))) with
| true -> begin
(fail1 r)
end
| uu____6161 -> begin
(

let uu____6162 = (

let uu____6171 = (maybe_inline t11)
in (

let uu____6174 = (maybe_inline t21)
in ((uu____6171), (uu____6174))))
in (match (uu____6162) with
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
| MisMatch (uu____6211, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational)) -> begin
(match ((not (retry))) with
| true -> begin
(fail1 r)
end
| uu____6228 -> begin
(

let uu____6229 = (

let uu____6238 = (maybe_inline t11)
in (

let uu____6241 = (maybe_inline t21)
in ((uu____6238), (uu____6241))))
in (match (uu____6229) with
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

let uu____6284 = (FStar_TypeChecker_Common.decr_delta_depth d1)
in (match (uu____6284) with
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

let uu____6307 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env wl t11)
in ((t1'), (t21)))
end
| uu____6317 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env wl t21)
in ((t11), (t2')))
end)
in (match (uu____6307) with
| (t12, t22) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
end)))
end
| MisMatch (uu____6331) -> begin
(fail1 r)
end
| uu____6340 -> begin
(success n_delta r t11 t21)
end)))
in (

let r = (aux true (Prims.parse_int "0") t1 t2)
in ((

let uu____6353 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelDelta")))
in (match (uu____6353) with
| true -> begin
(

let uu____6354 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6355 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____6356 = (string_of_match_result (FStar_Pervasives_Native.fst r))
in (FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6354 uu____6355 uu____6356))))
end
| uu____6363 -> begin
()
end));
r;
)))))))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____6374 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____6374 FStar_Pervasives_Native.fst)))


let rigid_rigid : Prims.int = (Prims.parse_int "0")


let flex_rigid_eq : Prims.int = (Prims.parse_int "1")


let flex_rigid : Prims.int = (Prims.parse_int "4")


let rigid_flex : Prims.int = (Prims.parse_int "5")


let flex_flex : Prims.int = (Prims.parse_int "7")


let compress_tprob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem  ->  FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem = (fun tcenv p -> (

let uu___127_6399 = p
in (

let uu____6402 = (whnf tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____6403 = (whnf tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___127_6399.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____6402; FStar_TypeChecker_Common.relation = uu___127_6399.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____6403; FStar_TypeChecker_Common.element = uu___127_6399.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___127_6399.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___127_6399.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___127_6399.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___127_6399.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___127_6399.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___127_6399.FStar_TypeChecker_Common.rank}))))


let compress_prob : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun tcenv p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p1) -> begin
(

let uu____6417 = (compress_tprob tcenv p1)
in (FStar_All.pipe_right uu____6417 (fun _0_23 -> FStar_TypeChecker_Common.TProb (_0_23))))
end
| FStar_TypeChecker_Common.CProb (uu____6422) -> begin
p
end))


let rank : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun tcenv pr -> (

let prob = (

let uu____6444 = (compress_prob tcenv pr)
in (FStar_All.pipe_right uu____6444 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____6452 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____6452) with
| (lh, uu____6472) -> begin
(

let uu____6493 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____6493) with
| (rh, uu____6513) -> begin
(

let rank = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____6535), FStar_Syntax_Syntax.Tm_uvar (uu____6536)) -> begin
flex_flex
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____6537), uu____6538) when ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
flex_rigid_eq
end
| (uu____6539, FStar_Syntax_Syntax.Tm_uvar (uu____6540)) when ((Prims.op_Equality tp.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
flex_rigid_eq
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____6541), uu____6542) -> begin
flex_rigid
end
| (uu____6543, FStar_Syntax_Syntax.Tm_uvar (uu____6544)) -> begin
rigid_flex
end
| (uu____6545, uu____6546) -> begin
rigid_rigid
end)
in (

let uu____6547 = (FStar_All.pipe_right (

let uu___128_6551 = tp
in {FStar_TypeChecker_Common.pid = uu___128_6551.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___128_6551.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___128_6551.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___128_6551.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___128_6551.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___128_6551.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___128_6551.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___128_6551.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___128_6551.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___128_6551.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rank)}) (fun _0_24 -> FStar_TypeChecker_Common.TProb (_0_24)))
in ((rank), (uu____6547))))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____6557 = (FStar_All.pipe_right (

let uu___129_6561 = cp
in {FStar_TypeChecker_Common.pid = uu___129_6561.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___129_6561.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___129_6561.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___129_6561.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___129_6561.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___129_6561.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___129_6561.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___129_6561.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___129_6561.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___129_6561.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rigid_rigid)}) (fun _0_25 -> FStar_TypeChecker_Common.CProb (_0_25)))
in ((rigid_rigid), (uu____6557)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun uu____6620 probs -> (match (uu____6620) with
| (min_rank, min1, out) -> begin
(match (probs) with
| [] -> begin
((min1), (out), (min_rank))
end
| (hd1)::tl1 -> begin
(

let uu____6673 = (rank wl.tcenv hd1)
in (match (uu____6673) with
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
| uu____6719 -> begin
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
| uu____6749 -> begin
(aux ((min_rank), (min1), ((hd2)::out)) tl1)
end)
end)
end))
end)
end))
in (aux (((flex_flex + (Prims.parse_int "1"))), (FStar_Pervasives_Native.None), ([])) wl.attempting)))


let flex_prob_closing : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun tcenv bs p -> (

let flex_will_be_closed = (fun t -> (

let uu____6783 = (destruct_flex_t t)
in (match (uu____6783) with
| (uu____6784, u, uu____6786) -> begin
(FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders (FStar_Util.for_some (fun uu____6800 -> (match (uu____6800) with
| (y, uu____6806) -> begin
(FStar_All.pipe_right bs (FStar_Util.for_some (fun uu____6820 -> (match (uu____6820) with
| (x, uu____6826) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end))))
end))))
end)))
in (

let uu____6827 = (rank tcenv p)
in (match (uu____6827) with
| (r, p1) -> begin
(match ((((Prims.op_disEquality r rigid_flex) && (Prims.op_disEquality r flex_rigid)) && (Prims.op_disEquality r flex_flex))) with
| true -> begin
false
end
| uu____6834 -> begin
(match (p1) with
| FStar_TypeChecker_Common.CProb (uu____6835) -> begin
false
end
| FStar_TypeChecker_Common.TProb (p2) -> begin
(match ((Prims.op_Equality r flex_flex)) with
| true -> begin
((flex_will_be_closed p2.FStar_TypeChecker_Common.lhs) || (flex_will_be_closed p2.FStar_TypeChecker_Common.rhs))
end
| uu____6841 -> begin
(match ((Prims.op_Equality r flex_rigid)) with
| true -> begin
(flex_will_be_closed p2.FStar_TypeChecker_Common.lhs)
end
| uu____6842 -> begin
(flex_will_be_closed p2.FStar_TypeChecker_Common.rhs)
end)
end)
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
| uu____6864 -> begin
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
| uu____6878 -> begin
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
| uu____6892 -> begin
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

let uu____6944 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____6944) with
| (k, uu____6950) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Syntax_Unionfind.univ_equiv v1 v2)
end
| uu____6960 -> begin
false
end)
end)))))
end
| uu____6961 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (

let rec filter_out_common_univs = (fun u12 u22 -> (

let common_elts = (FStar_All.pipe_right u12 (FStar_List.fold_left (fun uvs uv1 -> (

let uu____7013 = (FStar_All.pipe_right u22 (FStar_List.existsML (fun uv2 -> (

let uu____7019 = (FStar_Syntax_Util.compare_univs uv1 uv2)
in (Prims.op_Equality uu____7019 (Prims.parse_int "0"))))))
in (match (uu____7013) with
| true -> begin
(uv1)::uvs
end
| uu____7022 -> begin
uvs
end))) []))
in (

let filter1 = (FStar_List.filter (fun u -> (

let uu____7035 = (FStar_All.pipe_right common_elts (FStar_List.existsML (fun u' -> (

let uu____7041 = (FStar_Syntax_Util.compare_univs u u')
in (Prims.op_Equality uu____7041 (Prims.parse_int "0"))))))
in (not (uu____7035)))))
in (

let uu____7042 = (filter1 u12)
in (

let uu____7045 = (filter1 u22)
in ((uu____7042), (uu____7045)))))))
in (

let try_umax_components = (fun u12 u22 msg -> (match (((u12), (u22))) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(

let uu____7074 = (filter_out_common_univs us1 us2)
in (match (uu____7074) with
| (us11, us21) -> begin
(match ((Prims.op_Equality (FStar_List.length us11) (FStar_List.length us21))) with
| true -> begin
(

let rec aux = (fun wl1 us12 us22 -> (match (((us12), (us22))) with
| ((u13)::us13, (u23)::us23) -> begin
(

let uu____7133 = (really_solve_universe_eq pid_orig wl1 u13 u23)
in (match (uu____7133) with
| USolved (wl2) -> begin
(aux wl2 us13 us23)
end
| failed -> begin
failed
end))
end
| uu____7136 -> begin
USolved (wl1)
end))
in (aux wl us11 us21))
end
| uu____7145 -> begin
(

let uu____7146 = (

let uu____7147 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____7148 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" uu____7147 uu____7148)))
in UFailed (uu____7146))
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

let uu____7172 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____7172) with
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

let uu____7198 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____7198) with
| USolved (wl2) -> begin
(aux wl2 us2)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____7201 -> begin
(

let uu____7206 = (

let uu____7207 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____7208 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" uu____7207 uu____7208 msg)))
in UFailed (uu____7206))
end))
in (match (((u11), (u21))) with
| (FStar_Syntax_Syntax.U_bvar (uu____7209), uu____7210) -> begin
(

let uu____7211 = (

let uu____7212 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____7213 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____7212 uu____7213)))
in (failwith uu____7211))
end
| (FStar_Syntax_Syntax.U_unknown, uu____7214) -> begin
(

let uu____7215 = (

let uu____7216 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____7217 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____7216 uu____7217)))
in (failwith uu____7215))
end
| (uu____7218, FStar_Syntax_Syntax.U_bvar (uu____7219)) -> begin
(

let uu____7220 = (

let uu____7221 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____7222 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____7221 uu____7222)))
in (failwith uu____7220))
end
| (uu____7223, FStar_Syntax_Syntax.U_unknown) -> begin
(

let uu____7224 = (

let uu____7225 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____7226 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____7225 uu____7226)))
in (failwith uu____7224))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____7229 -> begin
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

let uu____7250 = (FStar_Syntax_Unionfind.univ_equiv v1 v2)
in (match (uu____7250) with
| true -> begin
USolved (wl)
end
| uu____7251 -> begin
(

let wl1 = (extend_solution pid_orig ((UNIV (((v1), (u21))))::[]) wl)
in USolved (wl1))
end))
end
| (FStar_Syntax_Syntax.U_unif (v1), u) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____7264 = (occurs_univ v1 u3)
in (match (uu____7264) with
| true -> begin
(

let uu____7265 = (

let uu____7266 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____7267 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____7266 uu____7267)))
in (try_umax_components u11 u21 uu____7265))
end
| uu____7268 -> begin
(

let uu____7269 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____7269))
end)))
end
| (u, FStar_Syntax_Syntax.U_unif (v1)) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____7281 = (occurs_univ v1 u3)
in (match (uu____7281) with
| true -> begin
(

let uu____7282 = (

let uu____7283 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____7284 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____7283 uu____7284)))
in (try_umax_components u11 u21 uu____7282))
end
| uu____7285 -> begin
(

let uu____7286 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____7286))
end)))
end
| (FStar_Syntax_Syntax.U_max (uu____7287), uu____7288) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____7291 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____7294 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____7294) with
| true -> begin
USolved (wl)
end
| uu____7295 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (uu____7296, FStar_Syntax_Syntax.U_max (uu____7297)) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____7300 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____7303 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____7303) with
| true -> begin
USolved (wl)
end
| uu____7304 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (FStar_Syntax_Syntax.U_succ (uu____7305), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_succ (uu____7306), FStar_Syntax_Syntax.U_name (uu____7307)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ (uu____7308)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name (uu____7309)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____7310), FStar_Syntax_Syntax.U_succ (uu____7311)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____7312), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end)))))))


let solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (match (wl.tcenv.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
USolved (wl)
end
| uu____7333 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders : 'a 'b . ('a Prims.list * ('a Prims.list  ->  'b))  ->  ('a Prims.list * ('a Prims.list  ->  'b))  ->  (('a Prims.list * 'b) * ('a Prims.list * 'b)) = (fun bc1 bc2 -> (

let uu____7412 = bc1
in (match (uu____7412) with
| (bs1, mk_cod1) -> begin
(

let uu____7456 = bc2
in (match (uu____7456) with
| (bs2, mk_cod2) -> begin
(

let rec aux = (fun bs11 bs21 -> (match (((bs11), (bs21))) with
| ((x)::xs, (y)::ys) -> begin
(

let uu____7567 = (aux xs ys)
in (match (uu____7567) with
| ((xs1, xr), (ys1, yr)) -> begin
(((((x)::xs1), (xr))), ((((y)::ys1), (yr))))
end))
end
| (xs, ys) -> begin
(

let uu____7650 = (

let uu____7657 = (mk_cod1 xs)
in (([]), (uu____7657)))
in (

let uu____7660 = (

let uu____7667 = (mk_cod2 ys)
in (([]), (uu____7667)))
in ((uu____7650), (uu____7660))))
end))
in (aux bs1 bs2))
end))
end)))


let quasi_pattern : FStar_TypeChecker_Env.env  ->  flex_t  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ) FStar_Pervasives_Native.option = (fun env f -> (

let uu____7704 = f
in (match (uu____7704) with
| (uu____7711, {FStar_Syntax_Syntax.ctx_uvar_head = uu____7712; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____7713; FStar_Syntax_Syntax.ctx_uvar_binders = ctx; FStar_Syntax_Syntax.ctx_uvar_typ = t_hd; FStar_Syntax_Syntax.ctx_uvar_reason = uu____7716; FStar_Syntax_Syntax.ctx_uvar_should_check = uu____7717; FStar_Syntax_Syntax.ctx_uvar_range = uu____7718}, args) -> begin
(

let name_exists_in = (fun x bs -> (FStar_Util.for_some (fun uu____7770 -> (match (uu____7770) with
| (y, uu____7776) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end)) bs))
in (

let rec aux = (fun pat_binders formals t_res args1 -> (match (((formals), (args1))) with
| ([], []) -> begin
FStar_Pervasives_Native.Some ((((FStar_List.rev pat_binders)), (t_res)))
end
| (uu____7882, []) -> begin
FStar_Pervasives_Native.Some ((((FStar_List.rev pat_binders)), (t_res)))
end
| (((formal, uu____7914))::formals1, ((a, uu____7917))::args2) -> begin
(

let uu____7951 = (

let uu____7952 = (FStar_Syntax_Subst.compress a)
in uu____7952.FStar_Syntax_Syntax.n)
in (match (uu____7951) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____7964 = ((name_exists_in x ctx) || (name_exists_in x pat_binders))
in (match (uu____7964) with
| true -> begin
(

let uu____7973 = (

let uu____7976 = (FStar_Syntax_Syntax.mk_binder formal)
in (uu____7976)::pat_binders)
in (aux uu____7973 formals1 t_res args2))
end
| uu____7977 -> begin
(

let x1 = (

let uu___130_7979 = x
in {FStar_Syntax_Syntax.ppname = uu___130_7979.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___130_7979.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = formal.FStar_Syntax_Syntax.sort})
in (

let subst1 = (

let uu____7983 = (

let uu____7984 = (

let uu____7991 = (FStar_Syntax_Syntax.bv_to_name x1)
in ((formal), (uu____7991)))
in FStar_Syntax_Syntax.NT (uu____7984))
in (uu____7983)::[])
in (

let formals2 = (FStar_Syntax_Subst.subst_binders subst1 formals1)
in (

let t_res1 = (FStar_Syntax_Subst.subst subst1 t_res)
in (

let uu____7998 = (

let uu____8001 = (FStar_Syntax_Syntax.mk_binder (

let uu___131_8004 = x1
in {FStar_Syntax_Syntax.ppname = uu___131_8004.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___131_8004.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = formal.FStar_Syntax_Syntax.sort}))
in (uu____8001)::pat_binders)
in (aux uu____7998 formals2 t_res1 args2))))))
end))
end
| uu____8005 -> begin
(

let uu____8006 = (

let uu____8009 = (FStar_Syntax_Syntax.mk_binder formal)
in (uu____8009)::pat_binders)
in (aux uu____8006 formals1 t_res args2))
end))
end
| ([], args2) -> begin
(

let uu____8033 = (

let uu____8046 = (FStar_TypeChecker_Normalize.unfold_whnf env t_res)
in (FStar_Syntax_Util.arrow_formals uu____8046))
in (match (uu____8033) with
| (more_formals, t_res1) -> begin
(match (more_formals) with
| [] -> begin
FStar_Pervasives_Native.None
end
| uu____8091 -> begin
(aux pat_binders more_formals t_res1 args2)
end)
end))
end))
in (

let uu____8098 = (FStar_Syntax_Util.arrow_formals t_hd)
in (match (uu____8098) with
| (formals, t_res) -> begin
(aux [] formals t_res args)
end))))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____8322 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____8322) with
| true -> begin
(

let uu____8323 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" uu____8323))
end
| uu____8324 -> begin
()
end));
(

let uu____8325 = (next_prob probs)
in (match (uu____8325) with
| (FStar_Pervasives_Native.Some (hd1), tl1, rank1) -> begin
(

let probs1 = (

let uu___132_8346 = probs
in {attempting = tl1; wl_deferred = uu___132_8346.wl_deferred; ctr = uu___132_8346.ctr; defer_ok = uu___132_8346.defer_ok; smt_ok = uu___132_8346.smt_ok; tcenv = uu___132_8346.tcenv; wl_implicits = uu___132_8346.wl_implicits})
in (match (hd1) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs1)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (((not (probs1.defer_ok)) && (Prims.op_Equality rank1 flex_rigid))) with
| true -> begin
(

let tp1 = (

let uu___133_8356 = tp
in {FStar_TypeChecker_Common.pid = uu___133_8356.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___133_8356.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___133_8356.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___133_8356.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___133_8356.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___133_8356.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___133_8356.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___133_8356.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___133_8356.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___133_8356.FStar_TypeChecker_Common.rank})
in (solve_t' env tp1 probs1))
end
| uu____8359 -> begin
(match (((not (probs1.defer_ok)) && (Prims.op_Equality rigid_flex rank1))) with
| true -> begin
(

let tp1 = (

let uu___134_8363 = tp
in {FStar_TypeChecker_Common.pid = uu___134_8363.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___134_8363.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___134_8363.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___134_8363.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___134_8363.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___134_8363.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___134_8363.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___134_8363.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___134_8363.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___134_8363.FStar_TypeChecker_Common.rank})
in (solve_t' env tp1 probs1))
end
| uu____8366 -> begin
(solve_t' env (maybe_invert tp) probs1)
end)
end)
end))
end
| (FStar_Pervasives_Native.None, uu____8367, uu____8368) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ((([]), (probs.wl_implicits)))
end
| uu____8385 -> begin
(

let uu____8394 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____8453 -> (match (uu____8453) with
| (c, uu____8461, uu____8462) -> begin
(c < probs.ctr)
end))))
in (match (uu____8394) with
| (attempt1, rest) -> begin
(match (attempt1) with
| [] -> begin
(

let uu____8503 = (

let uu____8508 = (FStar_List.map (fun uu____8523 -> (match (uu____8523) with
| (uu____8534, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in ((uu____8508), (probs.wl_implicits)))
in Success (uu____8503))
end
| uu____8537 -> begin
(

let uu____8546 = (

let uu___135_8547 = probs
in (

let uu____8548 = (FStar_All.pipe_right attempt1 (FStar_List.map (fun uu____8567 -> (match (uu____8567) with
| (uu____8574, uu____8575, y) -> begin
y
end))))
in {attempting = uu____8548; wl_deferred = rest; ctr = uu___135_8547.ctr; defer_ok = uu___135_8547.defer_ok; smt_ok = uu___135_8547.smt_ok; tcenv = uu___135_8547.tcenv; wl_implicits = uu___135_8547.wl_implicits}))
in (solve env uu____8546))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____8582 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____8582) with
| USolved (wl1) -> begin
(

let uu____8584 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____8584))
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

let uu____8636 = (solve_universe_eq (p_pid orig) wl1 u1 u2)
in (match (uu____8636) with
| USolved (wl2) -> begin
(aux wl2 us11 us21)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____8639 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t11 = (whnf env t1)
in (

let t21 = (whnf env t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.pos = uu____8651; FStar_Syntax_Syntax.vars = uu____8652}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.pos = uu____8655; FStar_Syntax_Syntax.vars = uu____8656}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____8668), uu____8669) -> begin
(failwith "Impossible: expect head symbols to match")
end
| (uu____8676, FStar_Syntax_Syntax.Tm_uinst (uu____8677)) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____8684 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____8694 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8694) with
| true -> begin
(

let uu____8695 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" uu____8695 msg))
end
| uu____8696 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____8697 -> begin
(giveup env msg orig)
end))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (worklist  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  (FStar_TypeChecker_Common.prob * worklist))  ->  solution = (fun env bs1 bs2 orig wl rhs -> ((

let uu____8719 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8719) with
| true -> begin
(

let uu____8720 = (FStar_Syntax_Print.binders_to_string ", " bs1)
in (

let uu____8721 = (FStar_Syntax_Print.binders_to_string ", " bs2)
in (FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n" uu____8720 (rel_to_string (p_rel orig)) uu____8721)))
end
| uu____8722 -> begin
()
end));
(

let rec aux = (fun wl1 scope env1 subst1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
(

let uu____8822 = (rhs wl1 scope env1 subst1)
in (match (uu____8822) with
| (rhs_prob, wl2) -> begin
((

let uu____8842 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____8842) with
| true -> begin
(

let uu____8843 = (prob_to_string env1 rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" uu____8843))
end
| uu____8844 -> begin
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

let uu___136_8901 = hd1
in (

let uu____8902 = (FStar_Syntax_Subst.subst subst1 hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___136_8901.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___136_8901.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____8902}))
in (

let hd21 = (

let uu___137_8906 = hd2
in (

let uu____8907 = (FStar_Syntax_Subst.subst subst1 hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___137_8906.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___137_8906.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____8907}))
in (

let uu____8910 = (

let uu____8915 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_t_problem wl1 scope orig hd11.FStar_Syntax_Syntax.sort uu____8915 hd21.FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None "Formal parameter"))
in (match (uu____8910) with
| (prob, wl2) -> begin
(

let hd12 = (FStar_Syntax_Syntax.freshen_bv hd11)
in (

let subst2 = (

let uu____8934 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd12))))::uu____8934)
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 hd12)
in (

let uu____8938 = (aux wl2 (FStar_List.append scope ((((hd12), (imp)))::[])) env2 subst2 xs1 ys1)
in (match (uu____8938) with
| (FStar_Util.Inl (sub_probs, phi), wl3) -> begin
(

let phi1 = (

let uu____8993 = (close_forall env2 ((((hd12), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj (p_guard prob) uu____8993))
in ((

let uu____8995 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____8995) with
| true -> begin
(

let uu____8996 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____8997 = (FStar_Syntax_Print.bv_to_string hd12)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" uu____8996 uu____8997)))
end
| uu____8998 -> begin
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
| uu____9032 -> begin
((FStar_Util.Inr ("arity or argument-qualifier mismatch")), (wl1))
end))
in (

let scope = (p_scope orig)
in (

let uu____9068 = (aux wl scope env [] bs1 bs2)
in (match (uu____9068) with
| (FStar_Util.Inr (msg), wl1) -> begin
(giveup env msg orig)
end
| (FStar_Util.Inl (sub_probs, phi), wl1) -> begin
(

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some (phi)) [] wl1)
in (solve env (attempt sub_probs wl2)))
end))));
))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> ((def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb (problem)));
(

let uu____9115 = (compress_tprob wl.tcenv problem)
in (solve_t' env uu____9115 wl));
))
and solve_t_flex_rigid_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  flex_t  ->  FStar_Syntax_Syntax.term  ->  solution = (fun env orig wl lhs rhs -> (

let binders_as_bv_set = (fun bs -> (

let uu____9129 = (FStar_List.map FStar_Pervasives_Native.fst bs)
in (FStar_Util.as_set uu____9129 FStar_Syntax_Syntax.order_bv)))
in (

let mk_solution = (fun env1 lhs1 bs rhs1 -> (

let uu____9159 = lhs1
in (match (uu____9159) with
| (uu____9162, ctx_u, uu____9164) -> begin
(

let sol = (match (bs) with
| [] -> begin
rhs1
end
| uu____9170 -> begin
(

let uu____9171 = (sn_binders env1 bs)
in (u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ uu____9171 rhs1))
end)
in (TERM (((ctx_u), (sol))))::[])
end)))
in (

let try_quasi_pattern = (fun orig1 env1 wl1 lhs1 rhs1 -> (

let uu____9218 = (quasi_pattern env1 lhs1)
in (match (uu____9218) with
| FStar_Pervasives_Native.None -> begin
((FStar_Util.Inl ("Not a quasi-pattern")), (wl1))
end
| FStar_Pervasives_Native.Some (bs, uu____9248) -> begin
(

let uu____9253 = lhs1
in (match (uu____9253) with
| (t_lhs, ctx_u, args) -> begin
(

let uu____9267 = (occurs_check ctx_u rhs1)
in (match (uu____9267) with
| (uvars1, occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____9309 = (

let uu____9316 = (

let uu____9317 = (FStar_Option.get msg)
in (Prims.strcat "quasi-pattern, occurs-check failed: " uu____9317))
in FStar_Util.Inl (uu____9316))
in ((uu____9309), (wl1)))
end
| uu____9326 -> begin
(

let fvs_lhs = (binders_as_bv_set (FStar_List.append ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders bs))
in (

let fvs_rhs = (FStar_Syntax_Free.names rhs1)
in (

let uu____9337 = (

let uu____9338 = (FStar_Util.set_is_subset_of fvs_rhs fvs_lhs)
in (not (uu____9338)))
in (match (uu____9337) with
| true -> begin
((FStar_Util.Inl ("quasi-pattern, free names on the RHS are not included in the LHS")), (wl1))
end
| uu____9357 -> begin
(

let uu____9358 = (

let uu____9365 = (mk_solution env1 lhs1 bs rhs1)
in FStar_Util.Inr (uu____9365))
in (

let uu____9370 = (restrict_all_uvars ctx_u uvars1 wl1)
in ((uu____9358), (uu____9370))))
end))))
end)
end))
end))
end)))
in (

let first_order = (fun orig1 env1 wl1 lhs1 rhs1 -> (

let copy_uvar = (fun u t wl2 -> (new_uvar u.FStar_Syntax_Syntax.ctx_uvar_reason wl2 u.FStar_Syntax_Syntax.ctx_uvar_range u.FStar_Syntax_Syntax.ctx_uvar_gamma u.FStar_Syntax_Syntax.ctx_uvar_binders t u.FStar_Syntax_Syntax.ctx_uvar_should_check))
in (

let uu____9429 = (FStar_Syntax_Util.head_and_args rhs1)
in (match (uu____9429) with
| (rhs_hd, args) -> begin
(match (args) with
| [] -> begin
(

let uu____9472 = (

let uu____9473 = (prob_to_string env1 orig1)
in (FStar_Util.format1 "first_order heursitic cannot solve %s; rhs not an app" uu____9473))
in (giveup_or_defer env1 orig1 wl1 uu____9472))
end
| uu____9474 -> begin
(

let uu____9483 = (quasi_pattern env1 lhs1)
in (match (uu____9483) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9494 = (

let uu____9495 = (prob_to_string env1 orig1)
in (FStar_Util.format1 "first_order heursitic cannot solve %s; lhs not a quasi-pattern" uu____9495))
in (giveup_or_defer env1 orig1 wl1 uu____9494))
end
| FStar_Pervasives_Native.Some (bs_lhs, t_res_lhs) -> begin
(

let uu____9502 = (FStar_Util.prefix args)
in (match (uu____9502) with
| (args_rhs, last_arg_rhs) -> begin
(

let rhs' = (FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs FStar_Pervasives_Native.None rhs1.FStar_Syntax_Syntax.pos)
in (

let uu____9560 = lhs1
in (match (uu____9560) with
| (t_lhs, u_lhs, lhs_args) -> begin
(

let uu____9564 = (

let uu____9569 = (

let uu____9576 = (

let uu____9579 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9579))
in (copy_uvar u_lhs uu____9576 wl1))
in (match (uu____9569) with
| (uu____9594, t_last_arg, wl2) -> begin
(

let uu____9597 = (

let uu____9604 = (

let uu____9607 = (

let uu____9614 = (FStar_Syntax_Syntax.null_binder t_last_arg)
in (uu____9614)::[])
in (

let uu____9627 = (FStar_Syntax_Syntax.mk_Total t_res_lhs)
in (FStar_Syntax_Util.arrow uu____9607 uu____9627)))
in (copy_uvar u_lhs uu____9604 wl2))
in (match (uu____9597) with
| (uu____9634, lhs', wl3) -> begin
(

let uu____9637 = (copy_uvar u_lhs t_last_arg wl3)
in (match (uu____9637) with
| (uu____9648, lhs'_last_arg, wl4) -> begin
((lhs'), (lhs'_last_arg))
end))
end))
end))
in (match (uu____9564) with
| (lhs', lhs'_last_arg) -> begin
(

let sol = (

let uu____9656 = (

let uu____9657 = (

let uu____9662 = (

let uu____9663 = (

let uu____9666 = (

let uu____9671 = (

let uu____9672 = (FStar_Syntax_Syntax.as_arg lhs'_last_arg)
in (uu____9672)::[])
in (FStar_Syntax_Syntax.mk_Tm_app lhs' uu____9671))
in (uu____9666 FStar_Pervasives_Native.None t_lhs.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.abs bs_lhs uu____9663 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot t_res_lhs)))))
in ((u_lhs), (uu____9662)))
in TERM (uu____9657))
in (uu____9656)::[])
in (

let uu____9693 = (

let uu____9700 = (

let uu____9705 = (p_scope orig1)
in (mk_t_problem wl1 uu____9705 orig1 lhs' FStar_TypeChecker_Common.EQ rhs' FStar_Pervasives_Native.None "first-order lhs"))
in (match (uu____9700) with
| (p1, wl2) -> begin
(

let uu____9714 = (

let uu____9719 = (p_scope orig1)
in (mk_t_problem wl2 uu____9719 orig1 lhs'_last_arg FStar_TypeChecker_Common.EQ (FStar_Pervasives_Native.fst last_arg_rhs) FStar_Pervasives_Native.None "first-order rhs"))
in (match (uu____9714) with
| (p2, wl3) -> begin
(((p1)::(p2)::[]), (wl3))
end))
end))
in (match (uu____9693) with
| (sub_probs, wl2) -> begin
(

let uu____9738 = (

let uu____9739 = (solve_prob orig1 FStar_Pervasives_Native.None sol wl2)
in (attempt sub_probs uu____9739))
in (solve env1 uu____9738))
end)))
end))
end)))
end))
end))
end)
end))))
in (match ((p_rel orig)) with
| FStar_TypeChecker_Common.SUB -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer env orig wl "flex-rigid subtyping")
end
| uu____9740 -> begin
(solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.SUBINV -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer env orig wl "flex-rigid subtyping")
end
| uu____9741 -> begin
(solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.EQ -> begin
(

let uu____9742 = lhs
in (match (uu____9742) with
| (_t1, ctx_uv, args_lhs) -> begin
(

let uu____9746 = (pat_vars env ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs)
in (match (uu____9746) with
| FStar_Pervasives_Native.Some (lhs_binders) -> begin
(

let rhs1 = (sn env rhs)
in (

let names_to_string1 = (fun fvs -> (

let uu____9761 = (

let uu____9764 = (FStar_Util.set_elements fvs)
in (FStar_List.map FStar_Syntax_Print.bv_to_string uu____9764))
in (FStar_All.pipe_right uu____9761 (FStar_String.concat ", "))))
in (

let fvs1 = (binders_as_bv_set (FStar_List.append ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders lhs_binders))
in (

let fvs2 = (FStar_Syntax_Free.names rhs1)
in (

let uu____9779 = (occurs_check ctx_uv rhs1)
in (match (uu____9779) with
| (uvars1, occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____9801 = (

let uu____9802 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____9802))
in (giveup_or_defer env orig wl uu____9801))
end
| uu____9803 -> begin
(

let uu____9804 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____9804) with
| true -> begin
(

let sol = (mk_solution env lhs lhs_binders rhs1)
in (

let wl1 = (restrict_all_uvars ctx_uv uvars1 wl)
in (

let uu____9809 = (solve_prob orig FStar_Pervasives_Native.None sol wl1)
in (solve env uu____9809))))
end
| uu____9810 -> begin
(match (wl.defer_ok) with
| true -> begin
(

let uu____9811 = (

let uu____9812 = (names_to_string1 fvs2)
in (

let uu____9813 = (names_to_string1 fvs1)
in (

let uu____9814 = (FStar_Syntax_Print.binders_to_string ", " (FStar_List.append ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders lhs_binders))
in (FStar_Util.format3 "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}" uu____9812 uu____9813 uu____9814))))
in (giveup_or_defer env orig wl uu____9811))
end
| uu____9819 -> begin
(first_order orig env wl lhs rhs1)
end)
end))
end)
end))))))
end
| uu____9820 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer env orig wl "Not a pattern")
end
| uu____9823 -> begin
(

let uu____9824 = (try_quasi_pattern orig env wl lhs rhs)
in (match (uu____9824) with
| (FStar_Util.Inr (sol), wl1) -> begin
(

let uu____9847 = (solve_prob orig FStar_Pervasives_Native.None sol wl1)
in (solve env uu____9847))
end
| (FStar_Util.Inl (msg), uu____9849) -> begin
(first_order orig env wl lhs rhs)
end))
end)
end))
end))
end))))))
and solve_t_flex_flex : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  flex_t  ->  flex_t  ->  solution = (fun env orig wl lhs rhs -> (match ((p_rel orig)) with
| FStar_TypeChecker_Common.SUB -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer env orig wl "flex-flex subtyping")
end
| uu____9863 -> begin
(solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.SUBINV -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer env orig wl "flex-flex subtyping")
end
| uu____9864 -> begin
(solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs)
end)
end
| FStar_TypeChecker_Common.EQ -> begin
(

let uu____9865 = (

let uu____9882 = (quasi_pattern env lhs)
in (

let uu____9889 = (quasi_pattern env rhs)
in ((uu____9882), (uu____9889))))
in (match (uu____9865) with
| (FStar_Pervasives_Native.Some (binders_lhs, t_res_lhs), FStar_Pervasives_Native.Some (binders_rhs, t_res_rhs)) -> begin
(

let uu____9932 = lhs
in (match (uu____9932) with
| ({FStar_Syntax_Syntax.n = uu____9933; FStar_Syntax_Syntax.pos = range; FStar_Syntax_Syntax.vars = uu____9935}, u_lhs, uu____9937) -> begin
(

let uu____9940 = rhs
in (match (uu____9940) with
| (uu____9941, u_rhs, uu____9943) -> begin
(

let uu____9944 = ((FStar_Syntax_Unionfind.equiv u_lhs.FStar_Syntax_Syntax.ctx_uvar_head u_rhs.FStar_Syntax_Syntax.ctx_uvar_head) && (binders_eq binders_lhs binders_rhs))
in (match (uu____9944) with
| true -> begin
(

let uu____9945 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____9945))
end
| uu____9946 -> begin
(

let uu____9947 = (

let uu____9952 = (p_scope orig)
in (mk_t_problem wl uu____9952 orig t_res_lhs FStar_TypeChecker_Common.EQ t_res_rhs FStar_Pervasives_Native.None "flex-flex typing"))
in (match (uu____9947) with
| (sub_prob, wl1) -> begin
(

let uu____9955 = (maximal_prefix u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders)
in (match (uu____9955) with
| (ctx_w, (ctx_l, ctx_r)) -> begin
(

let gamma_w = (gamma_until u_lhs.FStar_Syntax_Syntax.ctx_uvar_gamma ctx_w)
in (

let zs = (intersect_binders (FStar_List.append ctx_l binders_lhs) (FStar_List.append ctx_r binders_rhs))
in (

let uu____9983 = (

let uu____9990 = (

let uu____9993 = (FStar_Syntax_Syntax.mk_Total t_res_lhs)
in (FStar_Syntax_Util.arrow zs uu____9993))
in (new_uvar (Prims.strcat "flex-flex quasi: lhs=" (Prims.strcat u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason (Prims.strcat ", rhs=" u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))) wl1 range gamma_w ctx_w uu____9990 (u_lhs.FStar_Syntax_Syntax.ctx_uvar_should_check || u_rhs.FStar_Syntax_Syntax.ctx_uvar_should_check)))
in (match (uu____9983) with
| (uu____9996, w, wl2) -> begin
(

let w_app = (

let uu____10002 = (

let uu____10007 = (FStar_List.map (fun uu____10016 -> (match (uu____10016) with
| (z, uu____10022) -> begin
(

let uu____10023 = (FStar_Syntax_Syntax.bv_to_name z)
in (FStar_Syntax_Syntax.as_arg uu____10023))
end)) zs)
in (FStar_Syntax_Syntax.mk_Tm_app w uu____10007))
in (uu____10002 FStar_Pervasives_Native.None w.FStar_Syntax_Syntax.pos))
in ((

let uu____10027 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____10027) with
| true -> begin
(

let uu____10028 = (flex_t_to_string lhs)
in (

let uu____10029 = (flex_t_to_string rhs)
in (

let uu____10030 = (

let uu____10031 = (destruct_flex_t w)
in (flex_t_to_string uu____10031))
in (FStar_Util.print3 "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s" uu____10028 uu____10029 uu____10030))))
end
| uu____10038 -> begin
()
end));
(

let sol = (

let s1 = (

let uu____10043 = (

let uu____10048 = (FStar_Syntax_Util.abs binders_lhs w_app (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot t_res_lhs))))
in ((u_lhs), (uu____10048)))
in TERM (uu____10043))
in (

let uu____10049 = (FStar_Syntax_Unionfind.equiv u_lhs.FStar_Syntax_Syntax.ctx_uvar_head u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____10049) with
| true -> begin
(s1)::[]
end
| uu____10052 -> begin
(

let s2 = (

let uu____10054 = (

let uu____10059 = (FStar_Syntax_Util.abs binders_rhs w_app (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot t_res_lhs))))
in ((u_rhs), (uu____10059)))
in TERM (uu____10054))
in (s1)::(s2)::[])
end)))
in (

let uu____10060 = (

let uu____10061 = (solve_prob orig FStar_Pervasives_Native.None sol wl2)
in (attempt ((sub_prob)::[]) uu____10061))
in (solve env uu____10060)));
))
end))))
end))
end))
end))
end))
end))
end
| uu____10062 -> begin
(giveup_or_defer env orig wl "flex-flex: non-patterns")
end))
end))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> ((def_check_prob "solve_t\'.1" (FStar_TypeChecker_Common.TProb (problem)));
(

let giveup_or_defer1 = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env1 orig wl1 head1 head2 t1 t2 -> (

let uu____10130 = (head_matches_delta env1 wl1 t1 t2)
in (match (uu____10130) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____10161), uu____10162) -> begin
(

let rec may_relate = (fun head3 -> (

let uu____10189 = (

let uu____10190 = (FStar_Syntax_Subst.compress head3)
in uu____10190.FStar_Syntax_Syntax.n)
in (match (uu____10189) with
| FStar_Syntax_Syntax.Tm_name (uu____10193) -> begin
true
end
| FStar_Syntax_Syntax.Tm_match (uu____10194) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____10217; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational; FStar_Syntax_Syntax.fv_qual = uu____10218}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____10221; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (uu____10222); FStar_Syntax_Syntax.fv_qual = uu____10223}) -> begin
(Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____10227, uu____10228) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____10270) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____10276) -> begin
(may_relate t)
end
| uu____10281 -> begin
false
end)))
in (

let uu____10282 = (((may_relate head1) || (may_relate head2)) && wl1.smt_ok)
in (match (uu____10282) with
| true -> begin
(

let uu____10283 = (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_eq2 wl1 orig t1 t2)
end
| uu____10292 -> begin
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

let uu____10311 = (

let uu____10312 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t11 uu____10312 t21))
in (FStar_Syntax_Util.mk_forall u_x x uu____10311))))
end))
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB)) with
| true -> begin
(

let uu____10317 = (has_type_guard t1 t2)
in ((uu____10317), (wl1)))
end
| uu____10322 -> begin
(

let uu____10323 = (has_type_guard t2 t1)
in ((uu____10323), (wl1)))
end))
end)
in (match (uu____10283) with
| (guard, wl2) -> begin
(

let uu____10330 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl2)
in (solve env1 uu____10330))
end))
end
| uu____10331 -> begin
(

let uu____10332 = (

let uu____10333 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____10334 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.format2 "head mismatch (%s vs %s)" uu____10333 uu____10334)))
in (giveup env1 uu____10332 orig))
end)))
end
| (uu____10335, FStar_Pervasives_Native.Some (t11, t21)) -> begin
(solve_t env1 (

let uu___138_10349 = problem
in {FStar_TypeChecker_Common.pid = uu___138_10349.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___138_10349.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___138_10349.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___138_10349.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___138_10349.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___138_10349.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___138_10349.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___138_10349.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___138_10349.FStar_TypeChecker_Common.rank}) wl1)
end
| (uu____10350, FStar_Pervasives_Native.None) -> begin
((

let uu____10362 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____10362) with
| true -> begin
(

let uu____10363 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10364 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____10365 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____10366 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" uu____10363 uu____10364 uu____10365 uu____10366)))))
end
| uu____10367 -> begin
()
end));
(

let uu____10368 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____10368) with
| (head11, args1) -> begin
(

let uu____10405 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____10405) with
| (head21, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((Prims.op_disEquality nargs (FStar_List.length args2))) with
| true -> begin
(

let uu____10459 = (

let uu____10460 = (FStar_Syntax_Print.term_to_string head11)
in (

let uu____10461 = (args_to_string args1)
in (

let uu____10462 = (FStar_Syntax_Print.term_to_string head21)
in (

let uu____10463 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____10460 uu____10461 uu____10462 uu____10463)))))
in (giveup env1 uu____10459 orig))
end
| uu____10464 -> begin
(

let uu____10465 = ((Prims.op_Equality nargs (Prims.parse_int "0")) || (

let uu____10471 = (FStar_Syntax_Util.eq_args args1 args2)
in (Prims.op_Equality uu____10471 FStar_Syntax_Util.Equal)))
in (match (uu____10465) with
| true -> begin
(

let uu____10472 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____10472) with
| USolved (wl2) -> begin
(

let uu____10474 = (solve_prob orig FStar_Pervasives_Native.None [] wl2)
in (solve env1 uu____10474))
end
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end))
end
| uu____10477 -> begin
(

let uu____10478 = (base_and_refinement env1 t1)
in (match (uu____10478) with
| (base1, refinement1) -> begin
(

let uu____10503 = (base_and_refinement env1 t2)
in (match (uu____10503) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(

let uu____10560 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____10560) with
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end
| USolved (wl2) -> begin
(

let uu____10564 = (FStar_List.fold_right2 (fun uu____10597 uu____10598 uu____10599 -> (match (((uu____10597), (uu____10598), (uu____10599))) with
| ((a, uu____10635), (a', uu____10637), (subprobs, wl3)) -> begin
(

let uu____10658 = (

let uu____10663 = (p_scope orig)
in (mk_t_problem wl3 uu____10663 orig a FStar_TypeChecker_Common.EQ a' FStar_Pervasives_Native.None "index"))
in (match (uu____10658) with
| (p, wl4) -> begin
(((p)::subprobs), (wl4))
end))
end)) args1 args2 (([]), (wl2)))
in (match (uu____10564) with
| (subprobs, wl3) -> begin
(

let formula = (

let uu____10683 = (FStar_List.map (fun p -> (p_guard p)) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____10683))
in (

let wl4 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) [] wl3)
in (solve env1 (attempt subprobs wl4))))
end))
end))
end
| uu____10689 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env1 (

let uu___139_10729 = problem
in {FStar_TypeChecker_Common.pid = uu___139_10729.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___139_10729.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___139_10729.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___139_10729.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___139_10729.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___139_10729.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___139_10729.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___139_10729.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___139_10729.FStar_TypeChecker_Common.rank}) wl1)))
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

let uu____10732 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____10732) with
| true -> begin
(

let uu____10733 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____10733))
end
| uu____10734 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in (

let uu____10737 = (FStar_Util.physical_equality t1 t2)
in (match (uu____10737) with
| true -> begin
(

let uu____10738 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____10738))
end
| uu____10739 -> begin
((

let uu____10741 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____10741) with
| true -> begin
(

let uu____10742 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____10743 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____10744 = (prob_to_string env orig)
in (FStar_Util.print3 "Attempting (%s - %s)\n%s\n" uu____10742 uu____10743 uu____10744))))
end
| uu____10745 -> begin
()
end));
(

let r = (FStar_TypeChecker_Env.get_range env)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_delayed (uu____10747), uu____10748) -> begin
(failwith "Impossible: terms were not compressed")
end
| (uu____10773, FStar_Syntax_Syntax.Tm_delayed (uu____10774)) -> begin
(failwith "Impossible: terms were not compressed")
end
| (FStar_Syntax_Syntax.Tm_ascribed (uu____10799), uu____10800) -> begin
(

let uu____10827 = (

let uu___140_10828 = problem
in (

let uu____10829 = (FStar_Syntax_Util.unascribe t1)
in {FStar_TypeChecker_Common.pid = uu___140_10828.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____10829; FStar_TypeChecker_Common.relation = uu___140_10828.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___140_10828.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___140_10828.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___140_10828.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___140_10828.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___140_10828.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___140_10828.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___140_10828.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___140_10828.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____10827 wl))
end
| (FStar_Syntax_Syntax.Tm_meta (uu____10830), uu____10831) -> begin
(

let uu____10838 = (

let uu___141_10839 = problem
in (

let uu____10840 = (FStar_Syntax_Util.unmeta t1)
in {FStar_TypeChecker_Common.pid = uu___141_10839.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____10840; FStar_TypeChecker_Common.relation = uu___141_10839.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___141_10839.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___141_10839.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___141_10839.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___141_10839.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___141_10839.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___141_10839.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___141_10839.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___141_10839.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____10838 wl))
end
| (uu____10841, FStar_Syntax_Syntax.Tm_ascribed (uu____10842)) -> begin
(

let uu____10869 = (

let uu___142_10870 = problem
in (

let uu____10871 = (FStar_Syntax_Util.unascribe t2)
in {FStar_TypeChecker_Common.pid = uu___142_10870.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___142_10870.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___142_10870.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____10871; FStar_TypeChecker_Common.element = uu___142_10870.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___142_10870.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___142_10870.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___142_10870.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___142_10870.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___142_10870.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___142_10870.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____10869 wl))
end
| (uu____10872, FStar_Syntax_Syntax.Tm_meta (uu____10873)) -> begin
(

let uu____10880 = (

let uu___143_10881 = problem
in (

let uu____10882 = (FStar_Syntax_Util.unmeta t2)
in {FStar_TypeChecker_Common.pid = uu___143_10881.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___143_10881.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___143_10881.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____10882; FStar_TypeChecker_Common.element = uu___143_10881.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___143_10881.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___143_10881.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___143_10881.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___143_10881.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___143_10881.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___143_10881.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____10880 wl))
end
| (FStar_Syntax_Syntax.Tm_quoted (t11, uu____10884), FStar_Syntax_Syntax.Tm_quoted (t21, uu____10886)) -> begin
(

let uu____10895 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____10895))
end
| (FStar_Syntax_Syntax.Tm_bvar (uu____10896), uu____10897) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (uu____10898, FStar_Syntax_Syntax.Tm_bvar (uu____10899)) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (FStar_Syntax_Syntax.Tm_type (u1), FStar_Syntax_Syntax.Tm_type (u2)) -> begin
(solve_one_universe_eq env orig u1 u2 wl)
end
| (FStar_Syntax_Syntax.Tm_arrow (bs1, c1), FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) -> begin
(

let mk_c = (fun c uu___106_10956 -> (match (uu___106_10956) with
| [] -> begin
c
end
| bs -> begin
(

let uu____10976 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____10976))
end))
in (

let uu____10985 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____10985) with
| ((bs11, c11), (bs21, c21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun wl1 scope env1 subst1 -> (

let c12 = (FStar_Syntax_Subst.subst_comp subst1 c11)
in (

let c22 = (FStar_Syntax_Subst.subst_comp subst1 c21)
in (

let rel = (

let uu____11108 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____11108) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____11109 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (mk_c_problem wl1 scope orig c12 rel c22 FStar_Pervasives_Native.None "function co-domain"))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___107_11183 -> (match (uu___107_11183) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____11217 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____11217) with
| ((bs11, tbody11), (bs21, tbody21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun wl1 scope env1 subst1 -> (

let uu____11336 = (FStar_Syntax_Subst.subst subst1 tbody11)
in (

let uu____11337 = (FStar_Syntax_Subst.subst subst1 tbody21)
in (mk_t_problem wl1 scope orig uu____11336 problem.FStar_TypeChecker_Common.relation uu____11337 FStar_Pervasives_Native.None "lambda co-domain")))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (uu____11338), uu____11339) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____11366) -> begin
true
end
| uu____11383 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____11402 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____11408 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let force_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
t
end
| uu____11419 -> begin
(

let uu____11420 = (env.FStar_TypeChecker_Env.type_of (

let uu___144_11428 = env
in {FStar_TypeChecker_Env.solver = uu___144_11428.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___144_11428.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___144_11428.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___144_11428.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___144_11428.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___144_11428.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___144_11428.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___144_11428.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___144_11428.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___144_11428.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___144_11428.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___144_11428.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___144_11428.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___144_11428.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___144_11428.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___144_11428.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___144_11428.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___144_11428.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___144_11428.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___144_11428.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___144_11428.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___144_11428.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___144_11428.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___144_11428.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___144_11428.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___144_11428.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___144_11428.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___144_11428.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___144_11428.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___144_11428.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___144_11428.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___144_11428.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___144_11428.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___144_11428.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___144_11428.FStar_TypeChecker_Env.dep_graph}) t)
in (match (uu____11420) with
| (uu____11429, ty, uu____11431) -> begin
(

let uu____11432 = (FStar_TypeChecker_Normalize.unfold_whnf env ty)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env t uu____11432))
end))
end))
in (

let uu____11433 = (

let uu____11446 = (maybe_eta t1)
in (

let uu____11451 = (maybe_eta t2)
in ((uu____11446), (uu____11451))))
in (match (uu____11433) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___145_11475 = problem
in {FStar_TypeChecker_Common.pid = uu___145_11475.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___145_11475.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___145_11475.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___145_11475.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___145_11475.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___145_11475.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___145_11475.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___145_11475.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___145_11475.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____11486 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____11486) with
| true -> begin
(

let uu____11487 = (destruct_flex_t not_abs)
in (solve_t_flex_rigid_eq env orig wl uu____11487 t_abs))
end
| uu____11488 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___146_11492 = problem
in {FStar_TypeChecker_Common.pid = uu___146_11492.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___146_11492.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___146_11492.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___146_11492.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___146_11492.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___146_11492.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___146_11492.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___146_11492.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___146_11492.FStar_TypeChecker_Common.rank}) wl)
end
| uu____11493 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____11504 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____11504) with
| true -> begin
(

let uu____11505 = (destruct_flex_t not_abs)
in (solve_t_flex_rigid_eq env orig wl uu____11505 t_abs))
end
| uu____11506 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___146_11510 = problem
in {FStar_TypeChecker_Common.pid = uu___146_11510.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___146_11510.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___146_11510.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___146_11510.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___146_11510.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___146_11510.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___146_11510.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___146_11510.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___146_11510.FStar_TypeChecker_Common.rank}) wl)
end
| uu____11511 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| uu____11512 -> begin
(failwith "Impossible: at least one side is an abstraction")
end)))))
end
| (uu____11525, FStar_Syntax_Syntax.Tm_abs (uu____11526)) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____11553) -> begin
true
end
| uu____11570 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____11589 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____11595 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let force_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
t
end
| uu____11606 -> begin
(

let uu____11607 = (env.FStar_TypeChecker_Env.type_of (

let uu___144_11615 = env
in {FStar_TypeChecker_Env.solver = uu___144_11615.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___144_11615.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___144_11615.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___144_11615.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___144_11615.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___144_11615.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___144_11615.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___144_11615.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___144_11615.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___144_11615.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___144_11615.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___144_11615.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___144_11615.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___144_11615.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___144_11615.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___144_11615.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___144_11615.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___144_11615.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___144_11615.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___144_11615.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___144_11615.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___144_11615.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___144_11615.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___144_11615.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___144_11615.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___144_11615.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___144_11615.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___144_11615.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___144_11615.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___144_11615.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___144_11615.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___144_11615.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___144_11615.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___144_11615.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___144_11615.FStar_TypeChecker_Env.dep_graph}) t)
in (match (uu____11607) with
| (uu____11616, ty, uu____11618) -> begin
(

let uu____11619 = (FStar_TypeChecker_Normalize.unfold_whnf env ty)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env t uu____11619))
end))
end))
in (

let uu____11620 = (

let uu____11633 = (maybe_eta t1)
in (

let uu____11638 = (maybe_eta t2)
in ((uu____11633), (uu____11638))))
in (match (uu____11620) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___145_11662 = problem
in {FStar_TypeChecker_Common.pid = uu___145_11662.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___145_11662.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___145_11662.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___145_11662.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___145_11662.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___145_11662.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___145_11662.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___145_11662.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___145_11662.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____11673 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____11673) with
| true -> begin
(

let uu____11674 = (destruct_flex_t not_abs)
in (solve_t_flex_rigid_eq env orig wl uu____11674 t_abs))
end
| uu____11675 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___146_11679 = problem
in {FStar_TypeChecker_Common.pid = uu___146_11679.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___146_11679.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___146_11679.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___146_11679.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___146_11679.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___146_11679.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___146_11679.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___146_11679.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___146_11679.FStar_TypeChecker_Common.rank}) wl)
end
| uu____11680 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____11691 = ((is_flex not_abs) && (Prims.op_Equality (p_rel orig) FStar_TypeChecker_Common.EQ))
in (match (uu____11691) with
| true -> begin
(

let uu____11692 = (destruct_flex_t not_abs)
in (solve_t_flex_rigid_eq env orig wl uu____11692 t_abs))
end
| uu____11693 -> begin
(

let t11 = (force_eta t1)
in (

let t21 = (force_eta t2)
in (match (((is_abs t11) && (is_abs t21))) with
| true -> begin
(solve_t env (

let uu___146_11697 = problem
in {FStar_TypeChecker_Common.pid = uu___146_11697.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___146_11697.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___146_11697.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___146_11697.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___146_11697.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___146_11697.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___146_11697.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___146_11697.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___146_11697.FStar_TypeChecker_Common.rank}) wl)
end
| uu____11698 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end)))
end))
end
| uu____11699 -> begin
(failwith "Impossible: at least one side is an abstraction")
end)))))
end
| (FStar_Syntax_Syntax.Tm_refine (x1, ph1), FStar_Syntax_Syntax.Tm_refine (x2, phi2)) -> begin
(

let should_delta = (((

let uu____11727 = (FStar_Syntax_Free.uvars t1)
in (FStar_Util.set_is_empty uu____11727)) && (

let uu____11731 = (FStar_Syntax_Free.uvars t2)
in (FStar_Util.set_is_empty uu____11731))) && (

let uu____11738 = (head_matches env x1.FStar_Syntax_Syntax.sort x2.FStar_Syntax_Syntax.sort)
in (match (uu____11738) with
| MisMatch (FStar_Pervasives_Native.Some (d1), FStar_Pervasives_Native.Some (d2)) -> begin
(

let is_unfoldable = (fun uu___108_11750 -> (match (uu___108_11750) with
| FStar_Syntax_Syntax.Delta_constant -> begin
true
end
| FStar_Syntax_Syntax.Delta_defined_at_level (uu____11751) -> begin
true
end
| uu____11752 -> begin
false
end))
in ((is_unfoldable d1) && (is_unfoldable d2)))
end
| uu____11753 -> begin
false
end)))
in (

let uu____11754 = (as_refinement should_delta env wl t1)
in (match (uu____11754) with
| (x11, phi1) -> begin
(

let uu____11761 = (as_refinement should_delta env wl t2)
in (match (uu____11761) with
| (x21, phi21) -> begin
(

let uu____11768 = (

let uu____11773 = (p_scope orig)
in (mk_t_problem wl uu____11773 orig x11.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x21.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type"))
in (match (uu____11768) with
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

let uu____11817 = (imp phi12 phi23)
in (FStar_All.pipe_right uu____11817 (guard_on_element wl1 problem x12))))
in (

let fallback = (fun uu____11823 -> (

let impl = (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp1 FStar_Syntax_Util.mk_iff phi11 phi22)
end
| uu____11825 -> begin
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

let uu____11830 = (

let uu____11835 = (

let uu____11836 = (p_scope orig)
in (

let uu____11843 = (

let uu____11850 = (FStar_Syntax_Syntax.mk_binder x12)
in (uu____11850)::[])
in (FStar_List.append uu____11836 uu____11843)))
in (mk_t_problem wl1 uu____11835 orig phi11 FStar_TypeChecker_Common.EQ phi22 FStar_Pervasives_Native.None "refinement formula"))
in (match (uu____11830) with
| (ref_prob, wl2) -> begin
(

let uu____11869 = (solve env1 (

let uu___147_11871 = wl2
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___147_11871.ctr; defer_ok = false; smt_ok = uu___147_11871.smt_ok; tcenv = uu___147_11871.tcenv; wl_implicits = uu___147_11871.wl_implicits}))
in (match (uu____11869) with
| Failed (uu____11878) -> begin
(fallback ())
end
| Success (uu____11883) -> begin
(

let guard = (

let uu____11891 = (FStar_All.pipe_right (p_guard ref_prob) (guard_on_element wl2 problem x12))
in (FStar_Syntax_Util.mk_conj (p_guard base_prob) uu____11891))
in (

let wl3 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl2)
in (

let wl4 = (

let uu___148_11894 = wl3
in {attempting = uu___148_11894.attempting; wl_deferred = uu___148_11894.wl_deferred; ctr = (wl3.ctr + (Prims.parse_int "1")); defer_ok = uu___148_11894.defer_ok; smt_ok = uu___148_11894.smt_ok; tcenv = uu___148_11894.tcenv; wl_implicits = uu___148_11894.wl_implicits})
in (solve env1 (attempt ((base_prob)::[]) wl4)))))
end))
end))
end
| uu____11895 -> begin
(fallback ())
end))))))))
end))
end))
end)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____11896), FStar_Syntax_Syntax.Tm_uvar (uu____11897)) -> begin
(

let uu____11898 = (destruct_flex_t t1)
in (

let uu____11899 = (destruct_flex_t t2)
in (solve_t_flex_flex env orig wl uu____11898 uu____11899)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____11900); FStar_Syntax_Syntax.pos = uu____11901; FStar_Syntax_Syntax.vars = uu____11902}, uu____11903), FStar_Syntax_Syntax.Tm_uvar (uu____11904)) -> begin
(

let uu____11925 = (destruct_flex_t t1)
in (

let uu____11926 = (destruct_flex_t t2)
in (solve_t_flex_flex env orig wl uu____11925 uu____11926)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____11927), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____11928); FStar_Syntax_Syntax.pos = uu____11929; FStar_Syntax_Syntax.vars = uu____11930}, uu____11931)) -> begin
(

let uu____11952 = (destruct_flex_t t1)
in (

let uu____11953 = (destruct_flex_t t2)
in (solve_t_flex_flex env orig wl uu____11952 uu____11953)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____11954); FStar_Syntax_Syntax.pos = uu____11955; FStar_Syntax_Syntax.vars = uu____11956}, uu____11957), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____11958); FStar_Syntax_Syntax.pos = uu____11959; FStar_Syntax_Syntax.vars = uu____11960}, uu____11961)) -> begin
(

let uu____12002 = (destruct_flex_t t1)
in (

let uu____12003 = (destruct_flex_t t2)
in (solve_t_flex_flex env orig wl uu____12002 uu____12003)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____12004), uu____12005) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(

let uu____12006 = (destruct_flex_t t1)
in (solve_t_flex_rigid_eq env orig wl uu____12006 t2))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12007); FStar_Syntax_Syntax.pos = uu____12008; FStar_Syntax_Syntax.vars = uu____12009}, uu____12010), uu____12011) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(

let uu____12032 = (destruct_flex_t t1)
in (solve_t_flex_rigid_eq env orig wl uu____12032 t2))
end
| (uu____12033, FStar_Syntax_Syntax.Tm_uvar (uu____12034)) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (uu____12035, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12036); FStar_Syntax_Syntax.pos = uu____12037; FStar_Syntax_Syntax.vars = uu____12038}, uu____12039)) when (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____12060), FStar_Syntax_Syntax.Tm_type (uu____12061)) -> begin
(solve_t' env (

let uu___149_12063 = problem
in {FStar_TypeChecker_Common.pid = uu___149_12063.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___149_12063.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___149_12063.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___149_12063.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___149_12063.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___149_12063.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___149_12063.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___149_12063.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___149_12063.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___149_12063.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12064); FStar_Syntax_Syntax.pos = uu____12065; FStar_Syntax_Syntax.vars = uu____12066}, uu____12067), FStar_Syntax_Syntax.Tm_type (uu____12068)) -> begin
(solve_t' env (

let uu___149_12090 = problem
in {FStar_TypeChecker_Common.pid = uu___149_12090.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___149_12090.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___149_12090.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___149_12090.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___149_12090.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___149_12090.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___149_12090.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___149_12090.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___149_12090.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___149_12090.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____12091), FStar_Syntax_Syntax.Tm_arrow (uu____12092)) -> begin
(solve_t' env (

let uu___149_12106 = problem
in {FStar_TypeChecker_Common.pid = uu___149_12106.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___149_12106.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___149_12106.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___149_12106.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___149_12106.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___149_12106.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___149_12106.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___149_12106.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___149_12106.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___149_12106.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12107); FStar_Syntax_Syntax.pos = uu____12108; FStar_Syntax_Syntax.vars = uu____12109}, uu____12110), FStar_Syntax_Syntax.Tm_arrow (uu____12111)) -> begin
(solve_t' env (

let uu___149_12145 = problem
in {FStar_TypeChecker_Common.pid = uu___149_12145.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___149_12145.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___149_12145.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___149_12145.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___149_12145.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___149_12145.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___149_12145.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___149_12145.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___149_12145.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___149_12145.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____12146), uu____12147) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____12148 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____12150 = (

let uu____12151 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____12151))
in (match (uu____12150) with
| true -> begin
(

let uu____12152 = (FStar_All.pipe_left (fun _0_26 -> FStar_TypeChecker_Common.TProb (_0_26)) (

let uu___150_12156 = problem
in {FStar_TypeChecker_Common.pid = uu___150_12156.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___150_12156.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___150_12156.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___150_12156.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___150_12156.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___150_12156.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___150_12156.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___150_12156.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___150_12156.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___150_12156.FStar_TypeChecker_Common.rank}))
in (

let uu____12157 = (destruct_flex_t t1)
in (solve_t_flex_rigid_eq env uu____12152 wl uu____12157 t2)))
end
| uu____12158 -> begin
(

let uu____12159 = (base_and_refinement env t2)
in (match (uu____12159) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12188 = (FStar_All.pipe_left (fun _0_27 -> FStar_TypeChecker_Common.TProb (_0_27)) (

let uu___151_12192 = problem
in {FStar_TypeChecker_Common.pid = uu___151_12192.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___151_12192.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___151_12192.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___151_12192.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___151_12192.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___151_12192.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___151_12192.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___151_12192.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___151_12192.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___151_12192.FStar_TypeChecker_Common.rank}))
in (

let uu____12193 = (destruct_flex_t t1)
in (solve_t_flex_rigid_eq env uu____12188 wl uu____12193 t_base)))
end
| FStar_Pervasives_Native.Some (y, phi) -> begin
(

let y' = (

let uu___152_12201 = y
in {FStar_Syntax_Syntax.ppname = uu___152_12201.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___152_12201.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let uu____12203 = (mk_t_problem wl problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (match (uu____12203) with
| (base_prob, wl1) -> begin
(

let guard = (FStar_Syntax_Util.mk_conj (p_guard base_prob) impl)
in (

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl1)
in (solve env (attempt ((base_prob)::[]) wl2))))
end))))
end)
end))
end)))
end)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12214); FStar_Syntax_Syntax.pos = uu____12215; FStar_Syntax_Syntax.vars = uu____12216}, uu____12217), uu____12218) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____12239 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____12241 = (

let uu____12242 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____12242))
in (match (uu____12241) with
| true -> begin
(

let uu____12243 = (FStar_All.pipe_left (fun _0_28 -> FStar_TypeChecker_Common.TProb (_0_28)) (

let uu___150_12247 = problem
in {FStar_TypeChecker_Common.pid = uu___150_12247.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___150_12247.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___150_12247.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___150_12247.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___150_12247.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___150_12247.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___150_12247.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___150_12247.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___150_12247.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___150_12247.FStar_TypeChecker_Common.rank}))
in (

let uu____12248 = (destruct_flex_t t1)
in (solve_t_flex_rigid_eq env uu____12243 wl uu____12248 t2)))
end
| uu____12249 -> begin
(

let uu____12250 = (base_and_refinement env t2)
in (match (uu____12250) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12279 = (FStar_All.pipe_left (fun _0_29 -> FStar_TypeChecker_Common.TProb (_0_29)) (

let uu___151_12283 = problem
in {FStar_TypeChecker_Common.pid = uu___151_12283.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___151_12283.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___151_12283.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___151_12283.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___151_12283.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___151_12283.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___151_12283.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___151_12283.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___151_12283.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___151_12283.FStar_TypeChecker_Common.rank}))
in (

let uu____12284 = (destruct_flex_t t1)
in (solve_t_flex_rigid_eq env uu____12279 wl uu____12284 t_base)))
end
| FStar_Pervasives_Native.Some (y, phi) -> begin
(

let y' = (

let uu___152_12292 = y
in {FStar_Syntax_Syntax.ppname = uu___152_12292.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___152_12292.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let uu____12294 = (mk_t_problem wl problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (match (uu____12294) with
| (base_prob, wl1) -> begin
(

let guard = (FStar_Syntax_Util.mk_conj (p_guard base_prob) impl)
in (

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl1)
in (solve env (attempt ((base_prob)::[]) wl2))))
end))))
end)
end))
end)))
end)
end
| (uu____12305, FStar_Syntax_Syntax.Tm_uvar (uu____12306)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| uu____12307 -> begin
(

let uu____12308 = (base_and_refinement env t1)
in (match (uu____12308) with
| (t_base, uu____12320) -> begin
(solve_t env (

let uu___153_12334 = problem
in {FStar_TypeChecker_Common.pid = uu___153_12334.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___153_12334.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___153_12334.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___153_12334.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___153_12334.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___153_12334.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___153_12334.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___153_12334.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___153_12334.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (uu____12335, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12336); FStar_Syntax_Syntax.pos = uu____12337; FStar_Syntax_Syntax.vars = uu____12338}, uu____12339)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| uu____12360 -> begin
(

let uu____12361 = (base_and_refinement env t1)
in (match (uu____12361) with
| (t_base, uu____12373) -> begin
(solve_t env (

let uu___153_12387 = problem
in {FStar_TypeChecker_Common.pid = uu___153_12387.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___153_12387.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___153_12387.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___153_12387.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___153_12387.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___153_12387.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___153_12387.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___153_12387.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___153_12387.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (FStar_Syntax_Syntax.Tm_refine (uu____12388), uu____12389) -> begin
(

let t21 = (

let uu____12397 = (base_and_refinement env t2)
in (FStar_All.pipe_left force_refinement uu____12397))
in (solve_t env (

let uu___154_12423 = problem
in {FStar_TypeChecker_Common.pid = uu___154_12423.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___154_12423.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___154_12423.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___154_12423.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___154_12423.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___154_12423.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___154_12423.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___154_12423.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___154_12423.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___154_12423.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____12424, FStar_Syntax_Syntax.Tm_refine (uu____12425)) -> begin
(

let t11 = (

let uu____12433 = (base_and_refinement env t1)
in (FStar_All.pipe_left force_refinement uu____12433))
in (solve_t env (

let uu___155_12459 = problem
in {FStar_TypeChecker_Common.pid = uu___155_12459.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___155_12459.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___155_12459.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___155_12459.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___155_12459.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___155_12459.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___155_12459.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___155_12459.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___155_12459.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___155_12459.FStar_TypeChecker_Common.rank}) wl))
end
| (FStar_Syntax_Syntax.Tm_match (t11, brs1), FStar_Syntax_Syntax.Tm_match (t21, brs2)) -> begin
(

let uu____12536 = (

let uu____12541 = (p_scope orig)
in (mk_t_problem wl uu____12541 orig t11 FStar_TypeChecker_Common.EQ t21 FStar_Pervasives_Native.None "match scrutinee"))
in (match (uu____12536) with
| (sc_prob, wl1) -> begin
(

let rec solve_branches = (fun wl2 brs11 brs21 -> (match (((brs11), (brs21))) with
| ((br1)::rs1, (br2)::rs2) -> begin
(

let uu____12754 = br1
in (match (uu____12754) with
| (p1, w1, uu____12779) -> begin
(

let uu____12796 = br2
in (match (uu____12796) with
| (p2, w2, uu____12815) -> begin
(

let uu____12820 = (

let uu____12821 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (not (uu____12821)))
in (match (uu____12820) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____12836 -> begin
(

let uu____12837 = (FStar_Syntax_Subst.open_branch' br1)
in (match (uu____12837) with
| ((p11, w11, e1), s) -> begin
(

let uu____12870 = br2
in (match (uu____12870) with
| (p21, w21, e2) -> begin
(

let w22 = (FStar_Util.map_opt w21 (FStar_Syntax_Subst.subst s))
in (

let e21 = (FStar_Syntax_Subst.subst s e2)
in (

let scope = (

let uu____12905 = (p_scope orig)
in (

let uu____12912 = (

let uu____12919 = (FStar_Syntax_Syntax.pat_bvs p11)
in (FStar_All.pipe_left (FStar_List.map FStar_Syntax_Syntax.mk_binder) uu____12919))
in (FStar_List.append uu____12905 uu____12912)))
in (

let uu____12934 = (match (((w11), (w22))) with
| (FStar_Pervasives_Native.Some (uu____12955), FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (uu____12966)) -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.Some ((([]), (wl2)))
end
| (FStar_Pervasives_Native.Some (w12), FStar_Pervasives_Native.Some (w23)) -> begin
(

let uu____12995 = (mk_t_problem wl2 scope orig w12 FStar_TypeChecker_Common.EQ w23 FStar_Pervasives_Native.None "when clause")
in (match (uu____12995) with
| (p, wl3) -> begin
FStar_Pervasives_Native.Some ((((p)::[]), (wl3)))
end))
end)
in (FStar_Util.bind_opt uu____12934 (fun uu____13037 -> (match (uu____13037) with
| (wprobs, wl3) -> begin
(

let uu____13058 = (mk_t_problem wl3 scope orig e1 FStar_TypeChecker_Common.EQ e21 FStar_Pervasives_Native.None "branch body")
in (match (uu____13058) with
| (prob, wl4) -> begin
(

let uu____13073 = (solve_branches wl4 rs1 rs2)
in (FStar_Util.bind_opt uu____13073 (fun uu____13097 -> (match (uu____13097) with
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
| uu____13182 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____13219 = (solve_branches wl1 brs1 brs2)
in (match (uu____13219) with
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
| (FStar_Syntax_Syntax.Tm_match (uu____13250), uu____13251) -> begin
(

let head1 = (

let uu____13275 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13275 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13315 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13315 FStar_Pervasives_Native.fst))
in ((

let uu____13355 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____13355) with
| true -> begin
(

let uu____13356 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____13357 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____13358 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____13356 uu____13357 uu____13358))))
end
| uu____13359 -> begin
()
end));
(

let uu____13360 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____13360) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13367 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13367) with
| true -> begin
(

let uu____13368 = (

let uu____13375 = (

let uu____13376 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____13376 FStar_Syntax_Util.Equal))
in (match (uu____13375) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____13385 -> begin
(

let uu____13386 = (mk_eq2 wl orig t1 t2)
in (match (uu____13386) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____13368) with
| (guard, wl1) -> begin
(

let uu____13407 = (solve_prob orig guard [] wl1)
in (solve env uu____13407))
end))
end
| uu____13408 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13409 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____13410), uu____13411) -> begin
(

let head1 = (

let uu____13419 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13419 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13459 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13459 FStar_Pervasives_Native.fst))
in ((

let uu____13499 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____13499) with
| true -> begin
(

let uu____13500 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____13501 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____13502 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____13500 uu____13501 uu____13502))))
end
| uu____13503 -> begin
()
end));
(

let uu____13504 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____13504) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13511 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13511) with
| true -> begin
(

let uu____13512 = (

let uu____13519 = (

let uu____13520 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____13520 FStar_Syntax_Util.Equal))
in (match (uu____13519) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____13529 -> begin
(

let uu____13530 = (mk_eq2 wl orig t1 t2)
in (match (uu____13530) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____13512) with
| (guard, wl1) -> begin
(

let uu____13551 = (solve_prob orig guard [] wl1)
in (solve env uu____13551))
end))
end
| uu____13552 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13553 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_name (uu____13554), uu____13555) -> begin
(

let head1 = (

let uu____13557 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13557 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13597 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13597 FStar_Pervasives_Native.fst))
in ((

let uu____13637 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____13637) with
| true -> begin
(

let uu____13638 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____13639 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____13640 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____13638 uu____13639 uu____13640))))
end
| uu____13641 -> begin
()
end));
(

let uu____13642 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____13642) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13649 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13649) with
| true -> begin
(

let uu____13650 = (

let uu____13657 = (

let uu____13658 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____13658 FStar_Syntax_Util.Equal))
in (match (uu____13657) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____13667 -> begin
(

let uu____13668 = (mk_eq2 wl orig t1 t2)
in (match (uu____13668) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____13650) with
| (guard, wl1) -> begin
(

let uu____13689 = (solve_prob orig guard [] wl1)
in (solve env uu____13689))
end))
end
| uu____13690 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13691 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_constant (uu____13692), uu____13693) -> begin
(

let head1 = (

let uu____13695 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13695 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13735 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13735 FStar_Pervasives_Native.fst))
in ((

let uu____13775 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____13775) with
| true -> begin
(

let uu____13776 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____13777 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____13778 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____13776 uu____13777 uu____13778))))
end
| uu____13779 -> begin
()
end));
(

let uu____13780 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____13780) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13787 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13787) with
| true -> begin
(

let uu____13788 = (

let uu____13795 = (

let uu____13796 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____13796 FStar_Syntax_Util.Equal))
in (match (uu____13795) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____13805 -> begin
(

let uu____13806 = (mk_eq2 wl orig t1 t2)
in (match (uu____13806) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____13788) with
| (guard, wl1) -> begin
(

let uu____13827 = (solve_prob orig guard [] wl1)
in (solve env uu____13827))
end))
end
| uu____13828 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13829 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____13830), uu____13831) -> begin
(

let head1 = (

let uu____13833 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13833 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13873 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13873 FStar_Pervasives_Native.fst))
in ((

let uu____13913 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____13913) with
| true -> begin
(

let uu____13914 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____13915 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____13916 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____13914 uu____13915 uu____13916))))
end
| uu____13917 -> begin
()
end));
(

let uu____13918 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____13918) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13925 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13925) with
| true -> begin
(

let uu____13926 = (

let uu____13933 = (

let uu____13934 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____13934 FStar_Syntax_Util.Equal))
in (match (uu____13933) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____13943 -> begin
(

let uu____13944 = (mk_eq2 wl orig t1 t2)
in (match (uu____13944) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____13926) with
| (guard, wl1) -> begin
(

let uu____13965 = (solve_prob orig guard [] wl1)
in (solve env uu____13965))
end))
end
| uu____13966 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13967 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_app (uu____13968), uu____13969) -> begin
(

let head1 = (

let uu____13985 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13985 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____14025 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____14025 FStar_Pervasives_Native.fst))
in ((

let uu____14065 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____14065) with
| true -> begin
(

let uu____14066 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____14067 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____14068 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____14066 uu____14067 uu____14068))))
end
| uu____14069 -> begin
()
end));
(

let uu____14070 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____14070) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____14077 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____14077) with
| true -> begin
(

let uu____14078 = (

let uu____14085 = (

let uu____14086 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____14086 FStar_Syntax_Util.Equal))
in (match (uu____14085) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____14095 -> begin
(

let uu____14096 = (mk_eq2 wl orig t1 t2)
in (match (uu____14096) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____14078) with
| (guard, wl1) -> begin
(

let uu____14117 = (solve_prob orig guard [] wl1)
in (solve env uu____14117))
end))
end
| uu____14118 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____14119 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____14120, FStar_Syntax_Syntax.Tm_match (uu____14121)) -> begin
(

let head1 = (

let uu____14145 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____14145 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____14185 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____14185 FStar_Pervasives_Native.fst))
in ((

let uu____14225 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____14225) with
| true -> begin
(

let uu____14226 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____14227 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____14228 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____14226 uu____14227 uu____14228))))
end
| uu____14229 -> begin
()
end));
(

let uu____14230 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____14230) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____14237 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____14237) with
| true -> begin
(

let uu____14238 = (

let uu____14245 = (

let uu____14246 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____14246 FStar_Syntax_Util.Equal))
in (match (uu____14245) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____14255 -> begin
(

let uu____14256 = (mk_eq2 wl orig t1 t2)
in (match (uu____14256) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____14238) with
| (guard, wl1) -> begin
(

let uu____14277 = (solve_prob orig guard [] wl1)
in (solve env uu____14277))
end))
end
| uu____14278 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____14279 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____14280, FStar_Syntax_Syntax.Tm_uinst (uu____14281)) -> begin
(

let head1 = (

let uu____14289 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____14289 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____14329 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____14329 FStar_Pervasives_Native.fst))
in ((

let uu____14369 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____14369) with
| true -> begin
(

let uu____14370 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____14371 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____14372 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____14370 uu____14371 uu____14372))))
end
| uu____14373 -> begin
()
end));
(

let uu____14374 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____14374) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____14381 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____14381) with
| true -> begin
(

let uu____14382 = (

let uu____14389 = (

let uu____14390 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____14390 FStar_Syntax_Util.Equal))
in (match (uu____14389) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____14399 -> begin
(

let uu____14400 = (mk_eq2 wl orig t1 t2)
in (match (uu____14400) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____14382) with
| (guard, wl1) -> begin
(

let uu____14421 = (solve_prob orig guard [] wl1)
in (solve env uu____14421))
end))
end
| uu____14422 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____14423 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____14424, FStar_Syntax_Syntax.Tm_name (uu____14425)) -> begin
(

let head1 = (

let uu____14427 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____14427 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____14467 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____14467 FStar_Pervasives_Native.fst))
in ((

let uu____14507 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____14507) with
| true -> begin
(

let uu____14508 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____14509 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____14510 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____14508 uu____14509 uu____14510))))
end
| uu____14511 -> begin
()
end));
(

let uu____14512 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____14512) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____14519 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____14519) with
| true -> begin
(

let uu____14520 = (

let uu____14527 = (

let uu____14528 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____14528 FStar_Syntax_Util.Equal))
in (match (uu____14527) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____14537 -> begin
(

let uu____14538 = (mk_eq2 wl orig t1 t2)
in (match (uu____14538) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____14520) with
| (guard, wl1) -> begin
(

let uu____14559 = (solve_prob orig guard [] wl1)
in (solve env uu____14559))
end))
end
| uu____14560 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____14561 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____14562, FStar_Syntax_Syntax.Tm_constant (uu____14563)) -> begin
(

let head1 = (

let uu____14565 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____14565 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____14605 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____14605 FStar_Pervasives_Native.fst))
in ((

let uu____14645 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____14645) with
| true -> begin
(

let uu____14646 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____14647 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____14648 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____14646 uu____14647 uu____14648))))
end
| uu____14649 -> begin
()
end));
(

let uu____14650 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____14650) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____14657 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____14657) with
| true -> begin
(

let uu____14658 = (

let uu____14665 = (

let uu____14666 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____14666 FStar_Syntax_Util.Equal))
in (match (uu____14665) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____14675 -> begin
(

let uu____14676 = (mk_eq2 wl orig t1 t2)
in (match (uu____14676) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____14658) with
| (guard, wl1) -> begin
(

let uu____14697 = (solve_prob orig guard [] wl1)
in (solve env uu____14697))
end))
end
| uu____14698 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____14699 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____14700, FStar_Syntax_Syntax.Tm_fvar (uu____14701)) -> begin
(

let head1 = (

let uu____14703 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____14703 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____14743 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____14743 FStar_Pervasives_Native.fst))
in ((

let uu____14783 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____14783) with
| true -> begin
(

let uu____14784 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____14785 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____14786 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____14784 uu____14785 uu____14786))))
end
| uu____14787 -> begin
()
end));
(

let uu____14788 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____14788) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____14795 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____14795) with
| true -> begin
(

let uu____14796 = (

let uu____14803 = (

let uu____14804 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____14804 FStar_Syntax_Util.Equal))
in (match (uu____14803) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____14813 -> begin
(

let uu____14814 = (mk_eq2 wl orig t1 t2)
in (match (uu____14814) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____14796) with
| (guard, wl1) -> begin
(

let uu____14835 = (solve_prob orig guard [] wl1)
in (solve env uu____14835))
end))
end
| uu____14836 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____14837 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (uu____14838, FStar_Syntax_Syntax.Tm_app (uu____14839)) -> begin
(

let head1 = (

let uu____14855 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____14855 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____14895 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____14895 FStar_Pervasives_Native.fst))
in ((

let uu____14935 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____14935) with
| true -> begin
(

let uu____14936 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (

let uu____14937 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____14938 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print3 ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n" uu____14936 uu____14937 uu____14938))))
end
| uu____14939 -> begin
()
end));
(

let uu____14940 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ))
in (match (uu____14940) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____14947 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____14947) with
| true -> begin
(

let uu____14948 = (

let uu____14955 = (

let uu____14956 = (FStar_Syntax_Util.eq_tm t1 t2)
in (Prims.op_Equality uu____14956 FStar_Syntax_Util.Equal))
in (match (uu____14955) with
| true -> begin
((FStar_Pervasives_Native.None), (wl))
end
| uu____14965 -> begin
(

let uu____14966 = (mk_eq2 wl orig t1 t2)
in (match (uu____14966) with
| (g, wl1) -> begin
((FStar_Pervasives_Native.Some (g)), (wl1))
end))
end))
in (match (uu____14948) with
| (guard, wl1) -> begin
(

let uu____14987 = (solve_prob orig guard [] wl1)
in (solve env uu____14987))
end))
end
| uu____14988 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____14989 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end));
)))
end
| (FStar_Syntax_Syntax.Tm_let (uu____14990), FStar_Syntax_Syntax.Tm_let (uu____14991)) -> begin
(

let uu____15016 = (FStar_Syntax_Util.term_eq t1 t2)
in (match (uu____15016) with
| true -> begin
(

let uu____15017 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____15017))
end
| uu____15018 -> begin
(giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig)
end))
end
| (FStar_Syntax_Syntax.Tm_let (uu____15019), uu____15020) -> begin
(

let uu____15033 = (

let uu____15038 = (

let uu____15039 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____15040 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____15041 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____15042 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)" uu____15039 uu____15040 uu____15041 uu____15042)))))
in ((FStar_Errors.Fatal_UnificationNotWellFormed), (uu____15038)))
in (FStar_Errors.raise_error uu____15033 t1.FStar_Syntax_Syntax.pos))
end
| (uu____15043, FStar_Syntax_Syntax.Tm_let (uu____15044)) -> begin
(

let uu____15057 = (

let uu____15062 = (

let uu____15063 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____15064 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____15065 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____15066 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format4 "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)" uu____15063 uu____15064 uu____15065 uu____15066)))))
in ((FStar_Errors.Fatal_UnificationNotWellFormed), (uu____15062)))
in (FStar_Errors.raise_error uu____15057 t1.FStar_Syntax_Syntax.pos))
end
| uu____15067 -> begin
(giveup env "head tag mismatch" orig)
end));
)
end))))
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

let sub_prob = (fun wl1 t1 rel t2 reason -> (

let uu____15110 = (p_scope orig)
in (mk_t_problem wl1 uu____15110 orig t1 rel t2 FStar_Pervasives_Native.None reason)))
in (

let solve_eq = (fun c1_comp c2_comp -> ((

let uu____15123 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____15123) with
| true -> begin
(

let uu____15124 = (

let uu____15125 = (FStar_Syntax_Syntax.mk_Comp c1_comp)
in (FStar_Syntax_Print.comp_to_string uu____15125))
in (

let uu____15126 = (

let uu____15127 = (FStar_Syntax_Syntax.mk_Comp c2_comp)
in (FStar_Syntax_Print.comp_to_string uu____15127))
in (FStar_Util.print2 "solve_c is using an equality constraint (%s vs %s)\n" uu____15124 uu____15126)))
end
| uu____15128 -> begin
()
end));
(

let uu____15129 = (

let uu____15130 = (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)
in (not (uu____15130)))
in (match (uu____15129) with
| true -> begin
(

let uu____15131 = (

let uu____15132 = (FStar_Syntax_Print.lid_to_string c1_comp.FStar_Syntax_Syntax.effect_name)
in (

let uu____15133 = (FStar_Syntax_Print.lid_to_string c2_comp.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible effects: %s <> %s" uu____15132 uu____15133)))
in (giveup env uu____15131 orig))
end
| uu____15134 -> begin
(

let uu____15135 = (sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ FStar_TypeChecker_Common.EQ c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type")
in (match (uu____15135) with
| (ret_sub_prob, wl1) -> begin
(

let uu____15142 = (FStar_List.fold_right2 (fun uu____15175 uu____15176 uu____15177 -> (match (((uu____15175), (uu____15176), (uu____15177))) with
| ((a1, uu____15213), (a2, uu____15215), (arg_sub_probs, wl2)) -> begin
(

let uu____15236 = (sub_prob wl2 a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (match (uu____15236) with
| (p, wl3) -> begin
(((p)::arg_sub_probs), (wl3))
end))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args (([]), (wl1)))
in (match (uu____15142) with
| (arg_sub_probs, wl2) -> begin
(

let sub_probs = (ret_sub_prob)::arg_sub_probs
in (

let guard = (

let uu____15263 = (FStar_List.map p_guard sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____15263))
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

let lift_c1 = (fun uu____15289 -> (

let wp = (match (c11.FStar_Syntax_Syntax.effect_args) with
| ((wp1, uu____15292))::[] -> begin
wp1
end
| uu____15309 -> begin
(

let uu____15318 = (

let uu____15319 = (

let uu____15320 = (FStar_Ident.range_of_lid c11.FStar_Syntax_Syntax.effect_name)
in (FStar_Range.string_of_range uu____15320))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" uu____15319))
in (failwith uu____15318))
end)
in (

let univs1 = (match (c11.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
(

let uu____15322 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (uu____15322)::[])
end
| x -> begin
x
end)
in (

let uu____15324 = (

let uu____15333 = (

let uu____15340 = (

let uu____15341 = (FStar_List.hd univs1)
in (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp uu____15341 c11.FStar_Syntax_Syntax.result_typ wp))
in (FStar_Syntax_Syntax.as_arg uu____15340))
in (uu____15333)::[])
in {FStar_Syntax_Syntax.comp_univs = univs1; FStar_Syntax_Syntax.effect_name = c21.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c11.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____15324; FStar_Syntax_Syntax.flags = c11.FStar_Syntax_Syntax.flags}))))
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____15354 = (lift_c1 ())
in (solve_eq uu____15354 c21))
end
| uu____15355 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___109_15360 -> (match (uu___109_15360) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| uu____15361 -> begin
false
end))))
in (

let uu____15362 = (match (((c11.FStar_Syntax_Syntax.effect_args), (c21.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____15388))::uu____15389, ((wp2, uu____15391))::uu____15392) -> begin
((wp1), (wp2))
end
| uu____15449 -> begin
(

let uu____15470 = (

let uu____15475 = (

let uu____15476 = (FStar_Syntax_Print.lid_to_string c11.FStar_Syntax_Syntax.effect_name)
in (

let uu____15477 = (FStar_Syntax_Print.lid_to_string c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____15476 uu____15477)))
in ((FStar_Errors.Fatal_ExpectNormalizedEffect), (uu____15475)))
in (FStar_Errors.raise_error uu____15470 env.FStar_TypeChecker_Env.range))
end)
in (match (uu____15362) with
| (wpc1, wpc2) -> begin
(

let uu____15484 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____15484) with
| true -> begin
(

let uu____15485 = (problem_using_guard orig c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ FStar_Pervasives_Native.None "result type")
in (solve_t env uu____15485 wl))
end
| uu____15486 -> begin
(

let uu____15487 = (

let uu____15494 = (FStar_TypeChecker_Env.effect_decl_opt env c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.must uu____15494))
in (match (uu____15487) with
| (c2_decl, qualifiers) -> begin
(

let uu____15515 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____15515) with
| true -> begin
(

let c1_repr = (

let uu____15519 = (

let uu____15520 = (

let uu____15521 = (lift_c1 ())
in (FStar_Syntax_Syntax.mk_Comp uu____15521))
in (

let uu____15522 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____15520 uu____15522)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env uu____15519))
in (

let c2_repr = (

let uu____15524 = (

let uu____15525 = (FStar_Syntax_Syntax.mk_Comp c21)
in (

let uu____15526 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____15525 uu____15526)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::[]) env uu____15524))
in (

let uu____15527 = (

let uu____15532 = (

let uu____15533 = (FStar_Syntax_Print.term_to_string c1_repr)
in (

let uu____15534 = (FStar_Syntax_Print.term_to_string c2_repr)
in (FStar_Util.format2 "sub effect repr: %s <: %s" uu____15533 uu____15534)))
in (sub_prob wl c1_repr problem.FStar_TypeChecker_Common.relation c2_repr uu____15532))
in (match (uu____15527) with
| (prob, wl1) -> begin
(

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some ((p_guard prob))) [] wl1)
in (solve env (attempt ((prob)::[]) wl2)))
end))))
end
| uu____15538 -> begin
(

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____15540 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____15542 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____15542) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____15543 -> begin
()
end));
(

let c1_univ = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____15545 = (

let uu____15552 = (

let uu____15553 = (

let uu____15568 = (FStar_TypeChecker_Env.inst_effect_fun_with ((c1_univ)::[]) env c2_decl c2_decl.FStar_Syntax_Syntax.trivial)
in (

let uu____15571 = (

let uu____15580 = (FStar_Syntax_Syntax.as_arg c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____15581 = (

let uu____15584 = (

let uu____15585 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c1_univ c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____15585))
in (uu____15584)::[])
in (uu____15580)::uu____15581))
in ((uu____15568), (uu____15571))))
in FStar_Syntax_Syntax.Tm_app (uu____15553))
in (FStar_Syntax_Syntax.mk uu____15552))
in (uu____15545 FStar_Pervasives_Native.None r)));
)
end
| uu____15599 -> begin
(

let c1_univ = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (

let c2_univ = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____15602 = (

let uu____15609 = (

let uu____15610 = (

let uu____15625 = (FStar_TypeChecker_Env.inst_effect_fun_with ((c2_univ)::[]) env c2_decl c2_decl.FStar_Syntax_Syntax.stronger)
in (

let uu____15628 = (

let uu____15637 = (FStar_Syntax_Syntax.as_arg c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____15638 = (

let uu____15641 = (FStar_Syntax_Syntax.as_arg wpc2)
in (

let uu____15642 = (

let uu____15645 = (

let uu____15646 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c1_univ c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____15646))
in (uu____15645)::[])
in (uu____15641)::uu____15642))
in (uu____15637)::uu____15638))
in ((uu____15625), (uu____15628))))
in FStar_Syntax_Syntax.Tm_app (uu____15610))
in (FStar_Syntax_Syntax.mk uu____15609))
in (uu____15602 FStar_Pervasives_Native.None r))))
end)
end)
in (

let uu____15660 = (sub_prob wl c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ "result type")
in (match (uu____15660) with
| (base_prob, wl1) -> begin
(

let wl2 = (

let uu____15668 = (

let uu____15671 = (FStar_Syntax_Util.mk_conj (p_guard base_prob) g)
in (FStar_All.pipe_left (fun _0_30 -> FStar_Pervasives_Native.Some (_0_30)) uu____15671))
in (solve_prob orig uu____15668 [] wl1))
in (solve env (attempt ((base_prob)::[]) wl2)))
end)))
end))
end))
end))
end)))
end))))
in (

let uu____15674 = (FStar_Util.physical_equality c1 c2)
in (match (uu____15674) with
| true -> begin
(

let uu____15675 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____15675))
end
| uu____15676 -> begin
((

let uu____15678 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____15678) with
| true -> begin
(

let uu____15679 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____15680 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____15679 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____15680)))
end
| uu____15681 -> begin
()
end));
(

let uu____15682 = (

let uu____15691 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____15694 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____15691), (uu____15694))))
in (match (uu____15682) with
| (c11, c21) -> begin
(match (((c11.FStar_Syntax_Syntax.n), (c21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____15712), FStar_Syntax_Syntax.Total (t2, uu____15714)) when (FStar_Syntax_Util.non_informative t2) -> begin
(

let uu____15731 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____15731 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____15732), FStar_Syntax_Syntax.Total (uu____15733)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| (FStar_Syntax_Syntax.Total (t1, uu____15751), FStar_Syntax_Syntax.Total (t2, uu____15753)) -> begin
(

let uu____15770 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____15770 wl))
end
| (FStar_Syntax_Syntax.GTotal (t1, uu____15772), FStar_Syntax_Syntax.GTotal (t2, uu____15774)) -> begin
(

let uu____15791 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____15791 wl))
end
| (FStar_Syntax_Syntax.Total (t1, uu____15793), FStar_Syntax_Syntax.GTotal (t2, uu____15795)) -> begin
(

let uu____15812 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____15812 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____15813), FStar_Syntax_Syntax.Comp (uu____15814)) -> begin
(

let uu____15823 = (

let uu___156_15826 = problem
in (

let uu____15829 = (

let uu____15830 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____15830))
in {FStar_TypeChecker_Common.pid = uu___156_15826.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____15829; FStar_TypeChecker_Common.relation = uu___156_15826.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___156_15826.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___156_15826.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___156_15826.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___156_15826.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___156_15826.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___156_15826.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___156_15826.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___156_15826.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____15823 wl))
end
| (FStar_Syntax_Syntax.Total (uu____15831), FStar_Syntax_Syntax.Comp (uu____15832)) -> begin
(

let uu____15841 = (

let uu___156_15844 = problem
in (

let uu____15847 = (

let uu____15848 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____15848))
in {FStar_TypeChecker_Common.pid = uu___156_15844.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____15847; FStar_TypeChecker_Common.relation = uu___156_15844.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___156_15844.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___156_15844.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___156_15844.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___156_15844.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___156_15844.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___156_15844.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___156_15844.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___156_15844.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____15841 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____15849), FStar_Syntax_Syntax.GTotal (uu____15850)) -> begin
(

let uu____15859 = (

let uu___157_15862 = problem
in (

let uu____15865 = (

let uu____15866 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____15866))
in {FStar_TypeChecker_Common.pid = uu___157_15862.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___157_15862.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___157_15862.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____15865; FStar_TypeChecker_Common.element = uu___157_15862.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___157_15862.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___157_15862.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___157_15862.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___157_15862.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___157_15862.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___157_15862.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____15859 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____15867), FStar_Syntax_Syntax.Total (uu____15868)) -> begin
(

let uu____15877 = (

let uu___157_15880 = problem
in (

let uu____15883 = (

let uu____15884 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____15884))
in {FStar_TypeChecker_Common.pid = uu___157_15880.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___157_15880.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___157_15880.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____15883; FStar_TypeChecker_Common.element = uu___157_15880.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___157_15880.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.logical_guard_uvar = uu___157_15880.FStar_TypeChecker_Common.logical_guard_uvar; FStar_TypeChecker_Common.scope = uu___157_15880.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___157_15880.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___157_15880.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___157_15880.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____15877 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____15885), FStar_Syntax_Syntax.Comp (uu____15886)) -> begin
(

let uu____15887 = ((((FStar_Syntax_Util.is_ml_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) || ((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_total_comp c21))) || (((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) && (Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.SUB)))
in (match (uu____15887) with
| true -> begin
(

let uu____15888 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c11) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c21) FStar_Pervasives_Native.None "result type")
in (solve_t env uu____15888 wl))
end
| uu____15889 -> begin
(

let c1_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (

let c2_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (match ((Prims.op_Equality problem.FStar_TypeChecker_Common.relation FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____15892 = (

let uu____15897 = (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)
in (match (uu____15897) with
| true -> begin
((c1_comp), (c2_comp))
end
| uu____15902 -> begin
(

let uu____15903 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let uu____15904 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((uu____15903), (uu____15904))))
end))
in (match (uu____15892) with
| (c1_comp1, c2_comp1) -> begin
(solve_eq c1_comp1 c2_comp1)
end))
end
| uu____15907 -> begin
(

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((

let uu____15911 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____15911) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c12.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c22.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____15912 -> begin
()
end));
(

let uu____15913 = (FStar_TypeChecker_Env.monad_leq env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____15913) with
| FStar_Pervasives_Native.None -> begin
(

let uu____15916 = (

let uu____15917 = (FStar_Syntax_Print.lid_to_string c12.FStar_Syntax_Syntax.effect_name)
in (

let uu____15918 = (FStar_Syntax_Print.lid_to_string c22.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____15917 uu____15918)))
in (giveup env uu____15916 orig))
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

let uu____15925 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____15958 -> (match (uu____15958) with
| (uu____15969, tm, uu____15971, uu____15972, uu____15973) -> begin
(FStar_Syntax_Print.term_to_string tm)
end))))
in (FStar_All.pipe_right uu____15925 (FStar_String.concat ", "))))


let ineqs_to_string : (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.string = (fun ineqs -> (

let vars = (

let uu____16006 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs) (FStar_List.map FStar_Syntax_Print.univ_to_string))
in (FStar_All.pipe_right uu____16006 (FStar_String.concat ", ")))
in (

let ineqs1 = (

let uu____16024 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs) (FStar_List.map (fun uu____16052 -> (match (uu____16052) with
| (u1, u2) -> begin
(

let uu____16059 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____16060 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "%s < %s" uu____16059 uu____16060)))
end))))
in (FStar_All.pipe_right uu____16024 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred), (g.FStar_TypeChecker_Env.univ_ineqs))) with
| (FStar_TypeChecker_Common.Trivial, [], (uu____16087, [])) -> begin
"{}"
end
| uu____16112 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____16135 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____16135) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____16136 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____16138 = (FStar_List.map (fun uu____16148 -> (match (uu____16148) with
| (uu____16153, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right uu____16138 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (

let uu____16158 = (ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs)
in (FStar_Util.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n" form carry uu____16158 imps)))))
end))


let new_t_problem : worklist  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  (FStar_TypeChecker_Common.prob * worklist) = (fun wl env lhs rel rhs elt loc -> (

let reason = (

let uu____16203 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____16203) with
| true -> begin
(

let uu____16204 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____16205 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____16204 (rel_to_string rel) uu____16205)))
end
| uu____16206 -> begin
"TOP"
end))
in (

let uu____16207 = (new_problem wl env lhs rel rhs elt loc reason)
in (match (uu____16207) with
| (p, wl1) -> begin
((FStar_TypeChecker_Common.TProb (p)), (wl1))
end))))


let new_t_prob : worklist  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv * worklist) = (fun wl env t1 rel t2 -> (

let x = (

let uu____16256 = (

let uu____16259 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_31 -> FStar_Pervasives_Native.Some (_0_31)) uu____16259))
in (FStar_Syntax_Syntax.new_bv uu____16256 t1))
in (

let uu____16262 = (

let uu____16267 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some (x)) uu____16267))
in (match (uu____16262) with
| (p, wl1) -> begin
((p), (x), (wl1))
end))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits) FStar_Pervasives_Native.option)  ->  (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits) FStar_Pervasives_Native.option = (fun env probs err -> (

let probs1 = (

let uu____16323 = (FStar_Options.eager_inference ())
in (match (uu____16323) with
| true -> begin
(

let uu___158_16324 = probs
in {attempting = uu___158_16324.attempting; wl_deferred = uu___158_16324.wl_deferred; ctr = uu___158_16324.ctr; defer_ok = false; smt_ok = uu___158_16324.smt_ok; tcenv = uu___158_16324.tcenv; wl_implicits = uu___158_16324.wl_implicits})
end
| uu____16325 -> begin
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

let uu____16344 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____16344) with
| true -> begin
(

let uu____16345 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____16345))
end
| uu____16346 -> begin
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

let uu____16367 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____16367) with
| true -> begin
(

let uu____16368 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____16368))
end
| uu____16369 -> begin
()
end));
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env f)
in ((

let uu____16372 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____16372) with
| true -> begin
(

let uu____16373 = (FStar_Syntax_Print.term_to_string f1)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____16373))
end
| uu____16374 -> begin
()
end));
(

let f2 = (

let uu____16376 = (

let uu____16377 = (FStar_Syntax_Util.unmeta f1)
in uu____16377.FStar_Syntax_Syntax.n)
in (match (uu____16376) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____16381 -> begin
FStar_TypeChecker_Common.NonTrivial (f1)
end))
in (

let uu___159_16382 = g
in {FStar_TypeChecker_Env.guard_f = f2; FStar_TypeChecker_Env.deferred = uu___159_16382.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___159_16382.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___159_16382.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  (FStar_TypeChecker_Common.deferred * (Prims.string * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar * FStar_Range.range * Prims.bool) Prims.list) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (deferred, implicits) -> begin
(

let uu____16496 = (

let uu____16497 = (

let uu____16498 = (FStar_All.pipe_right (p_guard prob) (fun _0_32 -> FStar_TypeChecker_Common.NonTrivial (_0_32)))
in {FStar_TypeChecker_Env.guard_f = uu____16498; FStar_TypeChecker_Env.deferred = deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = implicits})
in (simplify_guard env uu____16497))
in (FStar_All.pipe_left (fun _0_33 -> FStar_Pervasives_Native.Some (_0_33)) uu____16496))
end))


let with_guard_no_simp : 'Auu____16513 . 'Auu____16513  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____16536 = (

let uu____16537 = (FStar_All.pipe_right (p_guard prob) (fun _0_34 -> FStar_TypeChecker_Common.NonTrivial (_0_34)))
in {FStar_TypeChecker_Env.guard_f = uu____16537; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in FStar_Pervasives_Native.Some (uu____16536))
end))


let try_teq : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun smt_ok env t1 t2 -> ((

let uu____16577 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____16577) with
| true -> begin
(

let uu____16578 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____16579 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" uu____16578 uu____16579)))
end
| uu____16580 -> begin
()
end));
(

let uu____16581 = (

let uu____16586 = (empty_worklist env)
in (

let uu____16587 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem uu____16586 env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None uu____16587)))
in (match (uu____16581) with
| (prob, wl) -> begin
(

let g = (

let uu____16595 = (solve_and_commit env (singleton wl prob smt_ok) (fun uu____16615 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob) uu____16595))
in g)
end));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____16659 = (try_teq true env t1 t2)
in (match (uu____16659) with
| FStar_Pervasives_Native.None -> begin
((

let uu____16663 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____16664 = (FStar_TypeChecker_Err.basic_type_error env FStar_Pervasives_Native.None t2 t1)
in (FStar_Errors.log_issue uu____16663 uu____16664)));
trivial_guard;
)
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____16671 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____16671) with
| true -> begin
(

let uu____16672 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____16673 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____16674 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____16672 uu____16673 uu____16674))))
end
| uu____16675 -> begin
()
end));
g;
)
end)))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  unit = (fun env e t1 t2 -> (

let uu____16696 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____16697 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t2 t1)
in (FStar_Errors.log_issue uu____16696 uu____16697))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env c1 c2 -> (

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____16720 -> begin
FStar_TypeChecker_Common.SUB
end)
in ((

let uu____16722 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____16722) with
| true -> begin
(

let uu____16723 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____16724 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n" uu____16723 uu____16724 (match ((Prims.op_Equality rel FStar_TypeChecker_Common.EQ)) with
| true -> begin
"EQ"
end
| uu____16725 -> begin
"SUB"
end))))
end
| uu____16726 -> begin
()
end));
(

let uu____16727 = (

let uu____16734 = (empty_worklist env)
in (

let uu____16735 = (FStar_TypeChecker_Env.get_range env)
in (new_problem uu____16734 env c1 rel c2 FStar_Pervasives_Native.None uu____16735 "sub_comp")))
in (match (uu____16727) with
| (prob, wl) -> begin
(

let prob1 = FStar_TypeChecker_Common.CProb (prob)
in (

let uu____16745 = (solve_and_commit env (singleton wl prob1 true) (fun uu____16765 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob1) uu____16745)))
end));
)))


let solve_universe_inequalities' : FStar_Syntax_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  unit = (fun tx env uu____16820 -> (match (uu____16820) with
| (variables, ineqs) -> begin
(

let fail1 = (fun u1 u2 -> ((FStar_Syntax_Unionfind.rollback tx);
(

let uu____16863 = (

let uu____16868 = (

let uu____16869 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____16870 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Universe %s and %s are incompatible" uu____16869 uu____16870)))
in ((FStar_Errors.Fatal_IncompatibleUniverse), (uu____16868)))
in (

let uu____16871 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____16863 uu____16871)));
))
in (

let equiv1 = (fun v1 v' -> (

let uu____16883 = (

let uu____16888 = (FStar_Syntax_Subst.compress_univ v1)
in (

let uu____16889 = (FStar_Syntax_Subst.compress_univ v')
in ((uu____16888), (uu____16889))))
in (match (uu____16883) with
| (FStar_Syntax_Syntax.U_unif (v0), FStar_Syntax_Syntax.U_unif (v0')) -> begin
(FStar_Syntax_Unionfind.univ_equiv v0 v0')
end
| uu____16908 -> begin
false
end)))
in (

let sols = (FStar_All.pipe_right variables (FStar_List.collect (fun v1 -> (

let uu____16938 = (FStar_Syntax_Subst.compress_univ v1)
in (match (uu____16938) with
| FStar_Syntax_Syntax.U_unif (uu____16945) -> begin
(

let lower_bounds_of_v = (FStar_All.pipe_right ineqs (FStar_List.collect (fun uu____16974 -> (match (uu____16974) with
| (u, v') -> begin
(

let uu____16983 = (equiv1 v1 v')
in (match (uu____16983) with
| true -> begin
(

let uu____16986 = (FStar_All.pipe_right variables (FStar_Util.for_some (equiv1 u)))
in (match (uu____16986) with
| true -> begin
[]
end
| uu____16991 -> begin
(u)::[]
end))
end
| uu____16992 -> begin
[]
end))
end))))
in (

let lb = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max (lower_bounds_of_v)))
in (((lb), (v1)))::[]))
end
| uu____17002 -> begin
[]
end)))))
in (

let uu____17007 = (

let wl = (

let uu___160_17011 = (empty_worklist env)
in {attempting = uu___160_17011.attempting; wl_deferred = uu___160_17011.wl_deferred; ctr = uu___160_17011.ctr; defer_ok = false; smt_ok = uu___160_17011.smt_ok; tcenv = uu___160_17011.tcenv; wl_implicits = uu___160_17011.wl_implicits})
in (FStar_All.pipe_right sols (FStar_List.map (fun uu____17029 -> (match (uu____17029) with
| (lb, v1) -> begin
(

let uu____17036 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl lb v1)
in (match (uu____17036) with
| USolved (wl1) -> begin
()
end
| uu____17038 -> begin
(fail1 lb v1)
end))
end)))))
in (

let rec check_ineq = (fun uu____17048 -> (match (uu____17048) with
| (u, v1) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u)
in (

let v2 = (FStar_TypeChecker_Normalize.normalize_universe env v1)
in (match (((u1), (v2))) with
| (FStar_Syntax_Syntax.U_zero, uu____17057) -> begin
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
| (FStar_Syntax_Syntax.U_name (uu____17080), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_unif (uu____17082), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_max (us), uu____17093) -> begin
(FStar_All.pipe_right us (FStar_Util.for_all (fun u2 -> (check_ineq ((u2), (v2))))))
end
| (uu____17100, FStar_Syntax_Syntax.U_max (vs)) -> begin
(FStar_All.pipe_right vs (FStar_Util.for_some (fun v3 -> (check_ineq ((u1), (v3))))))
end
| uu____17108 -> begin
false
end)))
end))
in (

let uu____17113 = (FStar_All.pipe_right ineqs (FStar_Util.for_all (fun uu____17128 -> (match (uu____17128) with
| (u, v1) -> begin
(

let uu____17135 = (check_ineq ((u), (v1)))
in (match (uu____17135) with
| true -> begin
true
end
| uu____17136 -> begin
((

let uu____17138 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____17138) with
| true -> begin
(

let uu____17139 = (FStar_Syntax_Print.univ_to_string u)
in (

let uu____17140 = (FStar_Syntax_Print.univ_to_string v1)
in (FStar_Util.print2 "%s </= %s" uu____17139 uu____17140)))
end
| uu____17141 -> begin
()
end));
false;
)
end))
end))))
in (match (uu____17113) with
| true -> begin
()
end
| uu____17142 -> begin
((

let uu____17144 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____17144) with
| true -> begin
((

let uu____17146 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Partially solved inequality constraints are: %s\n" uu____17146));
(FStar_Syntax_Unionfind.rollback tx);
(

let uu____17156 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Original solved inequality constraints are: %s\n" uu____17156));
)
end
| uu____17165 -> begin
()
end));
(

let uu____17166 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_FailToSolveUniverseInEquality), ("Failed to solve universe inequalities for inductives")) uu____17166));
)
end)))))))
end))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  unit = (fun env ineqs -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Syntax_Unionfind.commit tx);
)))


let try_solve_deferred_constraints : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun defer_ok env g -> (

let fail1 = (fun uu____17233 -> (match (uu____17233) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ErrorInSolveDeferredConstraints), (msg)) (p_loc d)))
end))
in (

let wl = (

let uu___161_17254 = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in {attempting = uu___161_17254.attempting; wl_deferred = uu___161_17254.wl_deferred; ctr = uu___161_17254.ctr; defer_ok = defer_ok; smt_ok = uu___161_17254.smt_ok; tcenv = uu___161_17254.tcenv; wl_implicits = uu___161_17254.wl_implicits})
in ((

let uu____17256 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____17256) with
| true -> begin
(

let uu____17257 = (wl_to_string wl)
in (

let uu____17258 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" uu____17257 uu____17258)))
end
| uu____17269 -> begin
()
end));
(

let g1 = (

let uu____17271 = (solve_and_commit env wl fail1)
in (match (uu____17271) with
| FStar_Pervasives_Native.Some ((uu____17278)::uu____17279, uu____17280) when (not (defer_ok)) -> begin
(failwith "Impossible: Unexpected deferred constraints remain")
end
| FStar_Pervasives_Native.Some (deferred, imps) -> begin
(

let uu___162_17305 = g
in {FStar_TypeChecker_Env.guard_f = uu___162_17305.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = deferred; FStar_TypeChecker_Env.univ_ineqs = uu___162_17305.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)})
end
| uu____17316 -> begin
(failwith "Impossible: should have raised a failure already")
end))
in ((solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___163_17324 = g1
in {FStar_TypeChecker_Env.guard_f = uu___163_17324.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___163_17324.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = uu___163_17324.FStar_TypeChecker_Env.implicits});
));
))))


let solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (try_solve_deferred_constraints false env g))


let solve_some_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (try_solve_deferred_constraints true env g))


let last_proof_ns : FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let maybe_update_proof_ns : FStar_TypeChecker_Env.env  ->  unit = (fun env -> (

let pns = env.FStar_TypeChecker_Env.proof_ns
in (

let uu____17372 = (FStar_ST.op_Bang last_proof_ns)
in (match (uu____17372) with
| FStar_Pervasives_Native.None -> begin
(FStar_ST.op_Colon_Equals last_proof_ns (FStar_Pervasives_Native.Some (pns)))
end
| FStar_Pervasives_Native.Some (old) -> begin
(match ((Prims.op_Equality old pns)) with
| true -> begin
()
end
| uu____17430 -> begin
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

let uu___164_17495 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___164_17495.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___164_17495.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___164_17495.FStar_TypeChecker_Env.implicits})
in (

let uu____17496 = (

let uu____17497 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____17497)))
in (match (uu____17496) with
| true -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| uu____17500 -> begin
(match (g1.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((match (debug1) with
| true -> begin
(

let uu____17505 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____17506 = (

let uu____17507 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____17507))
in (FStar_Errors.diag uu____17505 uu____17506)))
end
| uu____17508 -> begin
()
end);
(

let vc1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env vc)
in ((match (debug1) with
| true -> begin
(

let uu____17511 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____17512 = (

let uu____17513 = (FStar_Syntax_Print.term_to_string vc1)
in (FStar_Util.format1 "After normalization VC=\n%s\n" uu____17513))
in (FStar_Errors.diag uu____17511 uu____17512)))
end
| uu____17514 -> begin
()
end);
(

let uu____17516 = (FStar_TypeChecker_Env.get_range env)
in (def_check_closed_in_env uu____17516 "discharge_guard\'" env vc1));
(

let uu____17517 = (check_trivial vc1)
in (match (uu____17517) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc2) -> begin
(match ((not (use_smt))) with
| true -> begin
((match (debug1) with
| true -> begin
(

let uu____17524 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____17525 = (

let uu____17526 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Cannot solve without SMT : %s\n" uu____17526))
in (FStar_Errors.diag uu____17524 uu____17525)))
end
| uu____17527 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end
| uu____17528 -> begin
((match (debug1) with
| true -> begin
(

let uu____17531 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____17532 = (

let uu____17533 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____17533))
in (FStar_Errors.diag uu____17531 uu____17532)))
end
| uu____17534 -> begin
()
end);
(

let vcs = (

let uu____17544 = (FStar_Options.use_tactics ())
in (match (uu____17544) with
| true -> begin
(FStar_Options.with_saved_options (fun uu____17563 -> ((

let uu____17565 = (FStar_Options.set_options FStar_Options.Set "--no_tactics")
in (FStar_All.pipe_left (fun a238 -> ()) uu____17565));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.preprocess env vc2);
)))
end
| uu____17566 -> begin
(

let uu____17567 = (

let uu____17574 = (FStar_Options.peek ())
in ((env), (vc2), (uu____17574)))
in (uu____17567)::[])
end))
in (FStar_All.pipe_right vcs (FStar_List.iter (fun uu____17608 -> (match (uu____17608) with
| (env1, goal, opts) -> begin
(

let goal1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env1 goal)
in (

let uu____17619 = (check_trivial goal1)
in (match (uu____17619) with
| FStar_TypeChecker_Common.Trivial -> begin
(match (debug1) with
| true -> begin
(FStar_Util.print_string "Goal completely solved by tactic\n")
end
| uu____17621 -> begin
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

let uu____17627 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____17628 = (

let uu____17629 = (FStar_Syntax_Print.term_to_string goal2)
in (

let uu____17630 = (FStar_TypeChecker_Env.string_of_proof_ns env1)
in (FStar_Util.format2 "Trying to solve:\n> %s\nWith proof_ns:\n %s\n" uu____17629 uu____17630)))
in (FStar_Errors.diag uu____17627 uu____17628)))
end
| uu____17631 -> begin
()
end);
(match (debug1) with
| true -> begin
(

let uu____17633 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____17634 = (

let uu____17635 = (FStar_Syntax_Print.term_to_string goal2)
in (FStar_Util.format1 "Before calling solver VC=\n%s\n" uu____17635))
in (FStar_Errors.diag uu____17633 uu____17634)))
end
| uu____17636 -> begin
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

let uu____17649 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____17649) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____17656 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ExpectTrivialPreCondition), ("Expected a trivial pre-condition")) uu____17656))
end)))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let uu____17667 = (discharge_guard' FStar_Pervasives_Native.None env g true)
in (match (uu____17667) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end)))


let resolve_implicits' : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env must_total forcelax g -> (

let unresolved = (fun u -> (

let uu____17700 = (FStar_Syntax_Util.head_and_args u)
in (match (uu____17700) with
| (hd1, uu____17716) -> begin
(

let uu____17737 = (

let uu____17738 = (FStar_Syntax_Subst.compress u)
in uu____17738.FStar_Syntax_Syntax.n)
in (match (uu____17737) with
| FStar_Syntax_Syntax.Tm_uvar (uu____17741) -> begin
true
end
| uu____17742 -> begin
false
end))
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____17762 = acc
in (match (uu____17762) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____17779 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd1)::tl1 -> begin
(

let uu____17824 = hd1
in (match (uu____17824) with
| (reason, tm, ctx_u, r, should_check) -> begin
(match ((not (should_check))) with
| true -> begin
(until_fixpoint ((out), (true)) tl1)
end
| uu____17840 -> begin
(

let uu____17841 = (unresolved tm)
in (match (uu____17841) with
| true -> begin
(until_fixpoint (((hd1)::out), (changed)) tl1)
end
| uu____17852 -> begin
(

let env1 = (

let uu___165_17854 = env
in {FStar_TypeChecker_Env.solver = uu___165_17854.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___165_17854.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___165_17854.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_TypeChecker_Env.gamma_sig = uu___165_17854.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___165_17854.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___165_17854.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___165_17854.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___165_17854.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___165_17854.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___165_17854.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___165_17854.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___165_17854.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___165_17854.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___165_17854.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___165_17854.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___165_17854.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___165_17854.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___165_17854.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___165_17854.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___165_17854.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___165_17854.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___165_17854.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___165_17854.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___165_17854.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___165_17854.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___165_17854.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___165_17854.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___165_17854.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___165_17854.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___165_17854.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___165_17854.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___165_17854.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___165_17854.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___165_17854.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___165_17854.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___165_17854.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___165_17854.FStar_TypeChecker_Env.dep_graph})
in (

let tm1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 tm)
in (

let env2 = (match (forcelax) with
| true -> begin
(

let uu___166_17857 = env1
in {FStar_TypeChecker_Env.solver = uu___166_17857.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___166_17857.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___166_17857.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___166_17857.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___166_17857.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___166_17857.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___166_17857.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___166_17857.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___166_17857.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___166_17857.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___166_17857.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___166_17857.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___166_17857.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___166_17857.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___166_17857.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___166_17857.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___166_17857.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___166_17857.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___166_17857.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___166_17857.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___166_17857.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___166_17857.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___166_17857.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___166_17857.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___166_17857.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___166_17857.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___166_17857.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___166_17857.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___166_17857.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___166_17857.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___166_17857.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___166_17857.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___166_17857.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___166_17857.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___166_17857.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___166_17857.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___166_17857.FStar_TypeChecker_Env.dep_graph})
end
| uu____17858 -> begin
env1
end)
in ((

let uu____17860 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("RelCheck")))
in (match (uu____17860) with
| true -> begin
(

let uu____17861 = (FStar_Syntax_Print.uvar_to_string ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____17862 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____17863 = (FStar_Syntax_Print.term_to_string ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (

let uu____17864 = (FStar_Range.string_of_range r)
in (FStar_Util.print5 "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n" uu____17861 uu____17862 uu____17863 reason uu____17864)))))
end
| uu____17865 -> begin
()
end));
(

let g1 = (FStar_All.try_with (fun uu___168_17868 -> (match (()) with
| () -> begin
(env2.FStar_TypeChecker_Env.check_type_of must_total env2 tm1 ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
end)) (fun uu___167_17872 -> (match (uu___167_17872) with
| e -> begin
((

let uu____17875 = (

let uu____17884 = (

let uu____17891 = (

let uu____17892 = (FStar_Syntax_Print.uvar_to_string ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____17893 = (FStar_TypeChecker_Normalize.term_to_string env2 tm1)
in (FStar_Util.format2 "Failed while checking implicit %s set to %s" uu____17892 uu____17893)))
in ((FStar_Errors.Error_BadImplicit), (uu____17891), (r)))
in (uu____17884)::[])
in (FStar_Errors.add_errors uu____17875));
(FStar_Exn.raise e);
)
end)))
in (

let g2 = (match (env2.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___169_17907 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___169_17907.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___169_17907.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___169_17907.FStar_TypeChecker_Env.implicits})
end
| uu____17908 -> begin
g1
end)
in (

let g' = (

let uu____17910 = (discharge_guard' (FStar_Pervasives_Native.Some ((fun uu____17917 -> (FStar_Syntax_Print.term_to_string tm1)))) env2 g2 true)
in (match (uu____17910) with
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

let uu___170_17929 = g
in (

let uu____17930 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___170_17929.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___170_17929.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___170_17929.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____17930})))))


let resolve_implicits : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (resolve_implicits' env true false g))


let resolve_implicits_tac : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (resolve_implicits' env false true g))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  unit = (fun env g -> (

let g1 = (

let uu____17984 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____17984 (resolve_implicits env)))
in (match (g1.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(

let uu____17995 = (discharge_guard env g1)
in (FStar_All.pipe_left (fun a239 -> ()) uu____17995))
end
| ((reason, e, ctx_u, r, should_check))::uu____18001 -> begin
(

let uu____18024 = (

let uu____18029 = (

let uu____18030 = (FStar_Syntax_Print.uvar_to_string ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____18031 = (FStar_Syntax_Print.term_to_string ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
in (

let uu____18032 = (FStar_Util.string_of_bool should_check)
in (FStar_Util.format4 "Failed to resolve implicit argument %s of type %s introduced for %s (should check=%s)" uu____18030 uu____18031 reason uu____18032))))
in ((FStar_Errors.Fatal_FailToResolveImplicitArgument), (uu____18029)))
in (FStar_Errors.raise_error uu____18024 r))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___171_18043 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___171_18043.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___171_18043.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ((((u1), (u2)))::[])); FStar_TypeChecker_Env.implicits = uu___171_18043.FStar_TypeChecker_Env.implicits}))


let discharge_guard_nosmt : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun env g -> (

let uu____18066 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____18066) with
| FStar_Pervasives_Native.Some (uu____18072) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end)))


let teq_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____18088 = (try_teq false env t1 t2)
in (match (uu____18088) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g) -> begin
(discharge_guard_nosmt env g)
end)))


let check_subtyping : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.option = (fun env t1 t2 -> ((

let uu____18114 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____18114) with
| true -> begin
(

let uu____18115 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____18116 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "check_subtyping of %s and %s\n" uu____18115 uu____18116)))
end
| uu____18117 -> begin
()
end));
(

let uu____18118 = (

let uu____18125 = (empty_worklist env)
in (new_t_prob uu____18125 env t1 FStar_TypeChecker_Common.SUB t2))
in (match (uu____18118) with
| (prob, x, wl) -> begin
(

let g = (

let uu____18138 = (solve_and_commit env (singleton wl prob true) (fun uu____18158 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob) uu____18138))
in ((

let uu____18188 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____18188) with
| true -> begin
(

let uu____18189 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____18190 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____18191 = (

let uu____18192 = (FStar_Util.must g)
in (guard_to_string env uu____18192))
in (FStar_Util.print3 "check_subtyping succeeded: %s <: %s\n\tguard is %s\n" uu____18189 uu____18190 uu____18191))))
end
| uu____18193 -> begin
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

let uu____18226 = (check_subtyping env t1 t2)
in (match (uu____18226) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (x, g) -> begin
(

let uu____18245 = (

let uu____18246 = (FStar_Syntax_Syntax.mk_binder x)
in (abstract_guard uu____18246 g))
in FStar_Pervasives_Native.Some (uu____18245))
end)))


let get_subtyping_prop : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> (

let uu____18264 = (check_subtyping env t1 t2)
in (match (uu____18264) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (x, g) -> begin
(

let uu____18283 = (

let uu____18284 = (

let uu____18285 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____18285)::[])
in (close_guard env uu____18284 g))
in FStar_Pervasives_Native.Some (uu____18283))
end)))


let subtype_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> ((

let uu____18314 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____18314) with
| true -> begin
(

let uu____18315 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____18316 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____18315 uu____18316)))
end
| uu____18317 -> begin
()
end));
(

let uu____18318 = (

let uu____18325 = (empty_worklist env)
in (new_t_prob uu____18325 env t1 FStar_TypeChecker_Common.SUB t2))
in (match (uu____18318) with
| (prob, x, wl) -> begin
(

let g = (

let uu____18332 = (solve_and_commit env (singleton wl prob false) (fun uu____18352 -> FStar_Pervasives_Native.None))
in (FStar_All.pipe_left (with_guard env prob) uu____18332))
in (match (g) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g1) -> begin
(

let g2 = (

let uu____18383 = (

let uu____18384 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____18384)::[])
in (close_guard env uu____18383 g1))
in (discharge_guard_nosmt env g2))
end))
end));
))





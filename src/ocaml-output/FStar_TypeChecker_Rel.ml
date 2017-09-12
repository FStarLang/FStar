
open Prims
open FStar_Pervasives

let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu____33; FStar_TypeChecker_Env.implicits = uu____34} -> begin
true
end
| uu____61 -> begin
false
end))


let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []}


let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun x g -> (match (g) with
| FStar_Pervasives_Native.None -> begin
g
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu____98; FStar_TypeChecker_Env.univ_ineqs = uu____99; FStar_TypeChecker_Env.implicits = uu____100}) -> begin
g
end
| FStar_Pervasives_Native.Some (g1) -> begin
(

let f = (match (g1.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| uu____126 -> begin
(failwith "impossible")
end)
in (

let uu____127 = (

let uu___139_128 = g1
in (

let uu____129 = (

let uu____130 = (

let uu____131 = (

let uu____132 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____132)::[])
in (FStar_Syntax_Util.abs uu____131 f (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0)))))
in (FStar_All.pipe_left (fun _0_41 -> FStar_TypeChecker_Common.NonTrivial (_0_41)) uu____130))
in {FStar_TypeChecker_Env.guard_f = uu____129; FStar_TypeChecker_Env.deferred = uu___139_128.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___139_128.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___139_128.FStar_TypeChecker_Env.implicits}))
in FStar_Pervasives_Native.Some (uu____127)))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___140_142 = g
in (

let uu____143 = (

let uu____144 = (

let uu____145 = (

let uu____148 = (

let uu____149 = (

let uu____164 = (

let uu____167 = (FStar_Syntax_Syntax.as_arg e)
in (uu____167)::[])
in ((f), (uu____164)))
in FStar_Syntax_Syntax.Tm_app (uu____149))
in (FStar_Syntax_Syntax.mk uu____148))
in (uu____145 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _0_42 -> FStar_TypeChecker_Common.NonTrivial (_0_42)) uu____144))
in {FStar_TypeChecker_Env.guard_f = uu____143; FStar_TypeChecker_Env.deferred = uu___140_142.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___140_142.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___140_142.FStar_TypeChecker_Env.implicits}))
end))


let map_guard : FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  FStar_TypeChecker_Env.guard_t = (fun g map1 -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___141_187 = g
in (

let uu____188 = (

let uu____189 = (map1 f)
in FStar_TypeChecker_Common.NonTrivial (uu____189))
in {FStar_TypeChecker_Env.guard_f = uu____188; FStar_TypeChecker_Env.deferred = uu___141_187.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___141_187.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___141_187.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____194) -> begin
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

let uu____207 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (uu____207))
end))


let check_trivial : FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (

let uu____212 = (

let uu____213 = (FStar_Syntax_Util.unmeta t)
in uu____213.FStar_Syntax_Syntax.n)
in (match (uu____212) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____217 -> begin
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

let uu____253 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = uu____253; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (((FStar_List.append (FStar_Pervasives_Native.fst g1.FStar_TypeChecker_Env.univ_ineqs) (FStar_Pervasives_Native.fst g2.FStar_TypeChecker_Env.univ_ineqs))), ((FStar_List.append (FStar_Pervasives_Native.snd g1.FStar_TypeChecker_Env.univ_ineqs) (FStar_Pervasives_Native.snd g2.FStar_TypeChecker_Env.univ_ineqs)))); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard_univs : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun us bs g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let f1 = (FStar_List.fold_right2 (fun u b f1 -> (

let uu____327 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____327) with
| true -> begin
f1
end
| uu____328 -> begin
(FStar_Syntax_Util.mk_forall u (FStar_Pervasives_Native.fst b) f1)
end))) us bs f)
in (

let uu___142_329 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.NonTrivial (f1); FStar_TypeChecker_Env.deferred = uu___142_329.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___142_329.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___142_329.FStar_TypeChecker_Env.implicits}))
end))


let close_forall : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____351 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____351) with
| true -> begin
f1
end
| uu____352 -> begin
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

let uu___143_367 = g
in (

let uu____368 = (

let uu____369 = (close_forall env binders f)
in FStar_TypeChecker_Common.NonTrivial (uu____369))
in {FStar_TypeChecker_Env.guard_f = uu____368; FStar_TypeChecker_Env.deferred = uu___143_367.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___143_367.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___143_367.FStar_TypeChecker_Env.implicits}))
end))


let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (

let uv = (FStar_Syntax_Unionfind.fresh ())
in (match (binders) with
| [] -> begin
(

let uv1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k)))) FStar_Pervasives_Native.None r)
in ((uv1), (uv1)))
end
| uu____402 -> begin
(

let args = (FStar_All.pipe_right binders (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder))
in (

let k' = (

let uu____427 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders uu____427))
in (

let uv1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k')))) FStar_Pervasives_Native.None r)
in (

let uu____435 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((uv1), (args)))) FStar_Pervasives_Native.None r)
in ((uu____435), (uv1))))))
end)))


let mk_eq2 : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t1 t2 -> (

let uu____466 = (FStar_Syntax_Util.type_u ())
in (match (uu____466) with
| (t_type, u) -> begin
(

let uu____473 = (

let uu____478 = (FStar_TypeChecker_Env.all_binders env)
in (new_uvar t1.FStar_Syntax_Syntax.pos uu____478 t_type))
in (match (uu____473) with
| (tt, uu____480) -> begin
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
| uu____514 -> begin
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
| uu____556 -> begin
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
| uu____750 -> begin
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
| uu____768 -> begin
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
| uu____793 -> begin
false
end))


let uu___is_CONTRAVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CONTRAVARIANT -> begin
true
end
| uu____798 -> begin
false
end))


let uu___is_INVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| INVARIANT -> begin
true
end
| uu____803 -> begin
false
end))


type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem


type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem


type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun uu___111_827 -> (match (uu___111_827) with
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

let uu____834 = (

let uu____835 = (FStar_Syntax_Subst.compress t)
in uu____835.FStar_Syntax_Syntax.n)
in (match (uu____834) with
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let uu____864 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____865 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "%s : %s" uu____864 uu____865)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty); FStar_Syntax_Syntax.pos = uu____868; FStar_Syntax_Syntax.vars = uu____869}, args) -> begin
(

let uu____915 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____916 = (FStar_Syntax_Print.term_to_string ty)
in (

let uu____917 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "(%s : %s) %s" uu____915 uu____916 uu____917))))
end
| uu____918 -> begin
"--"
end))
in (

let uu____919 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format3 "%s (%s)\t%s" compact uu____919 detail)))))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env uu___112_927 -> (match (uu___112_927) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____933 = (

let uu____936 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____937 = (

let uu____940 = (term_to_string p.FStar_TypeChecker_Common.lhs)
in (

let uu____941 = (

let uu____944 = (

let uu____947 = (term_to_string p.FStar_TypeChecker_Common.rhs)
in (uu____947)::[])
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::uu____944)
in (uu____940)::uu____941))
in (uu____936)::uu____937))
in (FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____933))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____953 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____954 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\n\t%s \n\t\t%s\n\t%s" uu____953 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____954)))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env uu___113_962 -> (match (uu___113_962) with
| UNIV (u, t) -> begin
(

let x = (

let uu____966 = (FStar_Options.hide_uvar_nums ())
in (match (uu____966) with
| true -> begin
"?"
end
| uu____967 -> begin
(

let uu____968 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____968 FStar_Util.string_of_int))
end))
in (

let uu____969 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x uu____969)))
end
| TERM ((u, uu____971), t) -> begin
(

let x = (

let uu____978 = (FStar_Options.hide_uvar_nums ())
in (match (uu____978) with
| true -> begin
"?"
end
| uu____979 -> begin
(

let uu____980 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____980 FStar_Util.string_of_int))
end))
in (

let uu____981 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x uu____981)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (

let uu____994 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right uu____994 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (

let uu____1007 = (

let uu____1010 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right uu____1010 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right uu____1007 (FStar_String.concat ", "))))


let args_to_string : 'Auu____1023 . (FStar_Syntax_Syntax.term * 'Auu____1023) Prims.list  ->  Prims.string = (fun args -> (

let uu____1040 = (FStar_All.pipe_right args (FStar_List.map (fun uu____1058 -> (match (uu____1058) with
| (x, uu____1064) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____1040 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> (

let uu____1071 = (

let uu____1072 = (FStar_Options.eager_inference ())
in (not (uu____1072)))
in {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = uu____1071; smt_ok = true; tcenv = env}))


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let uu___144_1091 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = uu___144_1091.wl_deferred; ctr = uu___144_1091.ctr; defer_ok = uu___144_1091.defer_ok; smt_ok = smt_ok; tcenv = uu___144_1091.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard : 'Auu____1106 . FStar_TypeChecker_Env.env  ->  ('Auu____1106 * FStar_TypeChecker_Common.prob) Prims.list  ->  worklist = (fun env g -> (

let uu___145_1127 = (empty_worklist env)
in (

let uu____1128 = (FStar_List.map FStar_Pervasives_Native.snd g)
in {attempting = uu____1128; wl_deferred = uu___145_1127.wl_deferred; ctr = uu___145_1127.ctr; defer_ok = false; smt_ok = uu___145_1127.smt_ok; tcenv = uu___145_1127.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu___146_1145 = wl
in {attempting = uu___146_1145.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = uu___146_1145.ctr; defer_ok = uu___146_1145.defer_ok; smt_ok = uu___146_1145.smt_ok; tcenv = uu___146_1145.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let uu___147_1164 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = uu___147_1164.wl_deferred; ctr = uu___147_1164.ctr; defer_ok = uu___147_1164.defer_ok; smt_ok = uu___147_1164.smt_ok; tcenv = uu___147_1164.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> ((

let uu____1178 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____1178) with
| true -> begin
(

let uu____1179 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1179))
end
| uu____1180 -> begin
()
end));
Failed (((prob), (reason)));
))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun uu___114_1184 -> (match (uu___114_1184) with
| FStar_TypeChecker_Common.EQ -> begin
FStar_TypeChecker_Common.EQ
end
| FStar_TypeChecker_Common.SUB -> begin
FStar_TypeChecker_Common.SUBINV
end
| FStar_TypeChecker_Common.SUBINV -> begin
FStar_TypeChecker_Common.SUB
end))


let invert : 'Auu____1191 'Auu____1192 . ('Auu____1192, 'Auu____1191) FStar_TypeChecker_Common.problem  ->  ('Auu____1192, 'Auu____1191) FStar_TypeChecker_Common.problem = (fun p -> (

let uu___148_1209 = p
in {FStar_TypeChecker_Common.pid = uu___148_1209.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = uu___148_1209.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___148_1209.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___148_1209.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___148_1209.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___148_1209.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___148_1209.FStar_TypeChecker_Common.rank}))


let maybe_invert : 'Auu____1220 'Auu____1221 . ('Auu____1221, 'Auu____1220) FStar_TypeChecker_Common.problem  ->  ('Auu____1221, 'Auu____1220) FStar_TypeChecker_Common.problem = (fun p -> (match ((p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV)) with
| true -> begin
(invert p)
end
| uu____1238 -> begin
p
end))


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___115_1242 -> (match (uu___115_1242) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_43 -> FStar_TypeChecker_Common.TProb (_0_43)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_44 -> FStar_TypeChecker_Common.CProb (_0_44)))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel uu___116_1268 -> (match (uu___116_1268) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun uu___117_1272 -> (match (uu___117_1272) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun uu___118_1286 -> (match (uu___118_1286) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun uu___119_1302 -> (match (uu___119_1302) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun uu___120_1318 -> (match (uu___120_1318) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun uu___121_1336 -> (match (uu___121_1336) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun uu___122_1354 -> (match (uu___122_1354) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___123_1368 -> (match (uu___123_1368) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _0_45 -> FStar_TypeChecker_Common.TProb (_0_45)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _0_46 -> FStar_TypeChecker_Common.CProb (_0_46)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> (

let uu____1391 = (FStar_All.pipe_right (p_reason p) FStar_List.length)
in (uu____1391 = (Prims.parse_int "1"))))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____1404 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
)))


let mk_problem : 'Auu____1469 'Auu____1470 . FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  'Auu____1470  ->  FStar_TypeChecker_Common.rel  ->  'Auu____1470  ->  'Auu____1469 FStar_Pervasives_Native.option  ->  Prims.string  ->  ('Auu____1470, 'Auu____1469) FStar_TypeChecker_Common.problem = (fun scope orig lhs rel rhs elt reason -> (

let uu____1507 = (next_pid ())
in (

let uu____1508 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____1507; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____1508; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})))


let new_problem : 'Auu____1531 'Auu____1532 . FStar_TypeChecker_Env.env  ->  'Auu____1532  ->  FStar_TypeChecker_Common.rel  ->  'Auu____1532  ->  'Auu____1531 FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  Prims.string  ->  ('Auu____1532, 'Auu____1531) FStar_TypeChecker_Common.problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (

let uu____1570 = (next_pid ())
in (

let uu____1571 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____1570; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____1571; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None}))))


let problem_using_guard : 'Auu____1592 'Auu____1593 . FStar_TypeChecker_Common.prob  ->  'Auu____1593  ->  FStar_TypeChecker_Common.rel  ->  'Auu____1593  ->  'Auu____1592 FStar_Pervasives_Native.option  ->  Prims.string  ->  ('Auu____1593, 'Auu____1592) FStar_TypeChecker_Common.problem = (fun orig lhs rel rhs elt reason -> (

let uu____1626 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____1626; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None}))


let guard_on_element : 'Auu____1637 . worklist  ->  ('Auu____1637, FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_TypeChecker_Common.problem  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun wl problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| FStar_Pervasives_Native.None -> begin
(

let u = (wl.tcenv.FStar_TypeChecker_Env.universe_of wl.tcenv x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Util.mk_forall u x phi))
end
| FStar_Pervasives_Native.Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (

let uu____1690 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____1690) with
| true -> begin
(

let uu____1691 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (

let uu____1692 = (prob_to_string env d)
in (

let uu____1693 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" uu____1691 uu____1692 uu____1693 s))))
end
| uu____1696 -> begin
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
| uu____1699 -> begin
(failwith "impossible")
end)
in (

let uu____1700 = (match (d1) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____1714 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (

let uu____1715 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((uu____1714), (uu____1715))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____1721 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (

let uu____1722 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((uu____1721), (uu____1722))))
end)
in (match (uu____1700) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___124_1739 -> (match (uu___124_1739) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Syntax_Unionfind.univ_union u u')
end
| uu____1751 -> begin
(FStar_Syntax_Unionfind.univ_change u t)
end)
end
| TERM ((u, uu____1753), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : FStar_Syntax_Syntax.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun uv s -> (FStar_Util.find_map s (fun uu___125_1775 -> (match (uu___125_1775) with
| UNIV (uu____1778) -> begin
FStar_Pervasives_Native.None
end
| TERM ((u, uu____1784), t) -> begin
(

let uu____1790 = (FStar_Syntax_Unionfind.equiv uv u)
in (match (uu____1790) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____1793 -> begin
FStar_Pervasives_Native.None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe_uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun u s -> (FStar_Util.find_map s (fun uu___126_1812 -> (match (uu___126_1812) with
| UNIV (u', t) -> begin
(

let uu____1817 = (FStar_Syntax_Unionfind.univ_equiv u u')
in (match (uu____1817) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____1820 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____1821 -> begin
FStar_Pervasives_Native.None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1830 = (

let uu____1831 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____1831))
in (FStar_Syntax_Subst.compress uu____1830)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1840 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress uu____1840)))


let norm_arg : 'Auu____1847 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * 'Auu____1847)  ->  (FStar_Syntax_Syntax.term * 'Auu____1847) = (fun env t -> (

let uu____1868 = (sn env (FStar_Pervasives_Native.fst t))
in ((uu____1868), ((FStar_Pervasives_Native.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____1901 -> (match (uu____1901) with
| (x, imp) -> begin
(

let uu____1912 = (

let uu___149_1913 = x
in (

let uu____1914 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___149_1913.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___149_1913.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1914}))
in ((uu____1912), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____1931 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____1931))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1935 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____1935))
end
| uu____1938 -> begin
u2
end)))
in (

let uu____1939 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1939))))


let normalize_refinement : 'Auu____1950 . FStar_TypeChecker_Normalize.steps  ->  FStar_TypeChecker_Env.env  ->  'Auu____1950  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement : 'Auu____1975 . FStar_TypeChecker_Env.env  ->  'Auu____1975  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option) = (fun env wl t1 -> (

let rec aux = (fun norm1 t11 -> (match (t11.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(match (norm1) with
| true -> begin
((x.FStar_Syntax_Syntax.sort), (FStar_Pervasives_Native.Some (((x), (phi)))))
end
| uu____2079 -> begin
(

let uu____2080 = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (match (uu____2080) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x1, phi1); FStar_Syntax_Syntax.pos = uu____2097; FStar_Syntax_Syntax.vars = uu____2098} -> begin
((x1.FStar_Syntax_Syntax.sort), (FStar_Pervasives_Native.Some (((x1), (phi1)))))
end
| tt -> begin
(

let uu____2124 = (

let uu____2125 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____2126 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" uu____2125 uu____2126)))
in (failwith uu____2124))
end))
end)
end
| FStar_Syntax_Syntax.Tm_uinst (uu____2141) -> begin
(match (norm1) with
| true -> begin
((t11), (FStar_Pervasives_Native.None))
end
| uu____2178 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (

let uu____2180 = (

let uu____2181 = (FStar_Syntax_Subst.compress t1')
in uu____2181.FStar_Syntax_Syntax.n)
in (match (uu____2180) with
| FStar_Syntax_Syntax.Tm_refine (uu____2198) -> begin
(aux true t1')
end
| uu____2205 -> begin
((t11), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2222) -> begin
(match (norm1) with
| true -> begin
((t11), (FStar_Pervasives_Native.None))
end
| uu____2253 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (

let uu____2255 = (

let uu____2256 = (FStar_Syntax_Subst.compress t1')
in uu____2256.FStar_Syntax_Syntax.n)
in (match (uu____2255) with
| FStar_Syntax_Syntax.Tm_refine (uu____2273) -> begin
(aux true t1')
end
| uu____2280 -> begin
((t11), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_app (uu____2297) -> begin
(match (norm1) with
| true -> begin
((t11), (FStar_Pervasives_Native.None))
end
| uu____2342 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (

let uu____2344 = (

let uu____2345 = (FStar_Syntax_Subst.compress t1')
in uu____2345.FStar_Syntax_Syntax.n)
in (match (uu____2344) with
| FStar_Syntax_Syntax.Tm_refine (uu____2362) -> begin
(aux true t1')
end
| uu____2369 -> begin
((t11), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_type (uu____2386) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_constant (uu____2403) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_name (uu____2420) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2437) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____2454) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_abs (uu____2483) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2516) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_let (uu____2549) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_match (uu____2578) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_meta (uu____2617) -> begin
(

let uu____2624 = (

let uu____2625 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____2626 = (FStar_Syntax_Print.tag_of_term t11)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2625 uu____2626)))
in (failwith uu____2624))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____2641) -> begin
(

let uu____2668 = (

let uu____2669 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____2670 = (FStar_Syntax_Print.tag_of_term t11)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2669 uu____2670)))
in (failwith uu____2668))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____2685) -> begin
(

let uu____2710 = (

let uu____2711 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____2712 = (FStar_Syntax_Print.tag_of_term t11)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2711 uu____2712)))
in (failwith uu____2710))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____2727 = (

let uu____2728 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____2729 = (FStar_Syntax_Print.tag_of_term t11)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2728 uu____2729)))
in (failwith uu____2727))
end))
in (

let uu____2744 = (whnf env t1)
in (aux false uu____2744))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____2755 = (

let uu____2770 = (empty_worklist env)
in (base_and_refinement env uu____2770 t))
in (FStar_All.pipe_right uu____2755 FStar_Pervasives_Native.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (

let uu____2805 = (FStar_Syntax_Syntax.null_bv t)
in ((uu____2805), (FStar_Syntax_Util.t_true))))


let as_refinement : 'Auu____2814 . FStar_TypeChecker_Env.env  ->  'Auu____2814  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env wl t -> (

let uu____2831 = (base_and_refinement env wl t)
in (match (uu____2831) with
| (t_base, refinement) -> begin
(match (refinement) with
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end
| FStar_Pervasives_Native.Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement : (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun uu____2911 -> (match (uu____2911) with
| (t_base, refopt) -> begin
(

let uu____2938 = (match (refopt) with
| FStar_Pervasives_Native.Some (y, phi) -> begin
((y), (phi))
end
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end)
in (match (uu____2938) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl prob -> (prob_to_string wl.tcenv prob))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (

let uu____2973 = (

let uu____2976 = (

let uu____2979 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____3002 -> (match (uu____3002) with
| (uu____3009, uu____3010, x) -> begin
x
end))))
in (FStar_List.append wl.attempting uu____2979))
in (FStar_List.map (wl_prob_to_string wl) uu____2976))
in (FStar_All.pipe_right uu____2973 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____3038 = (

let uu____3057 = (

let uu____3058 = (FStar_Syntax_Subst.compress k)
in uu____3058.FStar_Syntax_Syntax.n)
in (match (uu____3057) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (((FStar_List.length bs) = (FStar_List.length ys))) with
| true -> begin
(

let uu____3123 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (uu____3123)))
end
| uu____3148 -> begin
(

let uu____3149 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____3149) with
| (ys', t1, uu____3178) -> begin
(

let uu____3183 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t1))), (uu____3183)))
end))
end)
end
| uu____3224 -> begin
(

let uu____3225 = (

let uu____3236 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____3236)))
in ((((ys), (t))), (uu____3225)))
end))
in (match (uu____3038) with
| ((ys1, t1), (xs, c)) -> begin
(match (((FStar_List.length xs) <> (FStar_List.length ys1))) with
| true -> begin
(FStar_Syntax_Util.abs ys1 t1 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None []))))
end
| uu____3313 -> begin
(

let c1 = (

let uu____3315 = (FStar_Syntax_Util.rename_binders xs ys1)
in (FStar_Syntax_Subst.subst_comp uu____3315 c))
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

let uu____3348 = (p_guard prob)
in (match (uu____3348) with
| (uu____3353, uv) -> begin
((

let uu____3356 = (

let uu____3357 = (FStar_Syntax_Subst.compress uv)
in uu____3357.FStar_Syntax_Syntax.n)
in (match (uu____3356) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi1 = (u_abs k bs phi)
in ((

let uu____3389 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____3389) with
| true -> begin
(

let uu____3390 = (FStar_Util.string_of_int (p_pid prob))
in (

let uu____3391 = (FStar_Syntax_Print.term_to_string uv)
in (

let uu____3392 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" uu____3390 uu____3391 uu____3392))))
end
| uu____3393 -> begin
()
end));
(FStar_Syntax_Util.set_uvar uvar phi1);
)))
end
| uu____3394 -> begin
(match ((not (resolve_ok))) with
| true -> begin
(failwith "Impossible: this instance has already been assigned a solution")
end
| uu____3395 -> begin
()
end)
end));
(commit uvis);
(

let uu___150_3397 = wl
in {attempting = uu___150_3397.attempting; wl_deferred = uu___150_3397.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___150_3397.defer_ok; smt_ok = uu___150_3397.smt_ok; tcenv = uu___150_3397.tcenv});
)
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____3415 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____3415) with
| true -> begin
(

let uu____3416 = (FStar_Util.string_of_int pid)
in (

let uu____3417 = (

let uu____3418 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right uu____3418 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____3416 uu____3417)))
end
| uu____3423 -> begin
()
end));
(commit sol);
(

let uu___151_3425 = wl
in {attempting = uu___151_3425.attempting; wl_deferred = uu___151_3425.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___151_3425.defer_ok; smt_ok = uu___151_3425.smt_ok; tcenv = uu___151_3425.tcenv});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard1 = (fun t g -> (match (((t), (g))) with
| (uu____3467, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (FStar_Pervasives_Native.None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
FStar_Pervasives_Native.Some (f)
end
| (FStar_Pervasives_Native.Some (t1), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(

let uu____3479 = (FStar_Syntax_Util.mk_conj t1 f)
in FStar_Pervasives_Native.Some (uu____3479))
end))
in ((

let uu____3485 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____3485) with
| true -> begin
(

let uu____3486 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (

let uu____3487 = (

let uu____3488 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right uu____3488 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____3486 uu____3487)))
end
| uu____3493 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
)))


let rec occurs : 'b . worklist  ->  (FStar_Syntax_Syntax.uvar * 'b)  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun wl uk t -> (

let uu____3523 = (

let uu____3530 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right uu____3530 FStar_Util.set_elements))
in (FStar_All.pipe_right uu____3523 (FStar_Util.for_some (fun uu____3566 -> (match (uu____3566) with
| (uv, uu____3572) -> begin
(FStar_Syntax_Unionfind.equiv uv (FStar_Pervasives_Native.fst uk))
end))))))


let occurs_check : 'Auu____3585 'Auu____3586 . 'Auu____3586  ->  worklist  ->  (FStar_Syntax_Syntax.uvar * 'Auu____3585)  ->  FStar_Syntax_Syntax.typ  ->  (Prims.bool * Prims.string FStar_Pervasives_Native.option) = (fun env wl uk t -> (

let occurs_ok = (

let uu____3618 = (occurs wl uk t)
in (not (uu____3618)))
in (

let msg = (match (occurs_ok) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3624 -> begin
(

let uu____3625 = (

let uu____3626 = (FStar_Syntax_Print.uvar_to_string (FStar_Pervasives_Native.fst uk))
in (

let uu____3627 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" uu____3626 uu____3627)))
in FStar_Pervasives_Native.Some (uu____3625))
end)
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check : 'Auu____3644 'Auu____3645 . 'Auu____3645  ->  worklist  ->  (FStar_Syntax_Syntax.uvar * 'Auu____3644)  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.term  ->  (Prims.bool * Prims.bool * (Prims.string FStar_Pervasives_Native.option * FStar_Syntax_Syntax.bv FStar_Util.set * FStar_Syntax_Syntax.bv FStar_Util.set)) = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let uu____3699 = (occurs_check env wl uk t)
in (match (uu____3699) with
| (occurs_ok, msg) -> begin
(

let uu____3730 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (uu____3730), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars : 'Auu____3757 'Auu____3758 . (FStar_Syntax_Syntax.bv * 'Auu____3758) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____3757) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____3757) Prims.list = (fun v1 v2 -> (

let as_set1 = (fun v3 -> (FStar_All.pipe_right v3 (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set1 v1)
in (

let uu____3842 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____3896 uu____3897 -> (match (((uu____3896), (uu____3897))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____3978 = (

let uu____3979 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation uu____3979))
in (match (uu____3978) with
| true -> begin
((isect), (isect_set))
end
| uu____4000 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____4004 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____4004) with
| true -> begin
(

let uu____4017 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (uu____4017)))
end
| uu____4032 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (uu____3842) with
| (isect, uu____4058) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq : 'Auu____4087 'Auu____4088 . (FStar_Syntax_Syntax.bv * 'Auu____4088) Prims.list  ->  (FStar_Syntax_Syntax.bv * 'Auu____4087) Prims.list  ->  Prims.bool = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____4143 uu____4144 -> (match (((uu____4143), (uu____4144))) with
| ((a, uu____4162), (b, uu____4164)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt : 'Auu____4183 'Auu____4184 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____4184) Prims.list  ->  (FStar_Syntax_Syntax.term * 'Auu____4183)  ->  (FStar_Syntax_Syntax.bv * 'Auu____4183) FStar_Pervasives_Native.option = (fun env seen arg -> (

let hd1 = (norm_arg env arg)
in (match ((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(

let uu____4235 = (FStar_All.pipe_right seen (FStar_Util.for_some (fun uu____4249 -> (match (uu____4249) with
| (b, uu____4255) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end))))
in (match (uu____4235) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4266 -> begin
FStar_Pervasives_Native.Some (((a), ((FStar_Pervasives_Native.snd hd1))))
end))
end
| uu____4271 -> begin
FStar_Pervasives_Native.None
end)))


let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option = (fun env seen args -> (match (args) with
| [] -> begin
FStar_Pervasives_Native.Some ((FStar_List.rev seen))
end
| (hd1)::rest -> begin
(

let uu____4346 = (pat_var_opt env seen hd1)
in (match (uu____4346) with
| FStar_Pervasives_Native.None -> begin
((

let uu____4360 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____4360) with
| true -> begin
(

let uu____4361 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (FStar_Pervasives_Native.fst hd1))
in (FStar_Util.print1 "Not a pattern: %s\n" uu____4361))
end
| uu____4362 -> begin
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

let uu____4380 = (

let uu____4381 = (FStar_Syntax_Subst.compress t)
in uu____4381.FStar_Syntax_Syntax.n)
in (match (uu____4380) with
| FStar_Syntax_Syntax.Tm_uvar (uu____4384) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____4401); FStar_Syntax_Syntax.pos = uu____4402; FStar_Syntax_Syntax.vars = uu____4403}, uu____4404) -> begin
true
end
| uu____4441 -> begin
false
end)))


let destruct_flex_t : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.pos = uu____4566; FStar_Syntax_Syntax.vars = uu____4567}, args) -> begin
((t), (uv), (k), (args))
end
| uu____4635 -> begin
(failwith "Not a flex-uvar")
end))


let destruct_flex_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) * FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option) = (fun env t -> (

let uu____4714 = (destruct_flex_t t)
in (match (uu____4714) with
| (t1, uv, k, args) -> begin
(

let uu____4829 = (pat_vars env [] args)
in (match (uu____4829) with
| FStar_Pervasives_Native.Some (vars) -> begin
((((t1), (uv), (k), (args))), (FStar_Pervasives_Native.Some (vars)))
end
| uu____4927 -> begin
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
| uu____5009 -> begin
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
| uu____5046 -> begin
false
end))


let uu___is_FullMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullMatch -> begin
true
end
| uu____5051 -> begin
false
end))


let head_match : match_result  ->  match_result = (fun uu___127_5055 -> (match (uu___127_5055) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____5070 -> begin
HeadMatch
end))


let fv_delta_depth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.delta_depth = (fun env fv -> (match (fv.FStar_Syntax_Syntax.fv_delta) with
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(match ((env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)) with
| true -> begin
d
end
| uu____5080 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
end
| FStar_Syntax_Syntax.Delta_defined_at_level (uu____5081) -> begin
(

let uu____5082 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5082) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Syntax.Delta_constant
end
| uu____5093 -> begin
fv.FStar_Syntax_Syntax.fv_delta
end))
end
| d -> begin
d
end))


let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____5114) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____5123) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_bvar (uu____5150) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_name (uu____5151) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uvar (uu____5152) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_let (uu____5169) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_match (uu____5182) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____5206) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____5212, uu____5213) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____5255) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____5276; FStar_Syntax_Syntax.index = uu____5277; FStar_Syntax_Syntax.sort = t2}, uu____5279) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_constant (uu____5286) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_type (uu____5287) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____5288) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_abs (uu____5301) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5319 = (fv_delta_depth env fv)
in FStar_Pervasives_Native.Some (uu____5319))
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
| uu____5336 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____5343 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____5343) with
| true -> begin
FullMatch
end
| uu____5344 -> begin
(

let uu____5345 = (

let uu____5354 = (

let uu____5357 = (fv_delta_depth env f)
in FStar_Pervasives_Native.Some (uu____5357))
in (

let uu____5358 = (

let uu____5361 = (fv_delta_depth env g)
in FStar_Pervasives_Native.Some (uu____5361))
in ((uu____5354), (uu____5358))))
in MisMatch (uu____5345))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____5367), FStar_Syntax_Syntax.Tm_uinst (g, uu____5369)) -> begin
(

let uu____5378 = (head_matches env f g)
in (FStar_All.pipe_right uu____5378 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(match ((c = d)) with
| true -> begin
FullMatch
end
| uu____5381 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end)
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, uu____5387), FStar_Syntax_Syntax.Tm_uvar (uv', uu____5389)) -> begin
(

let uu____5438 = (FStar_Syntax_Unionfind.equiv uv uv')
in (match (uu____5438) with
| true -> begin
FullMatch
end
| uu____5439 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____5445), FStar_Syntax_Syntax.Tm_refine (y, uu____5447)) -> begin
(

let uu____5456 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____5456 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____5458), uu____5459) -> begin
(

let uu____5464 = (head_matches env x.FStar_Syntax_Syntax.sort t21)
in (FStar_All.pipe_right uu____5464 head_match))
end
| (uu____5465, FStar_Syntax_Syntax.Tm_refine (x, uu____5467)) -> begin
(

let uu____5472 = (head_matches env t11 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____5472 head_match))
end
| (FStar_Syntax_Syntax.Tm_type (uu____5473), FStar_Syntax_Syntax.Tm_type (uu____5474)) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_arrow (uu____5475), FStar_Syntax_Syntax.Tm_arrow (uu____5476)) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____5502), FStar_Syntax_Syntax.Tm_app (head', uu____5504)) -> begin
(

let uu____5545 = (head_matches env head1 head')
in (FStar_All.pipe_right uu____5545 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____5547), uu____5548) -> begin
(

let uu____5569 = (head_matches env head1 t21)
in (FStar_All.pipe_right uu____5569 head_match))
end
| (uu____5570, FStar_Syntax_Syntax.Tm_app (head1, uu____5572)) -> begin
(

let uu____5593 = (head_matches env t11 head1)
in (FStar_All.pipe_right uu____5593 head_match))
end
| uu____5594 -> begin
(

let uu____5599 = (

let uu____5608 = (delta_depth_of_term env t11)
in (

let uu____5611 = (delta_depth_of_term env t21)
in ((uu____5608), (uu____5611))))
in MisMatch (uu____5599))
end))))


let head_matches_delta : 'Auu____5628 . FStar_TypeChecker_Env.env  ->  'Auu____5628  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (match_result * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) FStar_Pervasives_Native.option) = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let uu____5661 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____5661) with
| (head1, uu____5679) -> begin
(

let uu____5700 = (

let uu____5701 = (FStar_Syntax_Util.un_uinst head1)
in uu____5701.FStar_Syntax_Syntax.n)
in (match (uu____5700) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5707 = (

let uu____5708 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____5708 FStar_Option.isSome))
in (match (uu____5707) with
| true -> begin
(

let uu____5727 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right uu____5727 (fun _0_47 -> FStar_Pervasives_Native.Some (_0_47))))
end
| uu____5730 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____5731 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (

let success = (fun d r t11 t21 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (((t11), (t21)))
end
| uu____5771 -> begin
FStar_Pervasives_Native.None
end))))
in (

let fail = (fun r -> ((r), (FStar_Pervasives_Native.None)))
in (

let rec aux = (fun retry n_delta t11 t21 -> (

let r = (head_matches env t11 t21)
in (match (r) with
| MisMatch (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational), uu____5834) -> begin
(match ((not (retry))) with
| true -> begin
(fail r)
end
| uu____5851 -> begin
(

let uu____5852 = (

let uu____5861 = (maybe_inline t11)
in (

let uu____5864 = (maybe_inline t21)
in ((uu____5861), (uu____5864))))
in (match (uu____5852) with
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
| MisMatch (uu____5901, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational)) -> begin
(match ((not (retry))) with
| true -> begin
(fail r)
end
| uu____5918 -> begin
(

let uu____5919 = (

let uu____5928 = (maybe_inline t11)
in (

let uu____5931 = (maybe_inline t21)
in ((uu____5928), (uu____5931))))
in (match (uu____5919) with
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

let uu____5974 = (FStar_TypeChecker_Common.decr_delta_depth d1)
in (match (uu____5974) with
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

let uu____5997 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in ((t1'), (t21)))
end
| uu____6007 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t21)
in ((t11), (t2')))
end)
in (match (uu____5997) with
| (t12, t22) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
end)))
end
| MisMatch (uu____6021) -> begin
(fail r)
end
| uu____6030 -> begin
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
| uu____6064 -> begin
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
| uu____6102 -> begin
false
end))


let __proj__C__item___0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_0) -> begin
_0
end))


type tcs =
tc Prims.list


let tc_to_string : tc  ->  Prims.string = (fun uu___128_6116 -> (match (uu___128_6116) with
| T (t, uu____6118) -> begin
(term_to_string t)
end
| C (c) -> begin
(FStar_Syntax_Print.comp_to_string c)
end))


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____6136 = (FStar_Syntax_Util.type_u ())
in (match (uu____6136) with
| (t, uu____6142) -> begin
(

let uu____6143 = (new_uvar r binders t)
in (FStar_Pervasives_Native.fst uu____6143))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____6156 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____6156 FStar_Pervasives_Native.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * variance * tc) Prims.list) = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (

let uu____6222 = (head_matches env t1 t')
in (match (uu____6222) with
| MisMatch (uu____6223) -> begin
false
end
| uu____6232 -> begin
true
end)))
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let rebuild = (fun args' -> (

let args1 = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((uu____6328, imp), T (t2, uu____6331)) -> begin
((t2), (imp))
end
| uu____6350 -> begin
(failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd1), (args1)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun uu____6417 -> (match (uu____6417) with
| (t2, uu____6431) -> begin
((FStar_Pervasives_Native.None), (INVARIANT), (T (((t2), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____6474 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6474) with
| (bs1, c1) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs2 tcs1 -> (match (((bs2), (tcs1))) with
| (((x, imp))::bs3, (T (t2, uu____6549))::tcs2) -> begin
(aux (((((

let uu___152_6584 = x
in {FStar_Syntax_Syntax.ppname = uu___152_6584.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___152_6584.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (imp)))::out) bs3 tcs2)
end
| ([], (C (c2))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c2)
end
| uu____6602 -> begin
(failwith "Bad reconstruction")
end))
in (aux [] bs1 tcs)))
in (

let rec decompose1 = (fun out uu___129_6655 -> (match (uu___129_6655) with
| [] -> begin
(FStar_List.rev ((((FStar_Pervasives_Native.None), (COVARIANT), (C (c1))))::out))
end
| (hd1)::rest -> begin
(decompose1 ((((FStar_Pervasives_Native.Some (hd1)), (CONTRAVARIANT), (T ((((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (

let uu____6772 = (decompose1 [] bs1)
in ((rebuild), (matches), (uu____6772)))))
end))
end
| uu____6821 -> begin
(

let rebuild = (fun uu___130_6827 -> (match (uu___130_6827) with
| [] -> begin
t1
end
| uu____6830 -> begin
(failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t2 -> (FStar_Util.return_all true))), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun uu___131_6862 -> (match (uu___131_6862) with
| T (t, uu____6864) -> begin
t
end
| uu____6873 -> begin
(failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun uu___132_6877 -> (match (uu___132_6877) with
| T (t, uu____6879) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| uu____6888 -> begin
(failwith "Impossible")
end))


let imitation_sub_probs : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * variance * tc) Prims.list  ->  (FStar_TypeChecker_Common.prob Prims.list * tc Prims.list * FStar_Syntax_Syntax.formula) = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope1 args q -> (match (q) with
| (uu____6999, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope1 r)
in (

let uu____7024 = (new_uvar r scope1 k)
in (match (uu____7024) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| uu____7042 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) FStar_Pervasives_Native.None r)
end)
in (

let uu____7059 = (

let uu____7060 = (mk_problem scope1 orig gi_ps (vary_rel rel variance) ti FStar_Pervasives_Native.None "type subterm")
in (FStar_All.pipe_left (fun _0_48 -> FStar_TypeChecker_Common.TProb (_0_48)) uu____7060))
in ((T (((gi_xs), (mk_kind)))), (uu____7059))))
end)))
end
| (uu____7073, uu____7074, C (uu____7075)) -> begin
(failwith "impos")
end))
in (

let rec aux = (fun scope1 args qs1 -> (match (qs1) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs2 -> begin
(

let uu____7222 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.pos = uu____7239; FStar_Syntax_Syntax.vars = uu____7240})) -> begin
(

let uu____7263 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____7263) with
| (T (gi_xs, uu____7287), prob) -> begin
(

let uu____7297 = (

let uu____7298 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_49 -> C (_0_49)) uu____7298))
in ((uu____7297), ((prob)::[])))
end
| uu____7301 -> begin
(failwith "impossible")
end))
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.pos = uu____7316; FStar_Syntax_Syntax.vars = uu____7317})) -> begin
(

let uu____7340 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____7340) with
| (T (gi_xs, uu____7364), prob) -> begin
(

let uu____7374 = (

let uu____7375 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_50 -> C (_0_50)) uu____7375))
in ((uu____7374), ((prob)::[])))
end
| uu____7378 -> begin
(failwith "impossible")
end))
end
| (uu____7389, uu____7390, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.pos = uu____7392; FStar_Syntax_Syntax.vars = uu____7393})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((FStar_Pervasives_Native.None), (INVARIANT), (T ((((FStar_Pervasives_Native.fst t)), (generic_kind))))))))
in (

let components1 = (((FStar_Pervasives_Native.None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let uu____7524 = (

let uu____7533 = (FStar_List.map (sub_prob scope1 args) components1)
in (FStar_All.pipe_right uu____7533 FStar_List.unzip))
in (match (uu____7524) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (

let uu____7587 = (

let uu____7588 = (

let uu____7591 = (FStar_List.hd tcs)
in (FStar_All.pipe_right uu____7591 un_T))
in (

let uu____7592 = (

let uu____7601 = (FStar_List.tl tcs)
in (FStar_All.pipe_right uu____7601 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____7588; FStar_Syntax_Syntax.effect_args = uu____7592; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____7587))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| uu____7610 -> begin
(

let uu____7623 = (sub_prob scope1 args q)
in (match (uu____7623) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (uu____7222) with
| (tc, probs) -> begin
(

let uu____7654 = (match (((q), (tc))) with
| ((FStar_Pervasives_Native.Some (b, imp), uu____7717, uu____7718), T (t, uu____7720)) -> begin
(

let b1 = (((

let uu___153_7757 = b
in {FStar_Syntax_Syntax.ppname = uu___153_7757.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___153_7757.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let uu____7758 = (

let uu____7765 = (FStar_Syntax_Util.arg_of_non_null_binder b1)
in (uu____7765)::args)
in ((FStar_Pervasives_Native.Some (b1)), ((b1)::scope1), (uu____7758))))
end
| uu____7800 -> begin
((FStar_Pervasives_Native.None), (scope1), (args))
end)
in (match (uu____7654) with
| (bopt, scope2, args1) -> begin
(

let uu____7884 = (aux scope2 args1 qs2)
in (match (uu____7884) with
| (sub_probs, tcs, f) -> begin
(

let f1 = (match (bopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7921 = (

let uu____7924 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst))))
in (f)::uu____7924)
in (FStar_Syntax_Util.mk_conj_l uu____7921))
end
| FStar_Pervasives_Native.Some (b) -> begin
(

let u_b = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (

let uu____7947 = (

let uu____7950 = (FStar_Syntax_Util.mk_forall u_b (FStar_Pervasives_Native.fst b) f)
in (

let uu____7951 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst))))
in (uu____7950)::uu____7951))
in (FStar_Syntax_Util.mk_conj_l uu____7947)))
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


let compress_tprob : 'Auu____8022 . worklist  ->  (FStar_Syntax_Syntax.term, 'Auu____8022) FStar_TypeChecker_Common.problem  ->  (FStar_Syntax_Syntax.term, 'Auu____8022) FStar_TypeChecker_Common.problem = (fun wl p -> (

let uu___154_8043 = p
in (

let uu____8048 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____8049 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___154_8043.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____8048; FStar_TypeChecker_Common.relation = uu___154_8043.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____8049; FStar_TypeChecker_Common.element = uu___154_8043.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___154_8043.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___154_8043.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___154_8043.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___154_8043.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___154_8043.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p1) -> begin
(

let uu____8063 = (compress_tprob wl p1)
in (FStar_All.pipe_right uu____8063 (fun _0_51 -> FStar_TypeChecker_Common.TProb (_0_51))))
end
| FStar_TypeChecker_Common.CProb (uu____8072) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (

let uu____8094 = (compress_prob wl pr)
in (FStar_All.pipe_right uu____8094 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____8104 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____8104) with
| (lh, uu____8124) -> begin
(

let uu____8145 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____8145) with
| (rh, uu____8165) -> begin
(

let uu____8186 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____8203), FStar_Syntax_Syntax.Tm_uvar (uu____8204)) -> begin
((flex_flex), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____8241), uu____8242) when ((tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (uu____8263, FStar_Syntax_Syntax.Tm_uvar (uu____8264)) when ((tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____8285), uu____8286) -> begin
(

let uu____8303 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (uu____8303) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
((flex_rigid), (tp))
end
| uu____8366 -> begin
(

let rank = (

let uu____8376 = (is_top_level_prob prob)
in (match (uu____8376) with
| true -> begin
flex_refine
end
| uu____8377 -> begin
flex_refine_inner
end))
in (

let uu____8378 = (

let uu___155_8383 = tp
in (

let uu____8388 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___155_8383.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___155_8383.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___155_8383.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____8388; FStar_TypeChecker_Common.element = uu___155_8383.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___155_8383.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___155_8383.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___155_8383.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___155_8383.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___155_8383.FStar_TypeChecker_Common.rank}))
in ((rank), (uu____8378))))
end)
end))
end
| (uu____8403, FStar_Syntax_Syntax.Tm_uvar (uu____8404)) -> begin
(

let uu____8421 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (uu____8421) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
((rigid_flex), (tp))
end
| uu____8484 -> begin
(

let uu____8493 = (

let uu___156_8500 = tp
in (

let uu____8505 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___156_8500.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____8505; FStar_TypeChecker_Common.relation = uu___156_8500.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___156_8500.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___156_8500.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___156_8500.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___156_8500.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___156_8500.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___156_8500.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___156_8500.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (uu____8493)))
end)
end))
end
| (uu____8526, uu____8527) -> begin
((rigid_rigid), (tp))
end)
in (match (uu____8186) with
| (rank, tp1) -> begin
(

let uu____8546 = (FStar_All.pipe_right (

let uu___157_8552 = tp1
in {FStar_TypeChecker_Common.pid = uu___157_8552.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___157_8552.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___157_8552.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___157_8552.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___157_8552.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___157_8552.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___157_8552.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___157_8552.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___157_8552.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rank)}) (fun _0_52 -> FStar_TypeChecker_Common.TProb (_0_52)))
in ((rank), (uu____8546)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____8562 = (FStar_All.pipe_right (

let uu___158_8568 = cp
in {FStar_TypeChecker_Common.pid = uu___158_8568.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___158_8568.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___158_8568.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___158_8568.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___158_8568.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___158_8568.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___158_8568.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___158_8568.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___158_8568.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rigid_rigid)}) (fun _0_53 -> FStar_TypeChecker_Common.CProb (_0_53)))
in ((rigid_rigid), (uu____8562)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun uu____8624 probs -> (match (uu____8624) with
| (min_rank, min1, out) -> begin
(match (probs) with
| [] -> begin
((min1), (out), (min_rank))
end
| (hd1)::tl1 -> begin
(

let uu____8677 = (rank wl hd1)
in (match (uu____8677) with
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
| uu____8723 -> begin
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
| uu____8753 -> begin
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
| uu____8787 -> begin
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
| uu____8801 -> begin
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
| uu____8815 -> begin
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

let uu____8860 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____8860) with
| (k, uu____8866) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Syntax_Unionfind.univ_equiv v1 v2)
end
| uu____8876 -> begin
false
end)
end)))))
end
| uu____8877 -> begin
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

let uu____8928 = (really_solve_universe_eq pid_orig wl1 u13 u23)
in (match (uu____8928) with
| USolved (wl2) -> begin
(aux wl2 us12 us22)
end
| failed -> begin
failed
end))
end
| uu____8931 -> begin
USolved (wl1)
end))
in (aux wl us1 us2))
end
| uu____8940 -> begin
(

let uu____8941 = (

let uu____8942 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____8943 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" uu____8942 uu____8943)))
in UFailed (uu____8941))
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

let uu____8963 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____8963) with
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

let uu____8985 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____8985) with
| USolved (wl2) -> begin
(aux wl2 us2)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____8988 -> begin
(

let uu____8993 = (

let uu____8994 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____8995 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" uu____8994 uu____8995 msg)))
in UFailed (uu____8993))
end))
in (match (((u11), (u21))) with
| (FStar_Syntax_Syntax.U_bvar (uu____8996), uu____8997) -> begin
(

let uu____8998 = (

let uu____8999 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____9000 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____8999 uu____9000)))
in (failwith uu____8998))
end
| (FStar_Syntax_Syntax.U_unknown, uu____9001) -> begin
(

let uu____9002 = (

let uu____9003 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____9004 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____9003 uu____9004)))
in (failwith uu____9002))
end
| (uu____9005, FStar_Syntax_Syntax.U_bvar (uu____9006)) -> begin
(

let uu____9007 = (

let uu____9008 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____9009 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____9008 uu____9009)))
in (failwith uu____9007))
end
| (uu____9010, FStar_Syntax_Syntax.U_unknown) -> begin
(

let uu____9011 = (

let uu____9012 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____9013 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____9012 uu____9013)))
in (failwith uu____9011))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((x.FStar_Ident.idText = y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____9016 -> begin
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

let uu____9037 = (FStar_Syntax_Unionfind.univ_equiv v1 v2)
in (match (uu____9037) with
| true -> begin
USolved (wl)
end
| uu____9038 -> begin
(

let wl1 = (extend_solution pid_orig ((UNIV (((v1), (u21))))::[]) wl)
in USolved (wl1))
end))
end
| (FStar_Syntax_Syntax.U_unif (v1), u) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____9059 = (occurs_univ v1 u3)
in (match (uu____9059) with
| true -> begin
(

let uu____9060 = (

let uu____9061 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____9062 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____9061 uu____9062)))
in (try_umax_components u11 u21 uu____9060))
end
| uu____9063 -> begin
(

let uu____9064 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____9064))
end)))
end
| (u, FStar_Syntax_Syntax.U_unif (v1)) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____9084 = (occurs_univ v1 u3)
in (match (uu____9084) with
| true -> begin
(

let uu____9085 = (

let uu____9086 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____9087 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____9086 uu____9087)))
in (try_umax_components u11 u21 uu____9085))
end
| uu____9088 -> begin
(

let uu____9089 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____9089))
end)))
end
| (FStar_Syntax_Syntax.U_max (uu____9098), uu____9099) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____9102 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____9105 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____9105) with
| true -> begin
USolved (wl)
end
| uu____9106 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (uu____9107, FStar_Syntax_Syntax.U_max (uu____9108)) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____9111 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____9114 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____9114) with
| true -> begin
USolved (wl)
end
| uu____9115 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (FStar_Syntax_Syntax.U_succ (uu____9116), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_succ (uu____9117), FStar_Syntax_Syntax.U_name (uu____9118)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ (uu____9119)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name (uu____9120)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____9121), FStar_Syntax_Syntax.U_succ (uu____9122)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____9123), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end))))))


let solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (match (wl.tcenv.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
USolved (wl)
end
| uu____9140 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders : 'a 'b . ('a Prims.list * ('a Prims.list  ->  'b))  ->  ('a Prims.list * ('a Prims.list  ->  'b))  ->  (('a Prims.list * 'b) * ('a Prims.list * 'b)) = (fun bc1 bc2 -> (

let uu____9217 = bc1
in (match (uu____9217) with
| (bs1, mk_cod1) -> begin
(

let uu____9258 = bc2
in (match (uu____9258) with
| (bs2, mk_cod2) -> begin
(

let curry = (fun n1 bs mk_cod -> (

let uu____9328 = (FStar_Util.first_N n1 bs)
in (match (uu____9328) with
| (bs3, rest) -> begin
(

let uu____9353 = (mk_cod rest)
in ((bs3), (uu____9353)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(

let uu____9382 = (

let uu____9389 = (mk_cod1 [])
in ((bs1), (uu____9389)))
in (

let uu____9392 = (

let uu____9399 = (mk_cod2 [])
in ((bs2), (uu____9399)))
in ((uu____9382), (uu____9392))))
end
| uu____9414 -> begin
(match ((l1 > l2)) with
| true -> begin
(

let uu____9441 = (curry l2 bs1 mk_cod1)
in (

let uu____9454 = (

let uu____9461 = (mk_cod2 [])
in ((bs2), (uu____9461)))
in ((uu____9441), (uu____9454))))
end
| uu____9476 -> begin
(

let uu____9477 = (

let uu____9484 = (mk_cod1 [])
in ((bs1), (uu____9484)))
in (

let uu____9487 = (curry l1 bs2 mk_cod2)
in ((uu____9477), (uu____9487))))
end)
end))))
end))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____9608 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____9608) with
| true -> begin
(

let uu____9609 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" uu____9609))
end
| uu____9610 -> begin
()
end));
(

let uu____9611 = (next_prob probs)
in (match (uu____9611) with
| (FStar_Pervasives_Native.Some (hd1), tl1, rank1) -> begin
(

let probs1 = (

let uu___159_9632 = probs
in {attempting = tl1; wl_deferred = uu___159_9632.wl_deferred; ctr = uu___159_9632.ctr; defer_ok = uu___159_9632.defer_ok; smt_ok = uu___159_9632.smt_ok; tcenv = uu___159_9632.tcenv})
in (match (hd1) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs1)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match ((((not (probs1.defer_ok)) && (flex_refine_inner <= rank1)) && (rank1 <= flex_rigid))) with
| true -> begin
(

let uu____9643 = (solve_flex_rigid_join env tp probs1)
in (match (uu____9643) with
| FStar_Pervasives_Native.None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| FStar_Pervasives_Native.Some (wl) -> begin
(solve env wl)
end))
end
| uu____9647 -> begin
(match ((((not (probs1.defer_ok)) && (rigid_flex <= rank1)) && (rank1 <= refine_flex))) with
| true -> begin
(

let uu____9648 = (solve_rigid_flex_meet env tp probs1)
in (match (uu____9648) with
| FStar_Pervasives_Native.None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| FStar_Pervasives_Native.Some (wl) -> begin
(solve env wl)
end))
end
| uu____9652 -> begin
(solve_t' env (maybe_invert tp) probs1)
end)
end)
end))
end
| (FStar_Pervasives_Native.None, uu____9653, uu____9654) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| uu____9671 -> begin
(

let uu____9680 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____9739 -> (match (uu____9739) with
| (c, uu____9747, uu____9748) -> begin
(c < probs.ctr)
end))))
in (match (uu____9680) with
| (attempt1, rest) -> begin
(match (attempt1) with
| [] -> begin
(

let uu____9789 = (FStar_List.map (fun uu____9804 -> (match (uu____9804) with
| (uu____9815, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (uu____9789))
end
| uu____9818 -> begin
(

let uu____9827 = (

let uu___160_9828 = probs
in (

let uu____9829 = (FStar_All.pipe_right attempt1 (FStar_List.map (fun uu____9850 -> (match (uu____9850) with
| (uu____9857, uu____9858, y) -> begin
y
end))))
in {attempting = uu____9829; wl_deferred = rest; ctr = uu___160_9828.ctr; defer_ok = uu___160_9828.defer_ok; smt_ok = uu___160_9828.smt_ok; tcenv = uu___160_9828.tcenv}))
in (solve env uu____9827))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____9865 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____9865) with
| USolved (wl1) -> begin
(

let uu____9867 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____9867))
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

let uu____9913 = (solve_universe_eq (p_pid orig) wl1 u1 u2)
in (match (uu____9913) with
| USolved (wl2) -> begin
(aux wl2 us11 us21)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____9916 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t11 = (whnf env t1)
in (

let t21 = (whnf env t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.pos = uu____9928; FStar_Syntax_Syntax.vars = uu____9929}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.pos = uu____9932; FStar_Syntax_Syntax.vars = uu____9933}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____9947), uu____9948) -> begin
(failwith "Impossible: expect head symbols to match")
end
| (uu____9955, FStar_Syntax_Syntax.Tm_uinst (uu____9956)) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____9963 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____9973 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9973) with
| true -> begin
(

let uu____9974 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" uu____9974 msg))
end
| uu____9975 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____9976 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist FStar_Pervasives_Native.option = (fun env tp wl -> ((

let uu____9983 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____9983) with
| true -> begin
(

let uu____9984 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" uu____9984))
end
| uu____9985 -> begin
()
end));
(

let uu____9986 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____9986) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let uu____10048 = (head_matches_delta env () t1 t2)
in (match (uu____10048) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (uu____10089) -> begin
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

let uu____10138 = (match (ts) with
| FStar_Pervasives_Native.Some (t11, t21) -> begin
(

let uu____10153 = (FStar_Syntax_Subst.compress t11)
in (

let uu____10154 = (FStar_Syntax_Subst.compress t21)
in ((uu____10153), (uu____10154))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____10159 = (FStar_Syntax_Subst.compress t1)
in (

let uu____10160 = (FStar_Syntax_Subst.compress t2)
in ((uu____10159), (uu____10160))))
end)
in (match (uu____10138) with
| (t11, t21) -> begin
(

let eq_prob = (fun t12 t22 -> (

let uu____10186 = (new_problem env t12 FStar_TypeChecker_Common.EQ t22 FStar_Pervasives_Native.None t12.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _0_54 -> FStar_TypeChecker_Common.TProb (_0_54)) uu____10186)))
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(

let uu____10217 = (

let uu____10226 = (

let uu____10229 = (

let uu____10232 = (

let uu____10233 = (

let uu____10240 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (uu____10240)))
in FStar_Syntax_Syntax.Tm_refine (uu____10233))
in (FStar_Syntax_Syntax.mk uu____10232))
in (uu____10229 FStar_Pervasives_Native.None t11.FStar_Syntax_Syntax.pos))
in (

let uu____10248 = (

let uu____10251 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (uu____10251)::[])
in ((uu____10226), (uu____10248))))
in FStar_Pervasives_Native.Some (uu____10217))
end
| (uu____10264, FStar_Syntax_Syntax.Tm_refine (x, uu____10266)) -> begin
(

let uu____10271 = (

let uu____10278 = (

let uu____10281 = (eq_prob x.FStar_Syntax_Syntax.sort t11)
in (uu____10281)::[])
in ((t11), (uu____10278)))
in FStar_Pervasives_Native.Some (uu____10271))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____10291), uu____10292) -> begin
(

let uu____10297 = (

let uu____10304 = (

let uu____10307 = (eq_prob x.FStar_Syntax_Syntax.sort t21)
in (uu____10307)::[])
in ((t21), (uu____10304)))
in FStar_Pervasives_Native.Some (uu____10297))
end
| uu____10316 -> begin
(

let uu____10321 = (FStar_Syntax_Util.head_and_args t11)
in (match (uu____10321) with
| (head1, uu____10345) -> begin
(

let uu____10366 = (

let uu____10367 = (FStar_Syntax_Util.un_uinst head1)
in uu____10367.FStar_Syntax_Syntax.n)
in (match (uu____10366) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____10378; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (i); FStar_Syntax_Syntax.fv_qual = uu____10380}) -> begin
(

let prev = (match ((i > (Prims.parse_int "1"))) with
| true -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i - (Prims.parse_int "1")))
end
| uu____10384 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
in (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t21)
in (disjoin t12 t22))))
end
| uu____10387 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____10400) -> begin
(

let uu____10425 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___133_10451 -> (match (uu___133_10451) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| FStar_Pervasives_Native.Some (rank1) when (is_rigid_flex rank1) -> begin
(

let uu____10458 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.rhs)
in (match (uu____10458) with
| (u', uu____10474) -> begin
(

let uu____10495 = (

let uu____10496 = (whnf env u')
in uu____10496.FStar_Syntax_Syntax.n)
in (match (uu____10495) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____10500) -> begin
(FStar_Syntax_Unionfind.equiv uv uv')
end
| uu____10525 -> begin
false
end))
end))
end
| uu____10526 -> begin
false
end)
end
| uu____10529 -> begin
false
end))))
in (match (uu____10425) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun uu____10563 tps -> (match (uu____10563) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
FStar_Pervasives_Native.Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____10611 = (

let uu____10620 = (whnf env hd1.FStar_TypeChecker_Common.lhs)
in (disjoin bound uu____10620))
in (match (uu____10611) with
| FStar_Pervasives_Native.Some (bound1, sub1) -> begin
(make_lower_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____10655 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let uu____10664 = (

let uu____10673 = (

let uu____10680 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((uu____10680), ([])))
in (make_lower_bound uu____10673 lower_bounds))
in (match (uu____10664) with
| FStar_Pervasives_Native.None -> begin
((

let uu____10692 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____10692) with
| true -> begin
(FStar_Util.print_string "No lower bounds\n")
end
| uu____10693 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (lhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in ((

let uu____10712 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____10712) with
| true -> begin
(

let wl' = (

let uu___161_10714 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___161_10714.wl_deferred; ctr = uu___161_10714.ctr; defer_ok = uu___161_10714.defer_ok; smt_ok = uu___161_10714.smt_ok; tcenv = uu___161_10714.tcenv})
in (

let uu____10715 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" uu____10715)))
end
| uu____10716 -> begin
()
end));
(

let uu____10717 = (solve_t env eq_prob (

let uu___162_10719 = wl
in {attempting = sub_probs; wl_deferred = uu___162_10719.wl_deferred; ctr = uu___162_10719.ctr; defer_ok = uu___162_10719.defer_ok; smt_ok = uu___162_10719.smt_ok; tcenv = uu___162_10719.tcenv}))
in (match (uu____10717) with
| Success (uu____10722) -> begin
(

let wl1 = (

let uu___163_10724 = wl
in {attempting = rest; wl_deferred = uu___163_10724.wl_deferred; ctr = uu___163_10724.ctr; defer_ok = uu___163_10724.defer_ok; smt_ok = uu___163_10724.smt_ok; tcenv = uu___163_10724.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) FStar_Pervasives_Native.None [] wl1)
in (

let uu____10726 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p FStar_Pervasives_Native.None [] wl3)) wl2 lower_bounds)
in FStar_Pervasives_Native.Some (wl2))))
end
| uu____10731 -> begin
FStar_Pervasives_Native.None
end));
))
end)))
end))
end
| uu____10732 -> begin
(failwith "Impossible: Not a rigid-flex")
end)))
end));
))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist FStar_Pervasives_Native.option = (fun env tp wl -> ((

let uu____10741 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____10741) with
| true -> begin
(

let uu____10742 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" uu____10742))
end
| uu____10743 -> begin
()
end));
(

let uu____10744 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____10744) with
| (u, args) -> begin
(

let uu____10783 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (uu____10783) with
| (ok, head_match1, partial_match, fallback, failed_match) -> begin
(

let max1 = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____10808 -> begin
i
end))
in (

let base_types_match = (fun t1 t2 -> (

let uu____10824 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____10824) with
| (h1, args1) -> begin
(

let uu____10865 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____10865) with
| (h2, uu____10885) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
(

let uu____10912 = (FStar_Syntax_Syntax.fv_eq tc1 tc2)
in (match (uu____10912) with
| true -> begin
(match (((FStar_List.length args1) = (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____10929 -> begin
(

let uu____10930 = (

let uu____10933 = (

let uu____10934 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_55 -> FStar_TypeChecker_Common.TProb (_0_55)) uu____10934))
in (uu____10933)::[])
in FStar_Pervasives_Native.Some (uu____10930))
end)
end
| uu____10945 -> begin
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
| uu____10966 -> begin
(

let uu____10967 = (

let uu____10970 = (

let uu____10971 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_56 -> FStar_TypeChecker_Common.TProb (_0_56)) uu____10971))
in (uu____10970)::[])
in FStar_Pervasives_Native.Some (uu____10967))
end)
end
| uu____10982 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____10985 -> begin
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

let uu____11075 = (

let uu____11084 = (

let uu____11087 = (FStar_Syntax_Util.mk_conj phi11 phi21)
in (FStar_Syntax_Util.refine x1 uu____11087))
in ((uu____11084), (m1)))
in FStar_Pervasives_Native.Some (uu____11075))))))
end))
end
| (uu____11100, FStar_Syntax_Syntax.Tm_refine (y, uu____11102)) -> begin
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
| (FStar_Syntax_Syntax.Tm_refine (x, uu____11150), uu____11151) -> begin
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
| uu____11198 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____11251) -> begin
(

let uu____11276 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___134_11302 -> (match (uu___134_11302) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| FStar_Pervasives_Native.Some (rank1) when (is_flex_rigid rank1) -> begin
(

let uu____11309 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.lhs)
in (match (uu____11309) with
| (u', uu____11325) -> begin
(

let uu____11346 = (

let uu____11347 = (whnf env u')
in uu____11347.FStar_Syntax_Syntax.n)
in (match (uu____11346) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____11351) -> begin
(FStar_Syntax_Unionfind.equiv uv uv')
end
| uu____11376 -> begin
false
end))
end))
end
| uu____11377 -> begin
false
end)
end
| uu____11380 -> begin
false
end))))
in (match (uu____11276) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun uu____11418 tps -> (match (uu____11418) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
FStar_Pervasives_Native.Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____11480 = (

let uu____11491 = (whnf env hd1.FStar_TypeChecker_Common.rhs)
in (conjoin bound uu____11491))
in (match (uu____11480) with
| FStar_Pervasives_Native.Some (bound1, sub1) -> begin
(make_upper_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____11542 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let uu____11553 = (

let uu____11564 = (

let uu____11573 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((uu____11573), ([])))
in (make_upper_bound uu____11564 upper_bounds))
in (match (uu____11553) with
| FStar_Pervasives_Native.None -> begin
((

let uu____11587 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11587) with
| true -> begin
(FStar_Util.print_string "No upper bounds\n")
end
| uu____11588 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "joining refinements")
in ((

let uu____11613 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11613) with
| true -> begin
(

let wl' = (

let uu___164_11615 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___164_11615.wl_deferred; ctr = uu___164_11615.ctr; defer_ok = uu___164_11615.defer_ok; smt_ok = uu___164_11615.smt_ok; tcenv = uu___164_11615.tcenv})
in (

let uu____11616 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" uu____11616)))
end
| uu____11617 -> begin
()
end));
(

let uu____11618 = (solve_t env eq_prob (

let uu___165_11620 = wl
in {attempting = sub_probs; wl_deferred = uu___165_11620.wl_deferred; ctr = uu___165_11620.ctr; defer_ok = uu___165_11620.defer_ok; smt_ok = uu___165_11620.smt_ok; tcenv = uu___165_11620.tcenv}))
in (match (uu____11618) with
| Success (uu____11623) -> begin
(

let wl1 = (

let uu___166_11625 = wl
in {attempting = rest; wl_deferred = uu___166_11625.wl_deferred; ctr = uu___166_11625.ctr; defer_ok = uu___166_11625.defer_ok; smt_ok = uu___166_11625.smt_ok; tcenv = uu___166_11625.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) FStar_Pervasives_Native.None [] wl1)
in (

let uu____11627 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p FStar_Pervasives_Native.None [] wl3)) wl2 upper_bounds)
in FStar_Pervasives_Native.Some (wl2))))
end
| uu____11632 -> begin
FStar_Pervasives_Native.None
end));
))
end)))
end))
end
| uu____11633 -> begin
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

let uu____11724 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____11724) with
| true -> begin
(

let uu____11725 = (prob_to_string env1 rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" uu____11725))
end
| uu____11726 -> begin
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

let uu___167_11779 = hd1
in (

let uu____11780 = (FStar_Syntax_Subst.subst subst1 hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___167_11779.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___167_11779.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____11780}))
in (

let hd21 = (

let uu___168_11784 = hd2
in (

let uu____11785 = (FStar_Syntax_Subst.subst subst1 hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___168_11784.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___168_11784.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____11785}))
in (

let prob = (

let uu____11789 = (

let uu____11794 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd11.FStar_Syntax_Syntax.sort uu____11794 hd21.FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None "Formal parameter"))
in (FStar_All.pipe_left (fun _0_57 -> FStar_TypeChecker_Common.TProb (_0_57)) uu____11789))
in (

let hd12 = (FStar_Syntax_Syntax.freshen_bv hd11)
in (

let subst2 = (

let uu____11805 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd12))))::uu____11805)
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 hd12)
in (

let uu____11809 = (aux ((((hd12), (imp)))::scope) env2 subst2 xs1 ys1)
in (match (uu____11809) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi1 = (

let uu____11839 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (

let uu____11844 = (close_forall env2 ((((hd12), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj uu____11839 uu____11844)))
in ((

let uu____11854 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____11854) with
| true -> begin
(

let uu____11855 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____11856 = (FStar_Syntax_Print.bv_to_string hd12)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" uu____11855 uu____11856)))
end
| uu____11857 -> begin
()
end));
FStar_Util.Inl ((((prob)::sub_probs), (phi1)));
))
end
| fail -> begin
fail
end))))))))
end
| uu____11879 -> begin
FStar_Util.Inr ("arity or argument-qualifier mismatch")
end))
in (

let scope = (p_scope orig)
in (

let uu____11889 = (aux scope env [] bs1 bs2)
in (match (uu____11889) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (phi)) [] wl)
in (solve env (attempt sub_probs wl1)))
end)))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let uu____11913 = (compress_tprob wl problem)
in (solve_t' env uu____11913 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer1 = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env1 orig wl1 head1 head2 t1 t2 -> (

let uu____11946 = (head_matches_delta env1 wl1 t1 t2)
in (match (uu____11946) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____11977), uu____11978) -> begin
(

let rec may_relate = (fun head3 -> (

let uu____12003 = (

let uu____12004 = (FStar_Syntax_Subst.compress head3)
in uu____12004.FStar_Syntax_Syntax.n)
in (match (uu____12003) with
| FStar_Syntax_Syntax.Tm_name (uu____12007) -> begin
true
end
| FStar_Syntax_Syntax.Tm_match (uu____12008) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____12033, uu____12034) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____12076) -> begin
(may_relate t)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____12082) -> begin
(may_relate t)
end
| uu____12087 -> begin
false
end)))
in (

let uu____12088 = (((may_relate head1) || (may_relate head2)) && wl1.smt_ok)
in (match (uu____12088) with
| true -> begin
(

let guard = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_eq2 env1 t1 t2)
end
| uu____12090 -> begin
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

let uu____12105 = (

let uu____12106 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t11 uu____12106 t21))
in (FStar_Syntax_Util.mk_forall u_x x uu____12105))))
end))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB)) with
| true -> begin
(has_type_guard t1 t2)
end
| uu____12107 -> begin
(has_type_guard t2 t1)
end))
end)
in (

let uu____12108 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl1)
in (solve env1 uu____12108)))
end
| uu____12109 -> begin
(

let uu____12110 = (

let uu____12111 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____12112 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.format2 "head mismatch (%s vs %s)" uu____12111 uu____12112)))
in (giveup env1 uu____12110 orig))
end)))
end
| (uu____12113, FStar_Pervasives_Native.Some (t11, t21)) -> begin
(solve_t env1 (

let uu___169_12127 = problem
in {FStar_TypeChecker_Common.pid = uu___169_12127.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___169_12127.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___169_12127.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___169_12127.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___169_12127.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___169_12127.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___169_12127.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___169_12127.FStar_TypeChecker_Common.rank}) wl1)
end
| (uu____12128, FStar_Pervasives_Native.None) -> begin
((

let uu____12140 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____12140) with
| true -> begin
(

let uu____12141 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12142 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____12143 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____12144 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" uu____12141 uu____12142 uu____12143 uu____12144)))))
end
| uu____12145 -> begin
()
end));
(

let uu____12146 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____12146) with
| (head11, args1) -> begin
(

let uu____12183 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____12183) with
| (head21, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((nargs <> (FStar_List.length args2))) with
| true -> begin
(

let uu____12237 = (

let uu____12238 = (FStar_Syntax_Print.term_to_string head11)
in (

let uu____12239 = (args_to_string args1)
in (

let uu____12240 = (FStar_Syntax_Print.term_to_string head21)
in (

let uu____12241 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____12238 uu____12239 uu____12240 uu____12241)))))
in (giveup env1 uu____12237 orig))
end
| uu____12242 -> begin
(

let uu____12243 = ((nargs = (Prims.parse_int "0")) || (

let uu____12249 = (FStar_Syntax_Util.eq_args args1 args2)
in (uu____12249 = FStar_Syntax_Util.Equal)))
in (match (uu____12243) with
| true -> begin
(

let uu____12250 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____12250) with
| USolved (wl2) -> begin
(

let uu____12252 = (solve_prob orig FStar_Pervasives_Native.None [] wl2)
in (solve env1 uu____12252))
end
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end))
end
| uu____12255 -> begin
(

let uu____12256 = (base_and_refinement env1 wl1 t1)
in (match (uu____12256) with
| (base1, refinement1) -> begin
(

let uu____12293 = (base_and_refinement env1 wl1 t2)
in (match (uu____12293) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(

let uu____12374 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____12374) with
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end
| USolved (wl2) -> begin
(

let subprobs = (FStar_List.map2 (fun uu____12396 uu____12397 -> (match (((uu____12396), (uu____12397))) with
| ((a, uu____12415), (a', uu____12417)) -> begin
(

let uu____12426 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' FStar_Pervasives_Native.None "index")
in (FStar_All.pipe_left (fun _0_58 -> FStar_TypeChecker_Common.TProb (_0_58)) uu____12426))
end)) args1 args2)
in (

let formula = (

let uu____12436 = (FStar_List.map (fun p -> (FStar_Pervasives_Native.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____12436))
in (

let wl3 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) [] wl2)
in (solve env1 (attempt subprobs wl3)))))
end))
end
| uu____12442 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env1 (

let uu___170_12490 = problem
in {FStar_TypeChecker_Common.pid = uu___170_12490.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___170_12490.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___170_12490.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___170_12490.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___170_12490.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___170_12490.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___170_12490.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___170_12490.FStar_TypeChecker_Common.rank}) wl1)))
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

let uu____12510 = p
in (match (uu____12510) with
| (((u, k), xs, c), ps, (h, uu____12521, qs)) -> begin
(

let xs1 = (sn_binders env1 xs)
in (

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____12603 = (imitation_sub_probs orig env1 xs1 ps qs)
in (match (uu____12603) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (

let uu____12626 = (h gs_xs)
in (

let uu____12627 = (FStar_All.pipe_right (FStar_Syntax_Util.residual_comp_of_comp c) (fun _0_59 -> FStar_Pervasives_Native.Some (_0_59)))
in (FStar_Syntax_Util.abs xs1 uu____12626 uu____12627)))
in ((

let uu____12633 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____12633) with
| true -> begin
(

let uu____12634 = (

let uu____12637 = (

let uu____12638 = (FStar_List.map tc_to_string gs_xs)
in (FStar_All.pipe_right uu____12638 (FStar_String.concat "\n\t")))
in (

let uu____12643 = (

let uu____12646 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____12647 = (

let uu____12650 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____12651 = (

let uu____12654 = (FStar_Syntax_Print.term_to_string im)
in (

let uu____12655 = (

let uu____12658 = (FStar_Syntax_Print.tag_of_term im)
in (

let uu____12659 = (

let uu____12662 = (

let uu____12663 = (FStar_List.map (prob_to_string env1) sub_probs)
in (FStar_All.pipe_right uu____12663 (FStar_String.concat ", ")))
in (

let uu____12668 = (

let uu____12671 = (FStar_TypeChecker_Normalize.term_to_string env1 formula)
in (uu____12671)::[])
in (uu____12662)::uu____12668))
in (uu____12658)::uu____12659))
in (uu____12654)::uu____12655))
in (uu____12650)::uu____12651))
in (uu____12646)::uu____12647))
in (uu____12637)::uu____12643))
in (FStar_Util.print "Imitating gs_xs=%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" uu____12634))
end
| uu____12672 -> begin
()
end));
(

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl1)
in (solve env1 (attempt sub_probs wl2)));
))
end))))
end)))
in (

let imitate' = (fun orig env1 wl1 uu___135_12692 -> (match (uu___135_12692) with
| FStar_Pervasives_Native.None -> begin
(giveup env1 "unable to compute subterms" orig)
end
| FStar_Pervasives_Native.Some (p) -> begin
(imitate orig env1 wl1 p)
end))
in (

let project = (fun orig env1 wl1 i p -> (

let uu____12724 = p
in (match (uu____12724) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____12815 = (FStar_List.nth ps i)
in (match (uu____12815) with
| (pi, uu____12819) -> begin
(

let uu____12824 = (FStar_List.nth xs i)
in (match (uu____12824) with
| (xi, uu____12836) -> begin
(

let rec gs = (fun k -> (

let uu____12849 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____12849) with
| (bs, k1) -> begin
(

let rec aux = (fun subst1 bs1 -> (match (bs1) with
| [] -> begin
(([]), ([]))
end
| ((a, uu____12936))::tl1 -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst1 a.FStar_Syntax_Syntax.sort)
in (

let uu____12949 = (new_uvar r xs k_a)
in (match (uu____12949) with
| (gi_xs, gi) -> begin
(

let gi_xs1 = (FStar_TypeChecker_Normalize.eta_expand env1 gi_xs)
in (

let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps FStar_Pervasives_Native.None r)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((a), (gi_xs1))))::subst1
in (

let uu____12971 = (aux subst2 tl1)
in (match (uu____12971) with
| (gi_xs', gi_ps') -> begin
(

let uu____12998 = (

let uu____13001 = (FStar_Syntax_Syntax.as_arg gi_xs1)
in (uu____13001)::gi_xs')
in (

let uu____13002 = (

let uu____13005 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (uu____13005)::gi_ps')
in ((uu____12998), (uu____13002))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in (

let uu____13010 = (

let uu____13011 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation uu____13011))
in (match (uu____13010) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13014 -> begin
(

let uu____13015 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (uu____13015) with
| (g_xs, uu____13027) -> begin
(

let xi1 = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (

let uu____13038 = (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs FStar_Pervasives_Native.None r)
in (

let uu____13039 = (FStar_All.pipe_right (FStar_Syntax_Util.residual_comp_of_comp c) (fun _0_60 -> FStar_Pervasives_Native.Some (_0_60)))
in (FStar_Syntax_Util.abs xs uu____13038 uu____13039)))
in (

let sub1 = (

let uu____13045 = (

let uu____13050 = (FStar_Syntax_Syntax.mk_Tm_app proj ps FStar_Pervasives_Native.None r)
in (

let uu____13053 = (

let uu____13056 = (FStar_List.map (fun uu____13071 -> (match (uu____13071) with
| (uu____13080, uu____13081, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h uu____13056))
in (mk_problem (p_scope orig) orig uu____13050 (p_rel orig) uu____13053 FStar_Pervasives_Native.None "projection")))
in (FStar_All.pipe_left (fun _0_61 -> FStar_TypeChecker_Common.TProb (_0_61)) uu____13045))
in ((

let uu____13096 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____13096) with
| true -> begin
(

let uu____13097 = (FStar_Syntax_Print.term_to_string proj)
in (

let uu____13098 = (prob_to_string env1 sub1)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" uu____13097 uu____13098)))
end
| uu____13099 -> begin
()
end));
(

let wl2 = (

let uu____13101 = (

let uu____13104 = (FStar_All.pipe_left FStar_Pervasives_Native.fst (p_guard sub1))
in FStar_Pervasives_Native.Some (uu____13104))
in (solve_prob orig uu____13101 ((TERM (((u), (proj))))::[]) wl1))
in (

let uu____13113 = (solve env1 (attempt ((sub1)::[]) wl2))
in (FStar_All.pipe_left (fun _0_62 -> FStar_Pervasives_Native.Some (_0_62)) uu____13113)));
))))
end))
end)))
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl1 -> (

let uu____13144 = lhs
in (match (uu____13144) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let uu____13180 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (uu____13180) with
| (xs, c) -> begin
(match (((FStar_List.length xs) = (FStar_List.length ps))) with
| true -> begin
(

let uu____13213 = (

let uu____13260 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____13260)))
in FStar_Pervasives_Native.Some (uu____13213))
end
| uu____13379 -> begin
(

let k_uv1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (

let uu____13404 = (

let uu____13411 = (

let uu____13412 = (FStar_Syntax_Subst.compress k)
in uu____13412.FStar_Syntax_Syntax.n)
in ((uu____13411), (args)))
in (match (uu____13404) with
| (uu____13423, []) -> begin
(

let uu____13426 = (

let uu____13437 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____13437)))
in FStar_Pervasives_Native.Some (uu____13426))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____13458), uu____13459) -> begin
(

let uu____13480 = (FStar_Syntax_Util.head_and_args k)
in (match (uu____13480) with
| (uv1, uv_args) -> begin
(

let uu____13523 = (

let uu____13524 = (FStar_Syntax_Subst.compress uv1)
in uu____13524.FStar_Syntax_Syntax.n)
in (match (uu____13523) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____13534) -> begin
(

let uu____13559 = (pat_vars env [] uv_args)
in (match (uu____13559) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (scope) -> begin
(

let xs1 = (FStar_All.pipe_right args (FStar_List.map (fun uu____13586 -> (

let uu____13587 = (

let uu____13588 = (

let uu____13589 = (

let uu____13594 = (

let uu____13595 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____13595 FStar_Pervasives_Native.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____13594))
in (FStar_Pervasives_Native.fst uu____13589))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.pos)) uu____13588))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____13587)))))
in (

let c1 = (

let uu____13605 = (

let uu____13606 = (

let uu____13611 = (

let uu____13612 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____13612 FStar_Pervasives_Native.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____13611))
in (FStar_Pervasives_Native.fst uu____13606))
in (FStar_Syntax_Syntax.mk_Total uu____13605))
in (

let k' = (FStar_Syntax_Util.arrow xs1 c1)
in (

let uv_sol = (

let uu____13625 = (

let uu____13628 = (

let uu____13629 = (

let uu____13632 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____13632 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Util.residual_tot uu____13629))
in FStar_Pervasives_Native.Some (uu____13628))
in (FStar_Syntax_Util.abs scope k' uu____13625))
in ((FStar_Syntax_Unionfind.change uvar uv_sol);
FStar_Pervasives_Native.Some (((xs1), (c1)));
)))))
end))
end
| uu____13650 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_app (uu____13655), uu____13656) -> begin
(

let uu____13675 = (FStar_Syntax_Util.head_and_args k)
in (match (uu____13675) with
| (uv1, uv_args) -> begin
(

let uu____13718 = (

let uu____13719 = (FStar_Syntax_Subst.compress uv1)
in uu____13719.FStar_Syntax_Syntax.n)
in (match (uu____13718) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____13729) -> begin
(

let uu____13754 = (pat_vars env [] uv_args)
in (match (uu____13754) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (scope) -> begin
(

let xs1 = (FStar_All.pipe_right args (FStar_List.map (fun uu____13781 -> (

let uu____13782 = (

let uu____13783 = (

let uu____13784 = (

let uu____13789 = (

let uu____13790 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____13790 FStar_Pervasives_Native.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____13789))
in (FStar_Pervasives_Native.fst uu____13784))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.pos)) uu____13783))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____13782)))))
in (

let c1 = (

let uu____13800 = (

let uu____13801 = (

let uu____13806 = (

let uu____13807 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____13807 FStar_Pervasives_Native.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____13806))
in (FStar_Pervasives_Native.fst uu____13801))
in (FStar_Syntax_Syntax.mk_Total uu____13800))
in (

let k' = (FStar_Syntax_Util.arrow xs1 c1)
in (

let uv_sol = (

let uu____13820 = (

let uu____13823 = (

let uu____13824 = (

let uu____13827 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____13827 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Util.residual_tot uu____13824))
in FStar_Pervasives_Native.Some (uu____13823))
in (FStar_Syntax_Util.abs scope k' uu____13820))
in ((FStar_Syntax_Unionfind.change uvar uv_sol);
FStar_Pervasives_Native.Some (((xs1), (c1)));
)))))
end))
end
| uu____13845 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs1, c1), uu____13852) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs1)
in (match ((n_xs = n_args)) with
| true -> begin
(

let uu____13893 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (FStar_All.pipe_right uu____13893 (fun _0_63 -> FStar_Pervasives_Native.Some (_0_63))))
end
| uu____13912 -> begin
(match ((n_xs < n_args)) with
| true -> begin
(

let uu____13929 = (FStar_Util.first_N n_xs args)
in (match (uu____13929) with
| (args1, rest) -> begin
(

let uu____13958 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (match (uu____13958) with
| (xs2, c2) -> begin
(

let uu____13971 = (elim (FStar_Syntax_Util.comp_result c2) rest)
in (FStar_Util.bind_opt uu____13971 (fun uu____13995 -> (match (uu____13995) with
| (xs', c3) -> begin
FStar_Pervasives_Native.Some ((((FStar_List.append xs2 xs')), (c3)))
end))))
end))
end))
end
| uu____14034 -> begin
(

let uu____14035 = (FStar_Util.first_N n_args xs1)
in (match (uu____14035) with
| (xs2, rest) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c1)))) FStar_Pervasives_Native.None k.FStar_Syntax_Syntax.pos)
in (

let uu____14103 = (

let uu____14108 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs2 uu____14108))
in (FStar_All.pipe_right uu____14103 (fun _0_64 -> FStar_Pervasives_Native.Some (_0_64)))))
end))
end)
end)))
end
| uu____14123 -> begin
(

let uu____14130 = (

let uu____14131 = (FStar_Syntax_Print.uvar_to_string uv)
in (

let uu____14132 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____14133 = (FStar_Syntax_Print.term_to_string k_uv1)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" uu____14131 uu____14132 uu____14133))))
in (failwith uu____14130))
end)))
in (

let uu____14140 = (elim k_uv1 ps)
in (FStar_Util.bind_opt uu____14140 (fun uu____14195 -> (match (uu____14195) with
| (xs1, c1) -> begin
(

let uu____14244 = (

let uu____14285 = (decompose env t2)
in ((((((uv), (k_uv1))), (xs1), (c1))), (ps), (uu____14285)))
in FStar_Pervasives_Native.Some (uu____14244))
end))))))
end)
end)))
in (

let rec imitate_or_project = (fun n1 stopt i -> (match (((i >= n1) || (FStar_Option.isNone stopt))) with
| true -> begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end
| uu____14400 -> begin
(

let st = (FStar_Option.get stopt)
in (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (match ((i = (~- ((Prims.parse_int "1"))))) with
| true -> begin
(

let uu____14403 = (imitate orig env wl1 st)
in (match (uu____14403) with
| Failed (uu____14408) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(imitate_or_project n1 stopt (i + (Prims.parse_int "1")));
)
end
| sol -> begin
sol
end))
end
| uu____14415 -> begin
(

let uu____14416 = (project orig env wl1 i st)
in (match (uu____14416) with
| FStar_Pervasives_Native.None -> begin
((FStar_Syntax_Unionfind.rollback tx);
(imitate_or_project n1 stopt (i + (Prims.parse_int "1")));
)
end
| FStar_Pervasives_Native.Some (Failed (uu____14424)) -> begin
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

let uu____14442 = (FStar_Syntax_Util.head_and_args t21)
in (match (uu____14442) with
| (hd1, uu____14458) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____14479) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____14492) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____14493) -> begin
true
end
| uu____14510 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd1)
in (

let uu____14514 = (FStar_Util.set_is_subset_of fvs_hd fvs1)
in (match (uu____14514) with
| true -> begin
true
end
| uu____14515 -> begin
((

let uu____14517 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14517) with
| true -> begin
(

let uu____14518 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" uu____14518))
end
| uu____14519 -> begin
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

let uu____14527 = (

let uu____14530 = (FStar_Syntax_Util.head_and_args t21)
in (FStar_All.pipe_right uu____14530 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____14527 FStar_Syntax_Free.names))
in (

let uu____14575 = (FStar_Util.set_is_empty fvs_hd)
in (match (uu____14575) with
| true -> begin
(~- ((Prims.parse_int "1")))
end
| uu____14576 -> begin
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

let uu____14586 = (occurs_check env wl1 ((uv), (k_uv)) t21)
in (match (uu____14586) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____14599 = (

let uu____14600 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____14600))
in (giveup_or_defer1 orig uu____14599))
end
| uu____14601 -> begin
(

let uu____14602 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____14602) with
| true -> begin
(

let uu____14603 = (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t21)) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))
in (match (uu____14603) with
| true -> begin
(

let uu____14604 = (subterms args_lhs)
in (imitate' orig env wl1 uu____14604))
end
| uu____14607 -> begin
((

let uu____14609 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14609) with
| true -> begin
(

let uu____14610 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____14611 = (names_to_string fvs1)
in (

let uu____14612 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" uu____14610 uu____14611 uu____14612))))
end
| uu____14613 -> begin
()
end));
(

let sol = (match (vars) with
| [] -> begin
t21
end
| uu____14619 -> begin
(

let uu____14620 = (sn_binders env vars)
in (u_abs k_uv uu____14620 t21))
end)
in (

let wl2 = (solve_prob orig FStar_Pervasives_Native.None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl1)
in (solve env wl2)));
)
end))
end
| uu____14632 -> begin
(match ((((not (patterns_only)) && wl1.defer_ok) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl1))
end
| uu____14633 -> begin
(

let uu____14634 = ((not (patterns_only)) && (check_head fvs1 t21))
in (match (uu____14634) with
| true -> begin
((

let uu____14636 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14636) with
| true -> begin
(

let uu____14637 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____14638 = (names_to_string fvs1)
in (

let uu____14639 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" uu____14637 uu____14638 uu____14639))))
end
| uu____14640 -> begin
()
end));
(

let uu____14641 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____14641 (~- ((Prims.parse_int "1")))));
)
end
| uu____14650 -> begin
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
| uu____14651 -> begin
(

let uu____14652 = (

let uu____14653 = (FStar_Syntax_Free.names t1)
in (check_head uu____14653 t2))
in (match (uu____14652) with
| true -> begin
(

let im_ok = (imitate_ok t2)
in ((

let uu____14658 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14658) with
| true -> begin
(

let uu____14659 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" uu____14659 (match ((im_ok < (Prims.parse_int "0"))) with
| true -> begin
"imitating"
end
| uu____14660 -> begin
"projecting"
end)))
end
| uu____14661 -> begin
()
end));
(

let uu____14662 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____14662 im_ok));
))
end
| uu____14671 -> begin
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
| uu____14682 -> begin
(

let force_quasi_pattern = (fun xs_opt uu____14717 -> (match (uu____14717) with
| (t, u, k, args) -> begin
(

let k1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let uu____14767 = (FStar_Syntax_Util.arrow_formals k1)
in (match (uu____14767) with
| (all_formals, uu____14785) -> begin
(

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args1 -> (match (((formals), (args1))) with
| ([], []) -> begin
(

let pat_args1 = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun uu____14948 -> (match (uu____14948) with
| (x, imp) -> begin
(

let uu____14959 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____14959), (imp)))
end))))
in (

let pattern_vars1 = (FStar_List.rev pattern_vars)
in (

let kk = (

let uu____14972 = (FStar_Syntax_Util.type_u ())
in (match (uu____14972) with
| (t1, uu____14978) -> begin
(

let uu____14979 = (new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1 t1)
in (FStar_Pervasives_Native.fst uu____14979))
end))
in (

let uu____14984 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk)
in (match (uu____14984) with
| (t', tm_u1) -> begin
(

let uu____14995 = (destruct_flex_t t')
in (match (uu____14995) with
| (uu____15030, u1, k11, uu____15033) -> begin
(

let sol = (

let uu____15079 = (

let uu____15088 = (u_abs k1 all_formals t')
in ((((u), (k1))), (uu____15088)))
in TERM (uu____15079))
in (

let t_app = (FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in ((sol), (((t_app), (u1), (k11), (pat_args1))))))
end))
end)))))
end
| ((formal)::formals1, (hd1)::tl1) -> begin
(

let uu____15188 = (pat_var_opt env pat_args hd1)
in (match (uu____15188) with
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun uu____15245 -> (match (uu____15245) with
| (x, uu____15251) -> begin
(FStar_Syntax_Syntax.bv_eq x (FStar_Pervasives_Native.fst y))
end))))
end)
in (match ((not (maybe_pat))) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals1 tl1)
end
| uu____15256 -> begin
(

let fvs = (FStar_Syntax_Free.names (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____15260 = (

let uu____15261 = (FStar_Util.set_is_subset_of fvs pattern_var_set)
in (not (uu____15261)))
in (match (uu____15260) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals1 tl1)
end
| uu____15266 -> begin
(

let uu____15267 = (FStar_Util.set_add (FStar_Pervasives_Native.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) uu____15267 formals1 tl1))
end)))
end))
end))
end
| uu____15278 -> begin
(failwith "Impossible")
end))
in (

let uu____15299 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] uu____15299 all_formals args)))
end)))
end))
in (

let solve_both_pats = (fun wl1 uu____15364 uu____15365 r -> (match (((uu____15364), (uu____15365))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
(

let uu____15563 = ((FStar_Syntax_Unionfind.equiv u1 u2) && (binders_eq xs ys))
in (match (uu____15563) with
| true -> begin
(

let uu____15564 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____15564))
end
| uu____15565 -> begin
(

let xs1 = (sn_binders env xs)
in (

let ys1 = (sn_binders env ys)
in (

let zs = (intersect_vars xs1 ys1)
in ((

let uu____15588 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____15588) with
| true -> begin
(

let uu____15589 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____15590 = (FStar_Syntax_Print.binders_to_string ", " ys1)
in (

let uu____15591 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (

let uu____15592 = (FStar_Syntax_Print.term_to_string k1)
in (

let uu____15593 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" uu____15589 uu____15590 uu____15591 uu____15592 uu____15593))))))
end
| uu____15594 -> begin
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

let uu____15653 = (FStar_Syntax_Util.subst_of_list xs2 args)
in (FStar_Syntax_Subst.subst uu____15653 k))
end
| uu____15656 -> begin
(match ((args_len < xs_len)) with
| true -> begin
(

let uu____15667 = (FStar_Util.first_N args_len xs2)
in (match (uu____15667) with
| (xs3, xs_rest) -> begin
(

let k3 = (

let uu____15721 = (FStar_Syntax_Syntax.mk_GTotal k)
in (FStar_Syntax_Util.arrow xs_rest uu____15721))
in (

let uu____15724 = (FStar_Syntax_Util.subst_of_list xs3 args)
in (FStar_Syntax_Subst.subst uu____15724 k3)))
end))
end
| uu____15727 -> begin
(

let uu____15728 = (

let uu____15729 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____15730 = (FStar_Syntax_Print.binders_to_string ", " xs2)
in (

let uu____15731 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" uu____15729 uu____15730 uu____15731))))
in (failwith uu____15728))
end)
end))))
in (

let uu____15732 = (

let uu____15741 = (

let uu____15754 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals uu____15754))
in (match (uu____15741) with
| (bs, k1') -> begin
(

let uu____15781 = (

let uu____15794 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals uu____15794))
in (match (uu____15781) with
| (cs, k2') -> begin
(

let k1'_xs = (subst_k k1' bs args1)
in (

let k2'_ys = (subst_k k2' cs args2)
in (

let sub_prob = (

let uu____15824 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys FStar_Pervasives_Native.None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_65 -> FStar_TypeChecker_Common.TProb (_0_65)) uu____15824))
in (

let uu____15833 = (

let uu____15838 = (

let uu____15839 = (FStar_Syntax_Subst.compress k1')
in uu____15839.FStar_Syntax_Syntax.n)
in (

let uu____15842 = (

let uu____15843 = (FStar_Syntax_Subst.compress k2')
in uu____15843.FStar_Syntax_Syntax.n)
in ((uu____15838), (uu____15842))))
in (match (uu____15833) with
| (FStar_Syntax_Syntax.Tm_type (uu____15854), uu____15855) -> begin
((k1'), ((sub_prob)::[]))
end
| (uu____15860, FStar_Syntax_Syntax.Tm_type (uu____15861)) -> begin
((k2'), ((sub_prob)::[]))
end
| uu____15866 -> begin
(

let uu____15871 = (FStar_Syntax_Util.type_u ())
in (match (uu____15871) with
| (t, uu____15885) -> begin
(

let uu____15886 = (new_uvar r zs t)
in (match (uu____15886) with
| (k_zs, uu____15900) -> begin
(

let kprob = (

let uu____15902 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k_zs FStar_Pervasives_Native.None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_66 -> FStar_TypeChecker_Common.TProb (_0_66)) uu____15902))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end)))))
end))
end))
in (match (uu____15732) with
| (k_u', sub_probs) -> begin
(

let uu____15923 = (

let uu____15934 = (

let uu____15935 = (new_uvar r zs k_u')
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____15935))
in (

let uu____15944 = (

let uu____15947 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs1 uu____15947))
in (

let uu____15950 = (

let uu____15953 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys1 uu____15953))
in ((uu____15934), (uu____15944), (uu____15950)))))
in (match (uu____15923) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs1 u_zs)
in (

let uu____15972 = (occurs_check env wl1 ((u1), (k1)) sub1)
in (match (uu____15972) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occcurs check")
end
| uu____15985 -> begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in (

let uu____15991 = (FStar_Syntax_Unionfind.equiv u1 u2)
in (match (uu____15991) with
| true -> begin
(

let wl2 = (solve_prob orig FStar_Pervasives_Native.None ((sol1)::[]) wl1)
in (solve env wl2))
end
| uu____15993 -> begin
(

let sub2 = (u_abs knew2 ys1 u_zs)
in (

let uu____15995 = (occurs_check env wl1 ((u2), (k2)) sub2)
in (match (uu____15995) with
| (occurs_ok1, msg1) -> begin
(match ((not (occurs_ok1))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occurs check")
end
| uu____16008 -> begin
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

let solve_one_pat = (fun uu____16048 uu____16049 -> (match (((uu____16048), (uu____16049))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
((

let uu____16167 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____16167) with
| true -> begin
(

let uu____16168 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____16169 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" uu____16168 uu____16169)))
end
| uu____16170 -> begin
()
end));
(

let uu____16171 = (FStar_Syntax_Unionfind.equiv u1 u2)
in (match (uu____16171) with
| true -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____16190 uu____16191 -> (match (((uu____16190), (uu____16191))) with
| ((a, uu____16209), (t21, uu____16211)) -> begin
(

let uu____16220 = (

let uu____16225 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig uu____16225 FStar_TypeChecker_Common.EQ t21 FStar_Pervasives_Native.None "flex-flex index"))
in (FStar_All.pipe_right uu____16220 (fun _0_67 -> FStar_TypeChecker_Common.TProb (_0_67))))
end)) xs args2)
in (

let guard = (

let uu____16231 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) FStar_Pervasives_Native.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____16231))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))))
end
| uu____16241 -> begin
(

let t21 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t21)
in (

let uu____16246 = (occurs_check env wl ((u1), (k1)) t21)
in (match (uu____16246) with
| (occurs_ok, uu____16254) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in (

let uu____16262 = (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars))
in (match (uu____16262) with
| true -> begin
(

let sol = (

let uu____16264 = (

let uu____16273 = (u_abs k1 xs t21)
in ((((u1), (k1))), (uu____16273)))
in TERM (uu____16264))
in (

let wl1 = (solve_prob orig FStar_Pervasives_Native.None ((sol)::[]) wl)
in (solve env wl1)))
end
| uu____16279 -> begin
(

let uu____16280 = (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok))
in (match (uu____16280) with
| true -> begin
(

let uu____16281 = (force_quasi_pattern (FStar_Pervasives_Native.Some (xs)) ((t21), (u2), (k2), (args2)))
in (match (uu____16281) with
| (sol, (uu____16299, u21, k21, ys)) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____16313 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____16313) with
| true -> begin
(

let uu____16314 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" uu____16314))
end
| uu____16315 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____16321 -> begin
(giveup env "impossible" orig)
end);
))
end))
end
| uu____16322 -> begin
(giveup_or_defer1 orig "flex-flex constraint")
end))
end)))
end))))
end));
)
end))
in (

let uu____16323 = lhs
in (match (uu____16323) with
| (t1, u1, k1, args1) -> begin
(

let uu____16328 = rhs
in (match (uu____16328) with
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
| uu____16368 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: neither side is a pattern")
end
| uu____16377 -> begin
(

let uu____16378 = (force_quasi_pattern FStar_Pervasives_Native.None ((t1), (u1), (k1), (args1)))
in (match (uu____16378) with
| (sol, uu____16390) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____16393 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____16393) with
| true -> begin
(

let uu____16394 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" uu____16394))
end
| uu____16395 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____16401 -> begin
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

let uu____16403 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____16403) with
| true -> begin
(

let uu____16404 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____16404))
end
| uu____16405 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in (

let uu____16408 = (FStar_Util.physical_equality t1 t2)
in (match (uu____16408) with
| true -> begin
(

let uu____16409 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____16409))
end
| uu____16410 -> begin
((

let uu____16412 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____16412) with
| true -> begin
(

let uu____16413 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" uu____16413))
end
| uu____16414 -> begin
()
end));
(

let r = (FStar_TypeChecker_Env.get_range env)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_ascribed (uu____16416), uu____16417) -> begin
(

let uu____16444 = (

let uu___171_16445 = problem
in (

let uu____16446 = (FStar_Syntax_Util.unmeta t1)
in {FStar_TypeChecker_Common.pid = uu___171_16445.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____16446; FStar_TypeChecker_Common.relation = uu___171_16445.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___171_16445.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___171_16445.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___171_16445.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___171_16445.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___171_16445.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___171_16445.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___171_16445.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____16444 wl))
end
| (FStar_Syntax_Syntax.Tm_meta (uu____16447), uu____16448) -> begin
(

let uu____16455 = (

let uu___171_16456 = problem
in (

let uu____16457 = (FStar_Syntax_Util.unmeta t1)
in {FStar_TypeChecker_Common.pid = uu___171_16456.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____16457; FStar_TypeChecker_Common.relation = uu___171_16456.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___171_16456.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___171_16456.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___171_16456.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___171_16456.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___171_16456.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___171_16456.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___171_16456.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____16455 wl))
end
| (uu____16458, FStar_Syntax_Syntax.Tm_ascribed (uu____16459)) -> begin
(

let uu____16486 = (

let uu___172_16487 = problem
in (

let uu____16488 = (FStar_Syntax_Util.unmeta t2)
in {FStar_TypeChecker_Common.pid = uu___172_16487.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___172_16487.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___172_16487.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____16488; FStar_TypeChecker_Common.element = uu___172_16487.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___172_16487.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___172_16487.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___172_16487.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___172_16487.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___172_16487.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____16486 wl))
end
| (uu____16489, FStar_Syntax_Syntax.Tm_meta (uu____16490)) -> begin
(

let uu____16497 = (

let uu___172_16498 = problem
in (

let uu____16499 = (FStar_Syntax_Util.unmeta t2)
in {FStar_TypeChecker_Common.pid = uu___172_16498.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___172_16498.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___172_16498.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____16499; FStar_TypeChecker_Common.element = uu___172_16498.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___172_16498.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___172_16498.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___172_16498.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___172_16498.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___172_16498.FStar_TypeChecker_Common.rank}))
in (solve_t' env uu____16497 wl))
end
| (FStar_Syntax_Syntax.Tm_bvar (uu____16500), uu____16501) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (uu____16502, FStar_Syntax_Syntax.Tm_bvar (uu____16503)) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (FStar_Syntax_Syntax.Tm_type (u1), FStar_Syntax_Syntax.Tm_type (u2)) -> begin
(solve_one_universe_eq env orig u1 u2 wl)
end
| (FStar_Syntax_Syntax.Tm_arrow (bs1, c1), FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) -> begin
(

let mk_c = (fun c uu___136_16558 -> (match (uu___136_16558) with
| [] -> begin
c
end
| bs -> begin
(

let uu____16580 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____16580))
end))
in (

let uu____16589 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____16589) with
| ((bs11, c11), (bs21, c21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let c12 = (FStar_Syntax_Subst.subst_comp subst1 c11)
in (

let c22 = (FStar_Syntax_Subst.subst_comp subst1 c21)
in (

let rel = (

let uu____16731 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____16731) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____16732 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (

let uu____16733 = (mk_problem scope orig c12 rel c22 FStar_Pervasives_Native.None "function co-domain")
in (FStar_All.pipe_left (fun _0_68 -> FStar_TypeChecker_Common.CProb (_0_68)) uu____16733)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___137_16809 -> (match (uu___137_16809) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____16843 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____16843) with
| ((bs11, tbody11), (bs21, tbody21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let uu____16979 = (

let uu____16984 = (FStar_Syntax_Subst.subst subst1 tbody11)
in (

let uu____16985 = (FStar_Syntax_Subst.subst subst1 tbody21)
in (mk_problem scope orig uu____16984 problem.FStar_TypeChecker_Common.relation uu____16985 FStar_Pervasives_Native.None "lambda co-domain")))
in (FStar_All.pipe_left (fun _0_69 -> FStar_TypeChecker_Common.TProb (_0_69)) uu____16979))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (uu____16990), uu____16991) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____17016) -> begin
true
end
| uu____17033 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____17056 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____17064 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let uu____17067 = (

let uu____17084 = (maybe_eta t1)
in (

let uu____17091 = (maybe_eta t2)
in ((uu____17084), (uu____17091))))
in (match (uu____17067) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___173_17133 = problem
in {FStar_TypeChecker_Common.pid = uu___173_17133.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___173_17133.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___173_17133.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___173_17133.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___173_17133.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___173_17133.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___173_17133.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___173_17133.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____17156 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____17156) with
| true -> begin
(

let uu____17157 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____17157 t_abs wl))
end
| uu____17164 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____17185 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____17185) with
| true -> begin
(

let uu____17186 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____17186 t_abs wl))
end
| uu____17193 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| uu____17194 -> begin
(failwith "Impossible: at least one side is an abstraction")
end))))
end
| (uu____17211, FStar_Syntax_Syntax.Tm_abs (uu____17212)) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____17237) -> begin
true
end
| uu____17254 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____17277 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____17285 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let uu____17288 = (

let uu____17305 = (maybe_eta t1)
in (

let uu____17312 = (maybe_eta t2)
in ((uu____17305), (uu____17312))))
in (match (uu____17288) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___173_17354 = problem
in {FStar_TypeChecker_Common.pid = uu___173_17354.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___173_17354.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___173_17354.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___173_17354.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___173_17354.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___173_17354.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___173_17354.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___173_17354.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____17377 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____17377) with
| true -> begin
(

let uu____17378 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____17378 t_abs wl))
end
| uu____17385 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____17406 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____17406) with
| true -> begin
(

let uu____17407 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____17407 t_abs wl))
end
| uu____17414 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| uu____17415 -> begin
(failwith "Impossible: at least one side is an abstraction")
end))))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____17432), FStar_Syntax_Syntax.Tm_refine (uu____17433)) -> begin
(

let uu____17446 = (as_refinement env wl t1)
in (match (uu____17446) with
| (x1, phi1) -> begin
(

let uu____17453 = (as_refinement env wl t2)
in (match (uu____17453) with
| (x2, phi2) -> begin
(

let base_prob = (

let uu____17461 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _0_70 -> FStar_TypeChecker_Common.TProb (_0_70)) uu____17461))
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

let uu____17499 = (imp phi12 phi22)
in (FStar_All.pipe_right uu____17499 (guard_on_element wl problem x11))))
in (

let fallback = (fun uu____17503 -> (

let impl = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp1 FStar_Syntax_Util.mk_iff phi11 phi21)
end
| uu____17505 -> begin
(mk_imp1 FStar_Syntax_Util.mk_imp phi11 phi21)
end)
in (

let guard = (

let uu____17509 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____17509 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env1 (attempt ((base_prob)::[]) wl1))))))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let ref_prob = (

let uu____17518 = (

let uu____17523 = (

let uu____17524 = (FStar_Syntax_Syntax.mk_binder x11)
in (uu____17524)::(p_scope orig))
in (mk_problem uu____17523 orig phi11 FStar_TypeChecker_Common.EQ phi21 FStar_Pervasives_Native.None "refinement formula"))
in (FStar_All.pipe_left (fun _0_71 -> FStar_TypeChecker_Common.TProb (_0_71)) uu____17518))
in (

let uu____17529 = (solve env1 (

let uu___174_17531 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___174_17531.ctr; defer_ok = false; smt_ok = uu___174_17531.smt_ok; tcenv = uu___174_17531.tcenv}))
in (match (uu____17529) with
| Failed (uu____17538) -> begin
(fallback ())
end
| Success (uu____17543) -> begin
(

let guard = (

let uu____17547 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (

let uu____17552 = (

let uu____17553 = (FStar_All.pipe_right (p_guard ref_prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____17553 (guard_on_element wl problem x11)))
in (FStar_Syntax_Util.mk_conj uu____17547 uu____17552)))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (

let wl2 = (

let uu___175_17562 = wl1
in {attempting = uu___175_17562.attempting; wl_deferred = uu___175_17562.wl_deferred; ctr = (wl1.ctr + (Prims.parse_int "1")); defer_ok = uu___175_17562.defer_ok; smt_ok = uu___175_17562.smt_ok; tcenv = uu___175_17562.tcenv})
in (solve env1 (attempt ((base_prob)::[]) wl2)))))
end)))
end
| uu____17563 -> begin
(fallback ())
end)))))))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____17564), FStar_Syntax_Syntax.Tm_uvar (uu____17565)) -> begin
(

let uu____17598 = (destruct_flex_t t1)
in (

let uu____17599 = (destruct_flex_t t2)
in (flex_flex1 orig uu____17598 uu____17599)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____17600); FStar_Syntax_Syntax.pos = uu____17601; FStar_Syntax_Syntax.vars = uu____17602}, uu____17603), FStar_Syntax_Syntax.Tm_uvar (uu____17604)) -> begin
(

let uu____17657 = (destruct_flex_t t1)
in (

let uu____17658 = (destruct_flex_t t2)
in (flex_flex1 orig uu____17657 uu____17658)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____17659), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____17660); FStar_Syntax_Syntax.pos = uu____17661; FStar_Syntax_Syntax.vars = uu____17662}, uu____17663)) -> begin
(

let uu____17716 = (destruct_flex_t t1)
in (

let uu____17717 = (destruct_flex_t t2)
in (flex_flex1 orig uu____17716 uu____17717)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____17718); FStar_Syntax_Syntax.pos = uu____17719; FStar_Syntax_Syntax.vars = uu____17720}, uu____17721), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____17722); FStar_Syntax_Syntax.pos = uu____17723; FStar_Syntax_Syntax.vars = uu____17724}, uu____17725)) -> begin
(

let uu____17798 = (destruct_flex_t t1)
in (

let uu____17799 = (destruct_flex_t t2)
in (flex_flex1 orig uu____17798 uu____17799)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____17800), uu____17801) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(

let uu____17818 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____17818 t2 wl))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____17825); FStar_Syntax_Syntax.pos = uu____17826; FStar_Syntax_Syntax.vars = uu____17827}, uu____17828), uu____17829) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(

let uu____17866 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____17866 t2 wl))
end
| (uu____17873, FStar_Syntax_Syntax.Tm_uvar (uu____17874)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (uu____17891, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____17892); FStar_Syntax_Syntax.pos = uu____17893; FStar_Syntax_Syntax.vars = uu____17894}, uu____17895)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____17932), FStar_Syntax_Syntax.Tm_type (uu____17933)) -> begin
(solve_t' env (

let uu___176_17951 = problem
in {FStar_TypeChecker_Common.pid = uu___176_17951.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___176_17951.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___176_17951.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___176_17951.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___176_17951.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___176_17951.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___176_17951.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___176_17951.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___176_17951.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____17952); FStar_Syntax_Syntax.pos = uu____17953; FStar_Syntax_Syntax.vars = uu____17954}, uu____17955), FStar_Syntax_Syntax.Tm_type (uu____17956)) -> begin
(solve_t' env (

let uu___176_17994 = problem
in {FStar_TypeChecker_Common.pid = uu___176_17994.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___176_17994.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___176_17994.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___176_17994.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___176_17994.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___176_17994.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___176_17994.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___176_17994.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___176_17994.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____17995), FStar_Syntax_Syntax.Tm_arrow (uu____17996)) -> begin
(solve_t' env (

let uu___176_18026 = problem
in {FStar_TypeChecker_Common.pid = uu___176_18026.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___176_18026.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___176_18026.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___176_18026.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___176_18026.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___176_18026.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___176_18026.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___176_18026.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___176_18026.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____18027); FStar_Syntax_Syntax.pos = uu____18028; FStar_Syntax_Syntax.vars = uu____18029}, uu____18030), FStar_Syntax_Syntax.Tm_arrow (uu____18031)) -> begin
(solve_t' env (

let uu___176_18081 = problem
in {FStar_TypeChecker_Common.pid = uu___176_18081.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___176_18081.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___176_18081.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___176_18081.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___176_18081.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___176_18081.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___176_18081.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___176_18081.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___176_18081.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____18082), uu____18083) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____18100 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____18102 = (

let uu____18103 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____18103))
in (match (uu____18102) with
| true -> begin
(

let uu____18104 = (FStar_All.pipe_left (fun _0_72 -> FStar_TypeChecker_Common.TProb (_0_72)) (

let uu___177_18110 = problem
in {FStar_TypeChecker_Common.pid = uu___177_18110.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___177_18110.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___177_18110.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___177_18110.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___177_18110.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___177_18110.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___177_18110.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___177_18110.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___177_18110.FStar_TypeChecker_Common.rank}))
in (

let uu____18111 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____18104 uu____18111 t2 wl)))
end
| uu____18118 -> begin
(

let uu____18119 = (base_and_refinement env wl t2)
in (match (uu____18119) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18162 = (FStar_All.pipe_left (fun _0_73 -> FStar_TypeChecker_Common.TProb (_0_73)) (

let uu___178_18168 = problem
in {FStar_TypeChecker_Common.pid = uu___178_18168.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___178_18168.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___178_18168.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___178_18168.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___178_18168.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___178_18168.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___178_18168.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___178_18168.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___178_18168.FStar_TypeChecker_Common.rank}))
in (

let uu____18169 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____18162 uu____18169 t_base wl)))
end
| FStar_Pervasives_Native.Some (y, phi) -> begin
(

let y' = (

let uu___179_18189 = y
in {FStar_Syntax_Syntax.ppname = uu___179_18189.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___179_18189.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let base_prob = (

let uu____18192 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_74 -> FStar_TypeChecker_Common.TProb (_0_74)) uu____18192))
in (

let guard = (

let uu____18204 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____18204 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl1)))))))
end)
end))
end)))
end)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____18212); FStar_Syntax_Syntax.pos = uu____18213; FStar_Syntax_Syntax.vars = uu____18214}, uu____18215), uu____18216) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____18253 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____18255 = (

let uu____18256 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____18256))
in (match (uu____18255) with
| true -> begin
(

let uu____18257 = (FStar_All.pipe_left (fun _0_75 -> FStar_TypeChecker_Common.TProb (_0_75)) (

let uu___177_18263 = problem
in {FStar_TypeChecker_Common.pid = uu___177_18263.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___177_18263.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___177_18263.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___177_18263.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___177_18263.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___177_18263.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___177_18263.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___177_18263.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___177_18263.FStar_TypeChecker_Common.rank}))
in (

let uu____18264 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____18257 uu____18264 t2 wl)))
end
| uu____18271 -> begin
(

let uu____18272 = (base_and_refinement env wl t2)
in (match (uu____18272) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18315 = (FStar_All.pipe_left (fun _0_76 -> FStar_TypeChecker_Common.TProb (_0_76)) (

let uu___178_18321 = problem
in {FStar_TypeChecker_Common.pid = uu___178_18321.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___178_18321.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___178_18321.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___178_18321.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___178_18321.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___178_18321.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___178_18321.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___178_18321.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___178_18321.FStar_TypeChecker_Common.rank}))
in (

let uu____18322 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____18315 uu____18322 t_base wl)))
end
| FStar_Pervasives_Native.Some (y, phi) -> begin
(

let y' = (

let uu___179_18342 = y
in {FStar_Syntax_Syntax.ppname = uu___179_18342.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___179_18342.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let base_prob = (

let uu____18345 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_77 -> FStar_TypeChecker_Common.TProb (_0_77)) uu____18345))
in (

let guard = (

let uu____18357 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____18357 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl1)))))))
end)
end))
end)))
end)
end
| (uu____18365, FStar_Syntax_Syntax.Tm_uvar (uu____18366)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| uu____18383 -> begin
(

let uu____18384 = (base_and_refinement env wl t1)
in (match (uu____18384) with
| (t_base, uu____18400) -> begin
(solve_t env (

let uu___180_18422 = problem
in {FStar_TypeChecker_Common.pid = uu___180_18422.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___180_18422.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___180_18422.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___180_18422.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___180_18422.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___180_18422.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___180_18422.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___180_18422.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (uu____18425, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____18426); FStar_Syntax_Syntax.pos = uu____18427; FStar_Syntax_Syntax.vars = uu____18428}, uu____18429)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| uu____18466 -> begin
(

let uu____18467 = (base_and_refinement env wl t1)
in (match (uu____18467) with
| (t_base, uu____18483) -> begin
(solve_t env (

let uu___180_18505 = problem
in {FStar_TypeChecker_Common.pid = uu___180_18505.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___180_18505.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___180_18505.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___180_18505.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___180_18505.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___180_18505.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___180_18505.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___180_18505.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (FStar_Syntax_Syntax.Tm_refine (uu____18508), uu____18509) -> begin
(

let t21 = (

let uu____18519 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement uu____18519))
in (solve_t env (

let uu___181_18543 = problem
in {FStar_TypeChecker_Common.pid = uu___181_18543.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___181_18543.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___181_18543.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___181_18543.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___181_18543.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___181_18543.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___181_18543.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___181_18543.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___181_18543.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____18544, FStar_Syntax_Syntax.Tm_refine (uu____18545)) -> begin
(

let t11 = (

let uu____18555 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement uu____18555))
in (solve_t env (

let uu___182_18579 = problem
in {FStar_TypeChecker_Common.pid = uu___182_18579.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___182_18579.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___182_18579.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___182_18579.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___182_18579.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___182_18579.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___182_18579.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___182_18579.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___182_18579.FStar_TypeChecker_Common.rank}) wl))
end
| (FStar_Syntax_Syntax.Tm_match (uu____18582), uu____18583) -> begin
(

let head1 = (

let uu____18609 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____18609 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____18653 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____18653 FStar_Pervasives_Native.fst))
in (

let uu____18694 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____18694) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____18709 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____18709) with
| true -> begin
(

let guard = (

let uu____18721 = (

let uu____18722 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____18722 = FStar_Syntax_Util.Equal))
in (match (uu____18721) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____18725 -> begin
(

let uu____18726 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_78 -> FStar_Pervasives_Native.Some (_0_78)) uu____18726))
end))
in (

let uu____18729 = (solve_prob orig guard [] wl)
in (solve env uu____18729)))
end
| uu____18730 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____18731 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____18732), uu____18733) -> begin
(

let head1 = (

let uu____18743 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____18743 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____18787 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____18787 FStar_Pervasives_Native.fst))
in (

let uu____18828 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____18828) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____18843 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____18843) with
| true -> begin
(

let guard = (

let uu____18855 = (

let uu____18856 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____18856 = FStar_Syntax_Util.Equal))
in (match (uu____18855) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____18859 -> begin
(

let uu____18860 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_79 -> FStar_Pervasives_Native.Some (_0_79)) uu____18860))
end))
in (

let uu____18863 = (solve_prob orig guard [] wl)
in (solve env uu____18863)))
end
| uu____18864 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____18865 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_name (uu____18866), uu____18867) -> begin
(

let head1 = (

let uu____18871 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____18871 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____18915 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____18915 FStar_Pervasives_Native.fst))
in (

let uu____18956 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____18956) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____18971 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____18971) with
| true -> begin
(

let guard = (

let uu____18983 = (

let uu____18984 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____18984 = FStar_Syntax_Util.Equal))
in (match (uu____18983) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____18987 -> begin
(

let uu____18988 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_80 -> FStar_Pervasives_Native.Some (_0_80)) uu____18988))
end))
in (

let uu____18991 = (solve_prob orig guard [] wl)
in (solve env uu____18991)))
end
| uu____18992 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____18993 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_constant (uu____18994), uu____18995) -> begin
(

let head1 = (

let uu____18999 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____18999 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____19043 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____19043 FStar_Pervasives_Native.fst))
in (

let uu____19084 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____19084) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____19099 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____19099) with
| true -> begin
(

let guard = (

let uu____19111 = (

let uu____19112 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____19112 = FStar_Syntax_Util.Equal))
in (match (uu____19111) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____19115 -> begin
(

let uu____19116 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_81 -> FStar_Pervasives_Native.Some (_0_81)) uu____19116))
end))
in (

let uu____19119 = (solve_prob orig guard [] wl)
in (solve env uu____19119)))
end
| uu____19120 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____19121 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____19122), uu____19123) -> begin
(

let head1 = (

let uu____19127 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____19127 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____19171 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____19171 FStar_Pervasives_Native.fst))
in (

let uu____19212 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____19212) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____19227 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____19227) with
| true -> begin
(

let guard = (

let uu____19239 = (

let uu____19240 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____19240 = FStar_Syntax_Util.Equal))
in (match (uu____19239) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____19243 -> begin
(

let uu____19244 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_82 -> FStar_Pervasives_Native.Some (_0_82)) uu____19244))
end))
in (

let uu____19247 = (solve_prob orig guard [] wl)
in (solve env uu____19247)))
end
| uu____19248 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____19249 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____19250), uu____19251) -> begin
(

let head1 = (

let uu____19269 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____19269 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____19313 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____19313 FStar_Pervasives_Native.fst))
in (

let uu____19354 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____19354) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____19369 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____19369) with
| true -> begin
(

let guard = (

let uu____19381 = (

let uu____19382 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____19382 = FStar_Syntax_Util.Equal))
in (match (uu____19381) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____19385 -> begin
(

let uu____19386 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_83 -> FStar_Pervasives_Native.Some (_0_83)) uu____19386))
end))
in (

let uu____19389 = (solve_prob orig guard [] wl)
in (solve env uu____19389)))
end
| uu____19390 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____19391 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____19392, FStar_Syntax_Syntax.Tm_match (uu____19393)) -> begin
(

let head1 = (

let uu____19419 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____19419 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____19463 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____19463 FStar_Pervasives_Native.fst))
in (

let uu____19504 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____19504) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____19519 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____19519) with
| true -> begin
(

let guard = (

let uu____19531 = (

let uu____19532 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____19532 = FStar_Syntax_Util.Equal))
in (match (uu____19531) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____19535 -> begin
(

let uu____19536 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_84 -> FStar_Pervasives_Native.Some (_0_84)) uu____19536))
end))
in (

let uu____19539 = (solve_prob orig guard [] wl)
in (solve env uu____19539)))
end
| uu____19540 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____19541 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____19542, FStar_Syntax_Syntax.Tm_uinst (uu____19543)) -> begin
(

let head1 = (

let uu____19553 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____19553 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____19597 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____19597 FStar_Pervasives_Native.fst))
in (

let uu____19638 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____19638) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____19653 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____19653) with
| true -> begin
(

let guard = (

let uu____19665 = (

let uu____19666 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____19666 = FStar_Syntax_Util.Equal))
in (match (uu____19665) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____19669 -> begin
(

let uu____19670 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_85 -> FStar_Pervasives_Native.Some (_0_85)) uu____19670))
end))
in (

let uu____19673 = (solve_prob orig guard [] wl)
in (solve env uu____19673)))
end
| uu____19674 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____19675 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____19676, FStar_Syntax_Syntax.Tm_name (uu____19677)) -> begin
(

let head1 = (

let uu____19681 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____19681 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____19725 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____19725 FStar_Pervasives_Native.fst))
in (

let uu____19766 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____19766) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____19781 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____19781) with
| true -> begin
(

let guard = (

let uu____19793 = (

let uu____19794 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____19794 = FStar_Syntax_Util.Equal))
in (match (uu____19793) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____19797 -> begin
(

let uu____19798 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_86 -> FStar_Pervasives_Native.Some (_0_86)) uu____19798))
end))
in (

let uu____19801 = (solve_prob orig guard [] wl)
in (solve env uu____19801)))
end
| uu____19802 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____19803 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____19804, FStar_Syntax_Syntax.Tm_constant (uu____19805)) -> begin
(

let head1 = (

let uu____19809 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____19809 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____19853 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____19853 FStar_Pervasives_Native.fst))
in (

let uu____19894 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____19894) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____19909 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____19909) with
| true -> begin
(

let guard = (

let uu____19921 = (

let uu____19922 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____19922 = FStar_Syntax_Util.Equal))
in (match (uu____19921) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____19925 -> begin
(

let uu____19926 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_87 -> FStar_Pervasives_Native.Some (_0_87)) uu____19926))
end))
in (

let uu____19929 = (solve_prob orig guard [] wl)
in (solve env uu____19929)))
end
| uu____19930 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____19931 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____19932, FStar_Syntax_Syntax.Tm_fvar (uu____19933)) -> begin
(

let head1 = (

let uu____19937 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____19937 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____19981 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____19981 FStar_Pervasives_Native.fst))
in (

let uu____20022 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____20022) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____20037 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____20037) with
| true -> begin
(

let guard = (

let uu____20049 = (

let uu____20050 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____20050 = FStar_Syntax_Util.Equal))
in (match (uu____20049) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____20053 -> begin
(

let uu____20054 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_88 -> FStar_Pervasives_Native.Some (_0_88)) uu____20054))
end))
in (

let uu____20057 = (solve_prob orig guard [] wl)
in (solve env uu____20057)))
end
| uu____20058 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____20059 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____20060, FStar_Syntax_Syntax.Tm_app (uu____20061)) -> begin
(

let head1 = (

let uu____20079 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____20079 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____20123 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____20123 FStar_Pervasives_Native.fst))
in (

let uu____20164 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____20164) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____20179 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____20179) with
| true -> begin
(

let guard = (

let uu____20191 = (

let uu____20192 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____20192 = FStar_Syntax_Util.Equal))
in (match (uu____20191) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____20195 -> begin
(

let uu____20196 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_89 -> FStar_Pervasives_Native.Some (_0_89)) uu____20196))
end))
in (

let uu____20199 = (solve_prob orig guard [] wl)
in (solve env uu____20199)))
end
| uu____20200 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____20201 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_let (uu____20202), uu____20203) -> begin
(

let uu____20216 = (

let uu____20217 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____20218 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____20217 uu____20218)))
in (failwith uu____20216))
end
| (FStar_Syntax_Syntax.Tm_delayed (uu____20219), uu____20220) -> begin
(

let uu____20245 = (

let uu____20246 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____20247 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____20246 uu____20247)))
in (failwith uu____20245))
end
| (uu____20248, FStar_Syntax_Syntax.Tm_delayed (uu____20249)) -> begin
(

let uu____20274 = (

let uu____20275 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____20276 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____20275 uu____20276)))
in (failwith uu____20274))
end
| (uu____20277, FStar_Syntax_Syntax.Tm_let (uu____20278)) -> begin
(

let uu____20291 = (

let uu____20292 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____20293 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____20292 uu____20293)))
in (failwith uu____20291))
end
| uu____20294 -> begin
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

let uu____20330 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____20330) with
| true -> begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end
| uu____20331 -> begin
()
end));
(match ((not ((FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)))) with
| true -> begin
(

let uu____20332 = (

let uu____20333 = (FStar_Syntax_Print.lid_to_string c1_comp.FStar_Syntax_Syntax.effect_name)
in (

let uu____20334 = (FStar_Syntax_Print.lid_to_string c2_comp.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible effects: %s <> %s" uu____20333 uu____20334)))
in (giveup env uu____20332 orig))
end
| uu____20335 -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____20354 uu____20355 -> (match (((uu____20354), (uu____20355))) with
| ((a1, uu____20373), (a2, uu____20375)) -> begin
(

let uu____20384 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _0_90 -> FStar_TypeChecker_Common.TProb (_0_90)) uu____20384))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (

let uu____20394 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) FStar_Pervasives_Native.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____20394))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))))
end);
))
in (

let solve_sub = (fun c11 edge c21 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let lift_c1 = (fun uu____20418 -> (

let wp = (match (c11.FStar_Syntax_Syntax.effect_args) with
| ((wp1, uu____20425))::[] -> begin
wp1
end
| uu____20442 -> begin
(

let uu____20451 = (

let uu____20452 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c11.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" uu____20452))
in (failwith uu____20451))
end)
in (

let uu____20455 = (

let uu____20464 = (

let uu____20465 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c11.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____20465))
in (uu____20464)::[])
in {FStar_Syntax_Syntax.comp_univs = c11.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c21.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c11.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____20455; FStar_Syntax_Syntax.flags = c11.FStar_Syntax_Syntax.flags})))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____20466 = (lift_c1 ())
in (solve_eq uu____20466 c21))
end
| uu____20467 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___138_20472 -> (match (uu___138_20472) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| uu____20473 -> begin
false
end))))
in (

let uu____20474 = (match (((c11.FStar_Syntax_Syntax.effect_args), (c21.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____20508))::uu____20509, ((wp2, uu____20511))::uu____20512) -> begin
((wp1), (wp2))
end
| uu____20569 -> begin
(

let uu____20590 = (

let uu____20591 = (

let uu____20596 = (

let uu____20597 = (FStar_Syntax_Print.lid_to_string c11.FStar_Syntax_Syntax.effect_name)
in (

let uu____20598 = (FStar_Syntax_Print.lid_to_string c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____20597 uu____20598)))
in ((uu____20596), (env.FStar_TypeChecker_Env.range)))
in FStar_Errors.Error (uu____20591))
in (FStar_Exn.raise uu____20590))
end)
in (match (uu____20474) with
| (wpc1, wpc2) -> begin
(

let uu____20617 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____20617) with
| true -> begin
(

let uu____20620 = (problem_using_guard orig c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ FStar_Pervasives_Native.None "result type")
in (solve_t env uu____20620 wl))
end
| uu____20623 -> begin
(

let uu____20624 = (

let uu____20631 = (FStar_TypeChecker_Env.effect_decl_opt env c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.must uu____20631))
in (match (uu____20624) with
| (c2_decl, qualifiers) -> begin
(

let uu____20652 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____20652) with
| true -> begin
(

let c1_repr = (

let uu____20656 = (

let uu____20657 = (

let uu____20658 = (lift_c1 ())
in (FStar_Syntax_Syntax.mk_Comp uu____20658))
in (

let uu____20659 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____20657 uu____20659)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____20656))
in (

let c2_repr = (

let uu____20661 = (

let uu____20662 = (FStar_Syntax_Syntax.mk_Comp c21)
in (

let uu____20663 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____20662 uu____20663)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____20661))
in (

let prob = (

let uu____20665 = (

let uu____20670 = (

let uu____20671 = (FStar_Syntax_Print.term_to_string c1_repr)
in (

let uu____20672 = (FStar_Syntax_Print.term_to_string c2_repr)
in (FStar_Util.format2 "sub effect repr: %s <: %s" uu____20671 uu____20672)))
in (sub_prob c1_repr problem.FStar_TypeChecker_Common.relation c2_repr uu____20670))
in FStar_TypeChecker_Common.TProb (uu____20665))
in (

let wl1 = (

let uu____20674 = (

let uu____20677 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in FStar_Pervasives_Native.Some (uu____20677))
in (solve_prob orig uu____20674 [] wl))
in (solve env (attempt ((prob)::[]) wl1))))))
end
| uu____20682 -> begin
(

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____20684 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____20686 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____20686) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____20687 -> begin
()
end));
(

let uu____20688 = (

let uu____20691 = (

let uu____20692 = (

let uu____20707 = (

let uu____20708 = (

let uu____20709 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (uu____20709)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____20708 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (

let uu____20710 = (

let uu____20713 = (FStar_Syntax_Syntax.as_arg c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____20714 = (

let uu____20717 = (

let uu____20718 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____20718))
in (uu____20717)::[])
in (uu____20713)::uu____20714))
in ((uu____20707), (uu____20710))))
in FStar_Syntax_Syntax.Tm_app (uu____20692))
in (FStar_Syntax_Syntax.mk uu____20691))
in (uu____20688 FStar_Pervasives_Native.None r));
)
end
| uu____20724 -> begin
(

let uu____20725 = (

let uu____20728 = (

let uu____20729 = (

let uu____20744 = (

let uu____20745 = (

let uu____20746 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (uu____20746)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____20745 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (

let uu____20747 = (

let uu____20750 = (FStar_Syntax_Syntax.as_arg c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____20751 = (

let uu____20754 = (FStar_Syntax_Syntax.as_arg wpc2)
in (

let uu____20755 = (

let uu____20758 = (

let uu____20759 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____20759))
in (uu____20758)::[])
in (uu____20754)::uu____20755))
in (uu____20750)::uu____20751))
in ((uu____20744), (uu____20747))))
in FStar_Syntax_Syntax.Tm_app (uu____20729))
in (FStar_Syntax_Syntax.mk uu____20728))
in (uu____20725 FStar_Pervasives_Native.None r))
end)
end)
in (

let base_prob = (

let uu____20766 = (sub_prob c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _0_91 -> FStar_TypeChecker_Common.TProb (_0_91)) uu____20766))
in (

let wl1 = (

let uu____20776 = (

let uu____20779 = (

let uu____20782 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____20782 g))
in (FStar_All.pipe_left (fun _0_92 -> FStar_Pervasives_Native.Some (_0_92)) uu____20779))
in (solve_prob orig uu____20776 [] wl))
in (solve env (attempt ((base_prob)::[]) wl1)))))
end))
end))
end))
end)))
end))))
in (

let uu____20795 = (FStar_Util.physical_equality c1 c2)
in (match (uu____20795) with
| true -> begin
(

let uu____20796 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____20796))
end
| uu____20797 -> begin
((

let uu____20799 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____20799) with
| true -> begin
(

let uu____20800 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____20801 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____20800 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____20801)))
end
| uu____20802 -> begin
()
end));
(

let uu____20803 = (

let uu____20808 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____20809 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____20808), (uu____20809))))
in (match (uu____20803) with
| (c11, c21) -> begin
(match (((c11.FStar_Syntax_Syntax.n), (c21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____20813), FStar_Syntax_Syntax.Total (t2, uu____20815)) when (FStar_Syntax_Util.non_informative t2) -> begin
(

let uu____20832 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____20832 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____20835), FStar_Syntax_Syntax.Total (uu____20836)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| (FStar_Syntax_Syntax.Total (t1, uu____20854), FStar_Syntax_Syntax.Total (t2, uu____20856)) -> begin
(

let uu____20873 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____20873 wl))
end
| (FStar_Syntax_Syntax.GTotal (t1, uu____20877), FStar_Syntax_Syntax.GTotal (t2, uu____20879)) -> begin
(

let uu____20896 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____20896 wl))
end
| (FStar_Syntax_Syntax.Total (t1, uu____20900), FStar_Syntax_Syntax.GTotal (t2, uu____20902)) -> begin
(

let uu____20919 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____20919 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____20922), FStar_Syntax_Syntax.Comp (uu____20923)) -> begin
(

let uu____20932 = (

let uu___183_20937 = problem
in (

let uu____20942 = (

let uu____20943 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____20943))
in {FStar_TypeChecker_Common.pid = uu___183_20937.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____20942; FStar_TypeChecker_Common.relation = uu___183_20937.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___183_20937.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___183_20937.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___183_20937.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___183_20937.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___183_20937.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___183_20937.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___183_20937.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____20932 wl))
end
| (FStar_Syntax_Syntax.Total (uu____20944), FStar_Syntax_Syntax.Comp (uu____20945)) -> begin
(

let uu____20954 = (

let uu___183_20959 = problem
in (

let uu____20964 = (

let uu____20965 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____20965))
in {FStar_TypeChecker_Common.pid = uu___183_20959.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____20964; FStar_TypeChecker_Common.relation = uu___183_20959.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___183_20959.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___183_20959.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___183_20959.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___183_20959.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___183_20959.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___183_20959.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___183_20959.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____20954 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____20966), FStar_Syntax_Syntax.GTotal (uu____20967)) -> begin
(

let uu____20976 = (

let uu___184_20981 = problem
in (

let uu____20986 = (

let uu____20987 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____20987))
in {FStar_TypeChecker_Common.pid = uu___184_20981.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___184_20981.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___184_20981.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____20986; FStar_TypeChecker_Common.element = uu___184_20981.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___184_20981.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___184_20981.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___184_20981.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___184_20981.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___184_20981.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____20976 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____20988), FStar_Syntax_Syntax.Total (uu____20989)) -> begin
(

let uu____20998 = (

let uu___184_21003 = problem
in (

let uu____21008 = (

let uu____21009 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____21009))
in {FStar_TypeChecker_Common.pid = uu___184_21003.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___184_21003.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___184_21003.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____21008; FStar_TypeChecker_Common.element = uu___184_21003.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___184_21003.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___184_21003.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___184_21003.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___184_21003.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___184_21003.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____20998 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____21010), FStar_Syntax_Syntax.Comp (uu____21011)) -> begin
(

let uu____21012 = ((((FStar_Syntax_Util.is_ml_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) || ((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_total_comp c21))) || (((FStar_Syntax_Util.is_total_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB)))
in (match (uu____21012) with
| true -> begin
(

let uu____21013 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c11) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c21) FStar_Pervasives_Native.None "result type")
in (solve_t env uu____21013 wl))
end
| uu____21016 -> begin
(

let c1_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (

let c2_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____21019 = (match ((FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) with
| true -> begin
((c1_comp), (c2_comp))
end
| uu____21028 -> begin
(

let uu____21029 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let uu____21030 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((uu____21029), (uu____21030))))
end)
in (match (uu____21019) with
| (c1_comp1, c2_comp1) -> begin
(solve_eq c1_comp1 c2_comp1)
end))
end
| uu____21033 -> begin
(

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((

let uu____21037 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____21037) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c12.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c22.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____21038 -> begin
()
end));
(

let uu____21039 = (FStar_TypeChecker_Env.monad_leq env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____21039) with
| FStar_Pervasives_Native.None -> begin
(

let uu____21042 = (((FStar_Syntax_Util.is_ghost_effect c12.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c22.FStar_Syntax_Syntax.effect_name)) && (

let uu____21044 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c22.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative uu____21044)))
in (match (uu____21042) with
| true -> begin
(

let edge = {FStar_TypeChecker_Env.msource = c12.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c22.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = FStar_TypeChecker_Env.identity_mlift}
in (solve_sub c12 edge c22))
end
| uu____21046 -> begin
(

let uu____21047 = (

let uu____21048 = (FStar_Syntax_Print.lid_to_string c12.FStar_Syntax_Syntax.effect_name)
in (

let uu____21049 = (FStar_Syntax_Print.lid_to_string c22.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____21048 uu____21049)))
in (giveup env uu____21047 orig))
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

let uu____21055 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____21093 -> (match (uu____21093) with
| (uu____21106, uu____21107, u, uu____21109, uu____21110, uu____21111) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____21055 (FStar_String.concat ", "))))


let ineqs_to_string : (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.string = (fun ineqs -> (

let vars = (

let uu____21143 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs) (FStar_List.map FStar_Syntax_Print.univ_to_string))
in (FStar_All.pipe_right uu____21143 (FStar_String.concat ", ")))
in (

let ineqs1 = (

let uu____21161 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs) (FStar_List.map (fun uu____21189 -> (match (uu____21189) with
| (u1, u2) -> begin
(

let uu____21196 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____21197 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "%s < %s" uu____21196 uu____21197)))
end))))
in (FStar_All.pipe_right uu____21161 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred), (g.FStar_TypeChecker_Env.univ_ineqs))) with
| (FStar_TypeChecker_Common.Trivial, [], (uu____21216, [])) -> begin
"{}"
end
| uu____21241 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____21258 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____21258) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____21259 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____21261 = (FStar_List.map (fun uu____21271 -> (match (uu____21271) with
| (uu____21276, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right uu____21261 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (

let uu____21281 = (ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs)
in (FStar_Util.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n" form carry uu____21281 imps)))))
end))


let new_t_problem : 'Auu____21296 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  'Auu____21296 FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term, 'Auu____21296) FStar_TypeChecker_Common.problem = (fun env lhs rel rhs elt loc -> (

let reason = (

let uu____21330 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____21330) with
| true -> begin
(

let uu____21331 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____21332 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21331 (rel_to_string rel) uu____21332)))
end
| uu____21333 -> begin
"TOP"
end))
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (

let uu____21360 = (

let uu____21363 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_93 -> FStar_Pervasives_Native.Some (_0_93)) uu____21363))
in (FStar_Syntax_Syntax.new_bv uu____21360 t1))
in (

let env1 = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (

let uu____21372 = (

let uu____21375 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _0_94 -> FStar_Pervasives_Native.Some (_0_94)) uu____21375))
in (

let uu____21378 = (FStar_TypeChecker_Env.get_range env1)
in (new_t_problem env1 t1 rel t2 uu____21372 uu____21378)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option = (fun env probs err1 -> (

let probs1 = (

let uu____21411 = (FStar_Options.eager_inference ())
in (match (uu____21411) with
| true -> begin
(

let uu___185_21412 = probs
in {attempting = uu___185_21412.attempting; wl_deferred = uu___185_21412.wl_deferred; ctr = uu___185_21412.ctr; defer_ok = false; smt_ok = uu___185_21412.smt_ok; tcenv = uu___185_21412.tcenv})
end
| uu____21413 -> begin
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

let uu____21424 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____21424) with
| true -> begin
(

let uu____21425 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____21425))
end
| uu____21426 -> begin
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

let uu____21437 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____21437) with
| true -> begin
(

let uu____21438 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____21438))
end
| uu____21439 -> begin
()
end));
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env f)
in ((

let uu____21442 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____21442) with
| true -> begin
(

let uu____21443 = (FStar_Syntax_Print.term_to_string f1)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____21443))
end
| uu____21444 -> begin
()
end));
(

let f2 = (

let uu____21446 = (

let uu____21447 = (FStar_Syntax_Util.unmeta f1)
in uu____21447.FStar_Syntax_Syntax.n)
in (match (uu____21446) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____21451 -> begin
FStar_TypeChecker_Common.NonTrivial (f1)
end))
in (

let uu___186_21452 = g
in {FStar_TypeChecker_Env.guard_f = f2; FStar_TypeChecker_Env.deferred = uu___186_21452.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___186_21452.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___186_21452.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____21474 = (

let uu____21475 = (

let uu____21476 = (

let uu____21477 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____21477 (fun _0_95 -> FStar_TypeChecker_Common.NonTrivial (_0_95))))
in {FStar_TypeChecker_Env.guard_f = uu____21476; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env uu____21475))
in (FStar_All.pipe_left (fun _0_96 -> FStar_Pervasives_Native.Some (_0_96)) uu____21474))
end))


let with_guard_no_simp : 'Auu____21508 . 'Auu____21508  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____21528 = (

let uu____21529 = (

let uu____21530 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____21530 (fun _0_97 -> FStar_TypeChecker_Common.NonTrivial (_0_97))))
in {FStar_TypeChecker_Env.guard_f = uu____21529; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in FStar_Pervasives_Native.Some (uu____21528))
end))


let try_teq : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun smt_ok env t1 t2 -> ((

let uu____21572 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____21572) with
| true -> begin
(

let uu____21573 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____21574 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" uu____21573 uu____21574)))
end
| uu____21575 -> begin
()
end));
(

let prob = (

let uu____21577 = (

let uu____21582 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None uu____21582))
in (FStar_All.pipe_left (fun _0_98 -> FStar_TypeChecker_Common.TProb (_0_98)) uu____21577))
in (

let g = (

let uu____21590 = (

let uu____21593 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____21593 (fun uu____21595 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____21590))
in g));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____21616 = (try_teq true env t1 t2)
in (match (uu____21616) with
| FStar_Pervasives_Native.None -> begin
(

let uu____21619 = (

let uu____21620 = (

let uu____21625 = (FStar_TypeChecker_Err.basic_type_error env FStar_Pervasives_Native.None t2 t1)
in (

let uu____21626 = (FStar_TypeChecker_Env.get_range env)
in ((uu____21625), (uu____21626))))
in FStar_Errors.Error (uu____21620))
in (FStar_Exn.raise uu____21619))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____21629 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____21629) with
| true -> begin
(

let uu____21630 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____21631 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____21632 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____21630 uu____21631 uu____21632))))
end
| uu____21633 -> begin
()
end));
g;
)
end)))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 smt_ok -> ((

let uu____21653 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____21653) with
| true -> begin
(

let uu____21654 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____21655 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" uu____21654 uu____21655)))
end
| uu____21656 -> begin
()
end));
(

let uu____21657 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____21657) with
| (prob, x) -> begin
(

let g = (

let uu____21669 = (

let uu____21672 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____21672 (fun uu____21674 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____21669))
in ((

let uu____21684 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____21684) with
| true -> begin
(

let uu____21685 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____21686 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____21687 = (

let uu____21688 = (FStar_Util.must g)
in (guard_to_string env uu____21688))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" uu____21685 uu____21686 uu____21687))))
end
| uu____21689 -> begin
()
end));
(abstract_guard x g);
))
end));
))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env e t1 t2 -> (

let uu____21720 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____21721 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t2 t1)
in (FStar_Errors.err uu____21720 uu____21721))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env c1 c2 -> ((

let uu____21737 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____21737) with
| true -> begin
(

let uu____21738 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____21739 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" uu____21738 uu____21739)))
end
| uu____21740 -> begin
()
end));
(

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____21742 -> begin
FStar_TypeChecker_Common.SUB
end)
in (

let prob = (

let uu____21744 = (

let uu____21749 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 FStar_Pervasives_Native.None uu____21749 "sub_comp"))
in (FStar_All.pipe_left (fun _0_99 -> FStar_TypeChecker_Common.CProb (_0_99)) uu____21744))
in (

let uu____21754 = (

let uu____21757 = (singleton env prob)
in (solve_and_commit env uu____21757 (fun uu____21759 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____21754))));
))


let solve_universe_inequalities' : FStar_Syntax_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun tx env uu____21791 -> (match (uu____21791) with
| (variables, ineqs) -> begin
(

let fail = (fun u1 u2 -> ((FStar_Syntax_Unionfind.rollback tx);
(

let uu____21830 = (

let uu____21831 = (

let uu____21836 = (

let uu____21837 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____21838 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Universe %s and %s are incompatible" uu____21837 uu____21838)))
in (

let uu____21839 = (FStar_TypeChecker_Env.get_range env)
in ((uu____21836), (uu____21839))))
in FStar_Errors.Error (uu____21831))
in (FStar_Exn.raise uu____21830));
))
in (

let equiv1 = (fun v1 v' -> (

let uu____21847 = (

let uu____21852 = (FStar_Syntax_Subst.compress_univ v1)
in (

let uu____21853 = (FStar_Syntax_Subst.compress_univ v')
in ((uu____21852), (uu____21853))))
in (match (uu____21847) with
| (FStar_Syntax_Syntax.U_unif (v0), FStar_Syntax_Syntax.U_unif (v0')) -> begin
(FStar_Syntax_Unionfind.univ_equiv v0 v0')
end
| uu____21872 -> begin
false
end)))
in (

let sols = (FStar_All.pipe_right variables (FStar_List.collect (fun v1 -> (

let uu____21902 = (FStar_Syntax_Subst.compress_univ v1)
in (match (uu____21902) with
| FStar_Syntax_Syntax.U_unif (uu____21909) -> begin
(

let lower_bounds_of_v = (FStar_All.pipe_right ineqs (FStar_List.collect (fun uu____21938 -> (match (uu____21938) with
| (u, v') -> begin
(

let uu____21947 = (equiv1 v1 v')
in (match (uu____21947) with
| true -> begin
(

let uu____21950 = (FStar_All.pipe_right variables (FStar_Util.for_some (equiv1 u)))
in (match (uu____21950) with
| true -> begin
[]
end
| uu____21955 -> begin
(u)::[]
end))
end
| uu____21956 -> begin
[]
end))
end))))
in (

let lb = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max (lower_bounds_of_v)))
in (((lb), (v1)))::[]))
end
| uu____21966 -> begin
[]
end)))))
in (

let uu____21971 = (

let wl = (

let uu___187_21975 = (empty_worklist env)
in {attempting = uu___187_21975.attempting; wl_deferred = uu___187_21975.wl_deferred; ctr = uu___187_21975.ctr; defer_ok = false; smt_ok = uu___187_21975.smt_ok; tcenv = uu___187_21975.tcenv})
in (FStar_All.pipe_right sols (FStar_List.map (fun uu____21993 -> (match (uu____21993) with
| (lb, v1) -> begin
(

let uu____22000 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl lb v1)
in (match (uu____22000) with
| USolved (wl1) -> begin
()
end
| uu____22002 -> begin
(fail lb v1)
end))
end)))))
in (

let rec check_ineq = (fun uu____22010 -> (match (uu____22010) with
| (u, v1) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u)
in (

let v2 = (FStar_TypeChecker_Normalize.normalize_universe env v1)
in (match (((u1), (v2))) with
| (FStar_Syntax_Syntax.U_zero, uu____22019) -> begin
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
| (FStar_Syntax_Syntax.U_name (uu____22042), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_unif (uu____22044), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_max (us), uu____22055) -> begin
(FStar_All.pipe_right us (FStar_Util.for_all (fun u2 -> (check_ineq ((u2), (v2))))))
end
| (uu____22062, FStar_Syntax_Syntax.U_max (vs)) -> begin
(FStar_All.pipe_right vs (FStar_Util.for_some (fun v3 -> (check_ineq ((u1), (v3))))))
end
| uu____22070 -> begin
false
end)))
end))
in (

let uu____22075 = (FStar_All.pipe_right ineqs (FStar_Util.for_all (fun uu____22090 -> (match (uu____22090) with
| (u, v1) -> begin
(

let uu____22097 = (check_ineq ((u), (v1)))
in (match (uu____22097) with
| true -> begin
true
end
| uu____22098 -> begin
((

let uu____22100 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____22100) with
| true -> begin
(

let uu____22101 = (FStar_Syntax_Print.univ_to_string u)
in (

let uu____22102 = (FStar_Syntax_Print.univ_to_string v1)
in (FStar_Util.print2 "%s </= %s" uu____22101 uu____22102)))
end
| uu____22103 -> begin
()
end));
false;
)
end))
end))))
in (match (uu____22075) with
| true -> begin
()
end
| uu____22104 -> begin
((

let uu____22106 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____22106) with
| true -> begin
((

let uu____22108 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Partially solved inequality constraints are: %s\n" uu____22108));
(FStar_Syntax_Unionfind.rollback tx);
(

let uu____22118 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Original solved inequality constraints are: %s\n" uu____22118));
)
end
| uu____22127 -> begin
()
end));
(

let uu____22128 = (

let uu____22129 = (

let uu____22134 = (FStar_TypeChecker_Env.get_range env)
in (("Failed to solve universe inequalities for inductives"), (uu____22134)))
in FStar_Errors.Error (uu____22129))
in (FStar_Exn.raise uu____22128));
)
end)))))))
end))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun env ineqs -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Syntax_Unionfind.commit tx);
)))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail = (fun uu____22186 -> (match (uu____22186) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (FStar_Exn.raise (FStar_Errors.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in ((

let uu____22200 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____22200) with
| true -> begin
(

let uu____22201 = (wl_to_string wl)
in (

let uu____22202 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" uu____22201 uu____22202)))
end
| uu____22215 -> begin
()
end));
(

let g1 = (

let uu____22217 = (solve_and_commit env wl fail)
in (match (uu____22217) with
| FStar_Pervasives_Native.Some ([]) -> begin
(

let uu___188_22230 = g
in {FStar_TypeChecker_Env.guard_f = uu___188_22230.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu___188_22230.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___188_22230.FStar_TypeChecker_Env.implicits})
end
| uu____22235 -> begin
(failwith "impossible: Unexpected deferred constraints remain")
end))
in ((solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___189_22239 = g1
in {FStar_TypeChecker_Env.guard_f = uu___189_22239.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___189_22239.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = uu___189_22239.FStar_TypeChecker_Env.implicits});
));
))))


let last_proof_ns : FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let maybe_update_proof_ns : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (

let pns = env.FStar_TypeChecker_Env.proof_ns
in (

let uu____22262 = (FStar_ST.op_Bang last_proof_ns)
in (match (uu____22262) with
| FStar_Pervasives_Native.None -> begin
(FStar_ST.op_Colon_Equals last_proof_ns (FStar_Pervasives_Native.Some (pns)))
end
| FStar_Pervasives_Native.Some (old) -> begin
(match ((old = pns)) with
| true -> begin
()
end
| uu____22302 -> begin
((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(FStar_ST.op_Colon_Equals last_proof_ns (FStar_Pervasives_Native.Some (pns)));
)
end)
end))))


let discharge_guard' : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun use_env_range_msg env g use_smt -> (

let g1 = (solve_deferred_constraints env g)
in (

let ret_g = (

let uu___190_22353 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___190_22353.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___190_22353.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___190_22353.FStar_TypeChecker_Env.implicits})
in (

let uu____22354 = (

let uu____22355 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____22355)))
in (match (uu____22354) with
| true -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| uu____22358 -> begin
(match (g1.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((

let uu____22363 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Norm"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____22363) with
| true -> begin
(

let uu____22364 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____22365 = (

let uu____22366 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____22366))
in (FStar_Errors.diag uu____22364 uu____22365)))
end
| uu____22367 -> begin
()
end));
(

let vc1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env vc)
in (

let uu____22369 = (check_trivial vc1)
in (match (uu____22369) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc2) -> begin
(match ((not (use_smt))) with
| true -> begin
((

let uu____22376 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____22376) with
| true -> begin
(

let uu____22377 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____22378 = (

let uu____22379 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Cannot solve without SMT : %s\n" uu____22379))
in (FStar_Errors.diag uu____22377 uu____22378)))
end
| uu____22380 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| uu____22381 -> begin
((

let uu____22384 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____22384) with
| true -> begin
(

let uu____22385 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____22386 = (

let uu____22387 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____22387))
in (FStar_Errors.diag uu____22385 uu____22386)))
end
| uu____22388 -> begin
()
end));
(

let vcs = (

let uu____22398 = (FStar_Options.use_tactics ())
in (match (uu____22398) with
| true -> begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.preprocess env vc2)
end
| uu____22407 -> begin
(

let uu____22408 = (

let uu____22415 = (FStar_Options.peek ())
in ((env), (vc2), (uu____22415)))
in (uu____22408)::[])
end))
in (FStar_All.pipe_right vcs (FStar_List.iter (fun uu____22449 -> (match (uu____22449) with
| (env1, goal, opts) -> begin
(

let goal1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::[]) env1 goal)
in (

let uu____22460 = (check_trivial goal1)
in (match (uu____22460) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let uu____22462 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Tac"))))
in (match (uu____22462) with
| true -> begin
(FStar_Util.print_string "Goal completely solved by tactic\n")
end
| uu____22463 -> begin
()
end))
end
| FStar_TypeChecker_Common.NonTrivial (goal2) -> begin
((FStar_Options.push ());
(FStar_Options.set opts);
(maybe_update_proof_ns env1);
(

let uu____22469 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____22469) with
| true -> begin
(

let uu____22470 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____22471 = (

let uu____22472 = (FStar_Syntax_Print.term_to_string goal2)
in (

let uu____22473 = (FStar_TypeChecker_Env.string_of_proof_ns env1)
in (FStar_Util.format2 "Trying to solve:\n> %s\nWith proof_ns:\n %s\n" uu____22472 uu____22473)))
in (FStar_Errors.diag uu____22470 uu____22471)))
end
| uu____22474 -> begin
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

let uu____22485 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____22485) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____22491 = (

let uu____22492 = (

let uu____22497 = (FStar_TypeChecker_Env.get_range env)
in (("Expected a trivial pre-condition"), (uu____22497)))
in FStar_Errors.Error (uu____22492))
in (FStar_Exn.raise uu____22491))
end)))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let uu____22506 = (discharge_guard' FStar_Pervasives_Native.None env g true)
in (match (uu____22506) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end)))


let resolve_implicits' : Prims.bool  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun forcelax g -> (

let unresolved = (fun u -> (

let uu____22524 = (FStar_Syntax_Unionfind.find u)
in (match (uu____22524) with
| FStar_Pervasives_Native.None -> begin
true
end
| uu____22527 -> begin
false
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____22545 = acc
in (match (uu____22545) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____22564 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd1)::tl1 -> begin
(

let uu____22631 = hd1
in (match (uu____22631) with
| (uu____22644, env, u, tm, k, r) -> begin
(

let uu____22650 = (unresolved u)
in (match (uu____22650) with
| true -> begin
(until_fixpoint (((hd1)::out), (changed)) tl1)
end
| uu____22677 -> begin
(

let env1 = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 tm)
in ((

let uu____22681 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("RelCheck")))
in (match (uu____22681) with
| true -> begin
(

let uu____22682 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____22683 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____22684 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" uu____22682 uu____22683 uu____22684))))
end
| uu____22685 -> begin
()
end));
(

let env2 = (match (forcelax) with
| true -> begin
(

let uu___191_22687 = env1
in {FStar_TypeChecker_Env.solver = uu___191_22687.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___191_22687.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___191_22687.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___191_22687.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___191_22687.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___191_22687.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___191_22687.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___191_22687.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___191_22687.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___191_22687.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___191_22687.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___191_22687.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___191_22687.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___191_22687.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___191_22687.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___191_22687.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___191_22687.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___191_22687.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___191_22687.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___191_22687.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___191_22687.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___191_22687.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___191_22687.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___191_22687.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___191_22687.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___191_22687.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___191_22687.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___191_22687.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___191_22687.FStar_TypeChecker_Env.identifier_info})
end
| uu____22688 -> begin
env1
end)
in (

let uu____22689 = (env2.FStar_TypeChecker_Env.type_of (

let uu___192_22697 = env2
in {FStar_TypeChecker_Env.solver = uu___192_22697.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___192_22697.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___192_22697.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___192_22697.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___192_22697.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___192_22697.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___192_22697.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___192_22697.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___192_22697.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___192_22697.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___192_22697.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___192_22697.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___192_22697.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___192_22697.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___192_22697.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___192_22697.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___192_22697.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___192_22697.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___192_22697.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___192_22697.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___192_22697.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___192_22697.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___192_22697.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___192_22697.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___192_22697.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___192_22697.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___192_22697.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___192_22697.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___192_22697.FStar_TypeChecker_Env.identifier_info}) tm1)
in (match (uu____22689) with
| (uu____22698, uu____22699, g1) -> begin
(

let g2 = (match (env2.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___193_22702 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___193_22702.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___193_22702.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___193_22702.FStar_TypeChecker_Env.implicits})
end
| uu____22703 -> begin
g1
end)
in (

let g' = (

let uu____22705 = (discharge_guard' (FStar_Pervasives_Native.Some ((fun uu____22711 -> (FStar_Syntax_Print.term_to_string tm1)))) env2 g2 true)
in (match (uu____22705) with
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

let uu___194_22739 = g
in (

let uu____22740 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___194_22739.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___194_22739.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___194_22739.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____22740})))))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (resolve_implicits' false g))


let resolve_implicits_lax : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (resolve_implicits' true g))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g1 = (

let uu____22798 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____22798 resolve_implicits))
in (match (g1.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(

let uu____22811 = (discharge_guard env g1)
in (FStar_All.pipe_left FStar_Pervasives.ignore uu____22811))
end
| ((reason, uu____22813, uu____22814, e, t, r))::uu____22818 -> begin
(

let uu____22845 = (

let uu____22846 = (

let uu____22851 = (

let uu____22852 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____22853 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Failed to resolve implicit argument of type \'%s\' introduced in %s" uu____22852 uu____22853)))
in ((uu____22851), (r)))
in FStar_Errors.Error (uu____22846))
in (FStar_Exn.raise uu____22845))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___195_22862 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___195_22862.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___195_22862.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ((((u1), (u2)))::[])); FStar_TypeChecker_Env.implicits = uu___195_22862.FStar_TypeChecker_Env.implicits}))


let teq_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____22891 = (try_teq false env t1 t2)
in (match (uu____22891) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g) -> begin
(

let uu____22895 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____22895) with
| FStar_Pervasives_Native.Some (uu____22900) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end))
end)))






open Prims

let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu____20; FStar_TypeChecker_Env.implicits = uu____21} -> begin
true
end
| uu____35 -> begin
false
end))


let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []}


let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _; FStar_TypeChecker_Env.univ_ineqs = _; FStar_TypeChecker_Env.implicits = _})) -> begin
g
end
| Some (g1) -> begin
(

let f = (match (g1.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| uu____62 -> begin
(failwith "impossible")
end)
in (

let uu____63 = (

let uu___132_64 = g1
in (

let uu____65 = (

let uu____66 = (

let uu____67 = (

let uu____68 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____68)::[])
in (

let uu____69 = (

let uu____76 = (

let uu____82 = (

let uu____83 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____83 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____82 (fun _0_28 -> FStar_Util.Inl (_0_28))))
in Some (uu____76))
in (FStar_Syntax_Util.abs uu____67 f uu____69)))
in (FStar_All.pipe_left (fun _0_29 -> FStar_TypeChecker_Common.NonTrivial (_0_29)) uu____66))
in {FStar_TypeChecker_Env.guard_f = uu____65; FStar_TypeChecker_Env.deferred = uu___132_64.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___132_64.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___132_64.FStar_TypeChecker_Env.implicits}))
in Some (uu____63)))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___133_104 = g
in (

let uu____105 = (

let uu____106 = (

let uu____107 = (

let uu____110 = (

let uu____111 = (

let uu____121 = (

let uu____123 = (FStar_Syntax_Syntax.as_arg e)
in (uu____123)::[])
in ((f), (uu____121)))
in FStar_Syntax_Syntax.Tm_app (uu____111))
in (FStar_Syntax_Syntax.mk uu____110))
in (uu____107 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _0_30 -> FStar_TypeChecker_Common.NonTrivial (_0_30)) uu____106))
in {FStar_TypeChecker_Env.guard_f = uu____105; FStar_TypeChecker_Env.deferred = uu___133_104.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___133_104.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___133_104.FStar_TypeChecker_Env.implicits}))
end))


let map_guard : FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  FStar_TypeChecker_Env.guard_t = (fun g map1 -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___134_145 = g
in (

let uu____146 = (

let uu____147 = (map1 f)
in FStar_TypeChecker_Common.NonTrivial (uu____147))
in {FStar_TypeChecker_Env.guard_f = uu____146; FStar_TypeChecker_Env.deferred = uu___134_145.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___134_145.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___134_145.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____151) -> begin
(failwith "impossible")
end))


let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let uu____161 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (uu____161))
end))


let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____170 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end))


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

let uu____201 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = uu____201; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (((FStar_List.append (Prims.fst g1.FStar_TypeChecker_Env.univ_ineqs) (Prims.fst g2.FStar_TypeChecker_Env.univ_ineqs))), ((FStar_List.append (Prims.snd g1.FStar_TypeChecker_Env.univ_ineqs) (Prims.snd g2.FStar_TypeChecker_Env.univ_ineqs)))); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard_univs : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun us bs g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let f1 = (FStar_List.fold_right2 (fun u b f1 -> (

let uu____246 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____246) with
| true -> begin
f1
end
| uu____247 -> begin
(FStar_Syntax_Util.mk_forall u (Prims.fst b) f1)
end))) us bs f)
in (

let uu___135_248 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.NonTrivial (f1); FStar_TypeChecker_Env.deferred = uu___135_248.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___135_248.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___135_248.FStar_TypeChecker_Env.implicits}))
end))


let close_forall : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____262 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____262) with
| true -> begin
f1
end
| uu____263 -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Util.mk_forall u (Prims.fst b) f1))
end))) bs f))


let close_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___136_275 = g
in (

let uu____276 = (

let uu____277 = (close_forall env binders f)
in FStar_TypeChecker_Common.NonTrivial (uu____277))
in {FStar_TypeChecker_Env.guard_f = uu____276; FStar_TypeChecker_Env.deferred = uu___136_275.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___136_275.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___136_275.FStar_TypeChecker_Env.implicits}))
end))


let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (

let uv = (FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(

let uv1 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k))))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((uv1), (uv1)))
end
| uu____322 -> begin
(

let args = (FStar_All.pipe_right binders (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder))
in (

let k' = (

let uu____337 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders uu____337))
in (

let uv1 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k'))))) None r)
in (

let uu____357 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((uv1), (args))))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((uu____357), (uv1))))))
end)))


let mk_eq2 : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t1 t2 -> (

let uu____390 = (FStar_Syntax_Util.type_u ())
in (match (uu____390) with
| (t_type, u) -> begin
(

let uu____395 = (

let uu____398 = (FStar_TypeChecker_Env.all_binders env)
in (new_uvar t1.FStar_Syntax_Syntax.pos uu____398 t_type))
in (match (uu____395) with
| (tt, uu____400) -> begin
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
| uu____421 -> begin
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
| uu____447 -> begin
false
end))


let __proj__UNIV__item___0 : uvi  ->  (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe) = (fun projectee -> (match (projectee) with
| UNIV (_0) -> begin
_0
end))

type worklist =
{attempting : FStar_TypeChecker_Common.probs; wl_deferred : (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list; ctr : Prims.int; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_TypeChecker_Env.env}

type solution =
| Success of FStar_TypeChecker_Common.deferred
| Failed of (FStar_TypeChecker_Common.prob * Prims.string)


let uu___is_Success : solution  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
true
end
| uu____527 -> begin
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
| uu____541 -> begin
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
| uu____558 -> begin
false
end))


let uu___is_CONTRAVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CONTRAVARIANT -> begin
true
end
| uu____562 -> begin
false
end))


let uu___is_INVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| INVARIANT -> begin
true
end
| uu____566 -> begin
false
end))


type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem


type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem


type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun uu___104_583 -> (match (uu___104_583) with
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

let uu____596 = (

let uu____597 = (FStar_Syntax_Subst.compress t)
in uu____597.FStar_Syntax_Syntax.n)
in (match (uu____596) with
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let uu____614 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____618 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s:%s)" uu____614 uu____618)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty); FStar_Syntax_Syntax.tk = uu____621; FStar_Syntax_Syntax.pos = uu____622; FStar_Syntax_Syntax.vars = uu____623}, args) -> begin
(

let uu____651 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____655 = (FStar_Syntax_Print.term_to_string ty)
in (

let uu____656 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "(%s:%s) %s" uu____651 uu____655 uu____656))))
end
| uu____657 -> begin
(FStar_Syntax_Print.term_to_string t)
end)))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env uu___105_663 -> (match (uu___105_663) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____667 = (

let uu____669 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____670 = (

let uu____672 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____673 = (

let uu____675 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (

let uu____676 = (

let uu____678 = (

let uu____680 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (

let uu____681 = (

let uu____683 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (

let uu____684 = (

let uu____686 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (

let uu____687 = (

let uu____689 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (uu____689)::[])
in (uu____686)::uu____687))
in (uu____683)::uu____684))
in (uu____680)::uu____681))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::uu____678)
in (uu____675)::uu____676))
in (uu____672)::uu____673))
in (uu____669)::uu____670))
in (FStar_Util.format "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" uu____667))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____694 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____695 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____694 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____695)))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env uu___106_701 -> (match (uu___106_701) with
| UNIV (u, t) -> begin
(

let x = (

let uu____705 = (FStar_Options.hide_uvar_nums ())
in (match (uu____705) with
| true -> begin
"?"
end
| uu____706 -> begin
(

let uu____707 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____707 FStar_Util.string_of_int))
end))
in (

let uu____709 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x uu____709)))
end
| TERM ((u, uu____711), t) -> begin
(

let x = (

let uu____716 = (FStar_Options.hide_uvar_nums ())
in (match (uu____716) with
| true -> begin
"?"
end
| uu____717 -> begin
(

let uu____718 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____718 FStar_Util.string_of_int))
end))
in (

let uu____722 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x uu____722)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (

let uu____731 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right uu____731 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (

let uu____739 = (

let uu____741 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right uu____741 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right uu____739 (FStar_String.concat ", "))))


let args_to_string = (fun args -> (

let uu____759 = (FStar_All.pipe_right args (FStar_List.map (fun uu____767 -> (match (uu____767) with
| (x, uu____771) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____759 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> (

let uu____776 = (

let uu____777 = (FStar_Options.eager_inference ())
in (not (uu____777)))
in {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = uu____776; smt_ok = true; tcenv = env}))


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let uu___137_790 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = uu___137_790.wl_deferred; ctr = uu___137_790.ctr; defer_ok = uu___137_790.defer_ok; smt_ok = smt_ok; tcenv = uu___137_790.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard = (fun env g -> (

let uu___138_815 = (empty_worklist env)
in (

let uu____816 = (FStar_List.map Prims.snd g)
in {attempting = uu____816; wl_deferred = uu___138_815.wl_deferred; ctr = uu___138_815.ctr; defer_ok = false; smt_ok = uu___138_815.smt_ok; tcenv = uu___138_815.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu___139_828 = wl
in {attempting = uu___139_828.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = uu___139_828.ctr; defer_ok = uu___139_828.defer_ok; smt_ok = uu___139_828.smt_ok; tcenv = uu___139_828.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let uu___140_840 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = uu___140_840.wl_deferred; ctr = uu___140_840.ctr; defer_ok = uu___140_840.defer_ok; smt_ok = uu___140_840.smt_ok; tcenv = uu___140_840.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> ((

let uu____851 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____851) with
| true -> begin
(

let uu____852 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason uu____852))
end
| uu____853 -> begin
()
end));
Failed (((prob), (reason)));
))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun uu___107_856 -> (match (uu___107_856) with
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

let uu___141_872 = p
in {FStar_TypeChecker_Common.pid = uu___141_872.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = uu___141_872.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___141_872.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___141_872.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___141_872.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___141_872.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___141_872.FStar_TypeChecker_Common.rank}))


let maybe_invert = (fun p -> (match ((p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV)) with
| true -> begin
(invert p)
end
| uu____890 -> begin
p
end))


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___108_893 -> (match (uu___108_893) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_31 -> FStar_TypeChecker_Common.TProb (_0_31)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_32 -> FStar_TypeChecker_Common.CProb (_0_32)))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel uu___109_909 -> (match (uu___109_909) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun uu___110_912 -> (match (uu___110_912) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun uu___111_921 -> (match (uu___111_921) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun uu___112_931 -> (match (uu___112_931) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun uu___113_941 -> (match (uu___113_941) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun uu___114_952 -> (match (uu___114_952) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun uu___115_963 -> (match (uu___115_963) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___116_972 -> (match (uu___116_972) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _0_33 -> FStar_TypeChecker_Common.TProb (_0_33)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _0_34 -> FStar_TypeChecker_Common.CProb (_0_34)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> (

let uu____986 = (FStar_All.pipe_right (p_reason p) FStar_List.length)
in (uu____986 = (Prims.parse_int "1"))))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____997 -> ((FStar_Util.incr ctr);
(FStar_ST.read ctr);
)))


let mk_problem = (fun scope orig lhs rel rhs elt reason -> (

let uu____1047 = (next_pid ())
in (

let uu____1048 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____1047; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____1048; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))


let new_problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (

let uu____1095 = (next_pid ())
in (

let uu____1096 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____1095; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____1096; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (

let uu____1137 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____1137; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))


let guard_on_element = (fun wl problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(

let u = (wl.tcenv.FStar_TypeChecker_Env.universe_of wl.tcenv x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Util.mk_forall u x phi))
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (

let uu____1189 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____1189) with
| true -> begin
(

let uu____1190 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (

let uu____1191 = (prob_to_string env d)
in (

let uu____1192 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" uu____1190 uu____1191 uu____1192 s))))
end
| uu____1194 -> begin
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
| uu____1197 -> begin
(failwith "impossible")
end)
in (

let uu____1198 = (match (d1) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____1206 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (

let uu____1207 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((uu____1206), (uu____1207))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____1211 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (

let uu____1212 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((uu____1211), (uu____1212))))
end)
in (match (uu____1198) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___117_1221 -> (match (uu___117_1221) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| uu____1228 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, uu____1231), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun uu___118_1254 -> (match (uu___118_1254) with
| UNIV (uu____1256) -> begin
None
end
| TERM ((u, uu____1260), t) -> begin
(

let uu____1264 = (FStar_Unionfind.equivalent uv u)
in (match (uu____1264) with
| true -> begin
Some (t)
end
| uu____1269 -> begin
None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun uu___119_1283 -> (match (uu___119_1283) with
| UNIV (u', t) -> begin
(

let uu____1287 = (FStar_Unionfind.equivalent u u')
in (match (uu____1287) with
| true -> begin
Some (t)
end
| uu____1290 -> begin
None
end))
end
| uu____1291 -> begin
None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1298 = (

let uu____1299 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____1299))
in (FStar_Syntax_Subst.compress uu____1298)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1306 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress uu____1306)))


let norm_arg = (fun env t -> (

let uu____1325 = (sn env (Prims.fst t))
in ((uu____1325), ((Prims.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____1342 -> (match (uu____1342) with
| (x, imp) -> begin
(

let uu____1349 = (

let uu___142_1350 = x
in (

let uu____1351 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___142_1350.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___142_1350.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1351}))
in ((uu____1349), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____1366 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____1366))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1369 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____1369))
end
| uu____1371 -> begin
u2
end)))
in (

let uu____1372 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1372))))


let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement = (fun env wl t1 -> (

let rec aux = (fun norm t11 -> (match (t11.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(match (norm) with
| true -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| uu____1478 -> begin
(

let uu____1479 = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (match (uu____1479) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x1, phi1); FStar_Syntax_Syntax.tk = uu____1491; FStar_Syntax_Syntax.pos = uu____1492; FStar_Syntax_Syntax.vars = uu____1493} -> begin
((x1.FStar_Syntax_Syntax.sort), (Some (((x1), (phi1)))))
end
| tt -> begin
(

let uu____1514 = (

let uu____1515 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____1516 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1515 uu____1516)))
in (failwith uu____1514))
end))
end)
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(match (norm) with
| true -> begin
((t11), (None))
end
| uu____1549 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (

let uu____1551 = (

let uu____1552 = (FStar_Syntax_Subst.compress t1')
in uu____1552.FStar_Syntax_Syntax.n)
in (match (uu____1551) with
| FStar_Syntax_Syntax.Tm_refine (uu____1564) -> begin
(aux true t1')
end
| uu____1569 -> begin
((t11), (None))
end)))
end)
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
((t11), (None))
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(

let uu____1604 = (

let uu____1605 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____1606 = (FStar_Syntax_Print.tag_of_term t11)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1605 uu____1606)))
in (failwith uu____1604))
end))
in (

let uu____1616 = (whnf env t1)
in (aux false uu____1616))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____1625 = (

let uu____1635 = (empty_worklist env)
in (base_and_refinement env uu____1635 t))
in (FStar_All.pipe_right uu____1625 Prims.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (

let uu____1659 = (FStar_Syntax_Syntax.null_bv t)
in ((uu____1659), (FStar_Syntax_Util.t_true))))


let as_refinement = (fun env wl t -> (

let uu____1679 = (base_and_refinement env wl t)
in (match (uu____1679) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement = (fun uu____1738 -> (match (uu____1738) with
| (t_base, refopt) -> begin
(

let uu____1752 = (match (refopt) with
| Some (y, phi) -> begin
((y), (phi))
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (uu____1752) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl uu___120_1776 -> (match (uu___120_1776) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____1780 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1781 = (

let uu____1782 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string uu____1782))
in (

let uu____1783 = (

let uu____1784 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string uu____1784))
in (FStar_Util.format4 "%s: %s  (%s)  %s" uu____1780 uu____1781 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1783))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____1788 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1789 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____1790 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" uu____1788 uu____1789 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1790))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (

let uu____1794 = (

let uu____1796 = (

let uu____1798 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____1808 -> (match (uu____1808) with
| (uu____1812, uu____1813, x) -> begin
x
end))))
in (FStar_List.append wl.attempting uu____1798))
in (FStar_List.map (wl_prob_to_string wl) uu____1796))
in (FStar_All.pipe_right uu____1794 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____1831 = (

let uu____1841 = (

let uu____1842 = (FStar_Syntax_Subst.compress k)
in uu____1842.FStar_Syntax_Syntax.n)
in (match (uu____1841) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (((FStar_List.length bs) = (FStar_List.length ys))) with
| true -> begin
(

let uu____1883 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (uu____1883)))
end
| uu____1896 -> begin
(

let uu____1897 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____1897) with
| (ys', t1, uu____1918) -> begin
(

let uu____1931 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t1))), (uu____1931)))
end))
end)
end
| uu____1952 -> begin
(

let uu____1953 = (

let uu____1959 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____1959)))
in ((((ys), (t))), (uu____1953)))
end))
in (match (uu____1831) with
| ((ys1, t1), (xs, c)) -> begin
(match (((FStar_List.length xs) <> (FStar_List.length ys1))) with
| true -> begin
(FStar_Syntax_Util.abs ys1 t1 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ([]))))))
end
| uu____2012 -> begin
(

let c1 = (

let uu____2014 = (FStar_Syntax_Util.rename_binders xs ys1)
in (FStar_Syntax_Subst.subst_comp uu____2014 c))
in (

let uu____2016 = (

let uu____2023 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1) (fun _0_35 -> FStar_Util.Inl (_0_35)))
in (FStar_All.pipe_right uu____2023 (fun _0_36 -> Some (_0_36))))
in (FStar_Syntax_Util.abs ys1 t1 uu____2016)))
end)
end)))


let solve_prob' : Prims.bool  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun resolve_ok prob logical_guard uvis wl -> (

let phi = (match (logical_guard) with
| None -> begin
FStar_Syntax_Util.t_true
end
| Some (phi) -> begin
phi
end)
in (

let uu____2074 = (p_guard prob)
in (match (uu____2074) with
| (uu____2077, uv) -> begin
((

let uu____2080 = (

let uu____2081 = (FStar_Syntax_Subst.compress uv)
in uu____2081.FStar_Syntax_Syntax.n)
in (match (uu____2080) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi1 = (u_abs k bs phi)
in ((

let uu____2101 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____2101) with
| true -> begin
(

let uu____2102 = (FStar_Util.string_of_int (p_pid prob))
in (

let uu____2103 = (FStar_Syntax_Print.term_to_string uv)
in (

let uu____2104 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" uu____2102 uu____2103 uu____2104))))
end
| uu____2105 -> begin
()
end));
(FStar_Syntax_Util.set_uvar uvar phi1);
)))
end
| uu____2108 -> begin
(match ((not (resolve_ok))) with
| true -> begin
(failwith "Impossible: this instance has already been assigned a solution")
end
| uu____2109 -> begin
()
end)
end));
(commit uvis);
(

let uu___143_2111 = wl
in {attempting = uu___143_2111.attempting; wl_deferred = uu___143_2111.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___143_2111.defer_ok; smt_ok = uu___143_2111.smt_ok; tcenv = uu___143_2111.tcenv});
)
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____2124 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____2124) with
| true -> begin
(

let uu____2125 = (FStar_Util.string_of_int pid)
in (

let uu____2126 = (

let uu____2127 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right uu____2127 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____2125 uu____2126)))
end
| uu____2130 -> begin
()
end));
(commit sol);
(

let uu___144_2132 = wl
in {attempting = uu___144_2132.attempting; wl_deferred = uu___144_2132.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___144_2132.defer_ok; smt_ok = uu___144_2132.smt_ok; tcenv = uu___144_2132.tcenv});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard1 = (fun t g -> (match (((t), (g))) with
| (uu____2161, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t1), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(

let uu____2169 = (FStar_Syntax_Util.mk_conj t1 f)
in Some (uu____2169))
end))
in ((

let uu____2175 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____2175) with
| true -> begin
(

let uu____2176 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (

let uu____2177 = (

let uu____2178 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right uu____2178 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____2176 uu____2177)))
end
| uu____2181 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
)))


let rec occurs = (fun wl uk t -> (

let uu____2203 = (

let uu____2207 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right uu____2207 FStar_Util.set_elements))
in (FStar_All.pipe_right uu____2203 (FStar_Util.for_some (fun uu____2228 -> (match (uu____2228) with
| (uv, uu____2236) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (

let uu____2280 = (occurs wl uk t)
in (not (uu____2280)))
in (

let msg = (match (occurs_ok) with
| true -> begin
None
end
| uu____2284 -> begin
(

let uu____2285 = (

let uu____2286 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (

let uu____2290 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" uu____2286 uu____2290)))
in Some (uu____2285))
end)
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let uu____2338 = (occurs_check env wl uk t)
in (match (uu____2338) with
| (occurs_ok, msg) -> begin
(

let uu____2355 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (uu____2355), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set = (fun v3 -> (FStar_All.pipe_right v3 (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set v1)
in (

let uu____2419 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____2443 uu____2444 -> (match (((uu____2443), (uu____2444))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____2487 = (

let uu____2488 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation uu____2488))
in (match (uu____2487) with
| true -> begin
((isect), (isect_set))
end
| uu____2499 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____2502 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____2502) with
| true -> begin
(

let uu____2509 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (uu____2509)))
end
| uu____2517 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (uu____2419) with
| (isect, uu____2531) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____2580 uu____2581 -> (match (((uu____2580), (uu____2581))) with
| ((a, uu____2591), (b, uu____2593)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd1 = (norm_arg env arg)
in (match ((Prims.fst hd1).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(

let uu____2637 = (FStar_All.pipe_right seen (FStar_Util.for_some (fun uu____2643 -> (match (uu____2643) with
| (b, uu____2647) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end))))
in (match (uu____2637) with
| true -> begin
None
end
| uu____2653 -> begin
Some (((a), ((Prims.snd hd1))))
end))
end
| uu____2656 -> begin
None
end)))


let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| (hd1)::rest -> begin
(

let uu____2699 = (pat_var_opt env seen hd1)
in (match (uu____2699) with
| None -> begin
((

let uu____2707 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____2707) with
| true -> begin
(

let uu____2708 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd1))
in (FStar_Util.print1 "Not a pattern: %s\n" uu____2708))
end
| uu____2709 -> begin
()
end));
None;
)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end))
end))


let is_flex : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2720 = (

let uu____2721 = (FStar_Syntax_Subst.compress t)
in uu____2721.FStar_Syntax_Syntax.n)
in (match (uu____2720) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
true
end
| uu____2737 -> begin
false
end)))


let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = uu____2799; FStar_Syntax_Syntax.pos = uu____2800; FStar_Syntax_Syntax.vars = uu____2801}, args) -> begin
((t), (uv), (k), (args))
end
| uu____2842 -> begin
(failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let uu____2896 = (destruct_flex_t t)
in (match (uu____2896) with
| (t1, uv, k, args) -> begin
(

let uu____2964 = (pat_vars env [] args)
in (match (uu____2964) with
| Some (vars) -> begin
((((t1), (uv), (k), (args))), (Some (vars)))
end
| uu____3020 -> begin
((((t1), (uv), (k), (args))), (None))
end))
end)))

type match_result =
| MisMatch of (FStar_Syntax_Syntax.delta_depth Prims.option * FStar_Syntax_Syntax.delta_depth Prims.option)
| HeadMatch
| FullMatch


let uu___is_MisMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MisMatch (_0) -> begin
true
end
| uu____3068 -> begin
false
end))


let __proj__MisMatch__item___0 : match_result  ->  (FStar_Syntax_Syntax.delta_depth Prims.option * FStar_Syntax_Syntax.delta_depth Prims.option) = (fun projectee -> (match (projectee) with
| MisMatch (_0) -> begin
_0
end))


let uu___is_HeadMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HeadMatch -> begin
true
end
| uu____3091 -> begin
false
end))


let uu___is_FullMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullMatch -> begin
true
end
| uu____3095 -> begin
false
end))


let head_match : match_result  ->  match_result = (fun uu___121_3098 -> (match (uu___121_3098) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____3107 -> begin
HeadMatch
end))


let fv_delta_depth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.delta_depth = (fun env fv -> (match (fv.FStar_Syntax_Syntax.fv_delta) with
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(match ((env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)) with
| true -> begin
d
end
| uu____3119 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
end
| FStar_Syntax_Syntax.Delta_defined_at_level (uu____3120) -> begin
(

let uu____3121 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3121) with
| None -> begin
FStar_Syntax_Syntax.Delta_constant
end
| uu____3131 -> begin
fv.FStar_Syntax_Syntax.fv_delta
end))
end
| d -> begin
d
end))


let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth Prims.option = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (match (t1.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
None
end
| (FStar_Syntax_Syntax.Tm_uinst (t2, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t2, _, _)) | (FStar_Syntax_Syntax.Tm_app (t2, _)) | (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t2}, _)) -> begin
(delta_depth_of_term env t2)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3199 = (fv_delta_depth env fv)
in Some (uu____3199))
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
| uu____3213 -> begin
MisMatch (((None), (None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____3218 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____3218) with
| true -> begin
FullMatch
end
| uu____3219 -> begin
(

let uu____3220 = (

let uu____3225 = (

let uu____3227 = (fv_delta_depth env f)
in Some (uu____3227))
in (

let uu____3228 = (

let uu____3230 = (fv_delta_depth env g)
in Some (uu____3230))
in ((uu____3225), (uu____3228))))
in MisMatch (uu____3220))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____3234), FStar_Syntax_Syntax.Tm_uinst (g, uu____3236)) -> begin
(

let uu____3245 = (head_matches env f g)
in (FStar_All.pipe_right uu____3245 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(match ((c = d)) with
| true -> begin
FullMatch
end
| uu____3248 -> begin
MisMatch (((None), (None)))
end)
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, uu____3252), FStar_Syntax_Syntax.Tm_uvar (uv', uu____3254)) -> begin
(

let uu____3279 = (FStar_Unionfind.equivalent uv uv')
in (match (uu____3279) with
| true -> begin
FullMatch
end
| uu____3283 -> begin
MisMatch (((None), (None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____3287), FStar_Syntax_Syntax.Tm_refine (y, uu____3289)) -> begin
(

let uu____3298 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____3298 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____3300), uu____3301) -> begin
(

let uu____3306 = (head_matches env x.FStar_Syntax_Syntax.sort t21)
in (FStar_All.pipe_right uu____3306 head_match))
end
| (uu____3307, FStar_Syntax_Syntax.Tm_refine (x, uu____3309)) -> begin
(

let uu____3314 = (head_matches env t11 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____3314 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____3320), FStar_Syntax_Syntax.Tm_app (head', uu____3322)) -> begin
(

let uu____3351 = (head_matches env head1 head')
in (FStar_All.pipe_right uu____3351 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____3353), uu____3354) -> begin
(

let uu____3369 = (head_matches env head1 t21)
in (FStar_All.pipe_right uu____3369 head_match))
end
| (uu____3370, FStar_Syntax_Syntax.Tm_app (head1, uu____3372)) -> begin
(

let uu____3387 = (head_matches env t11 head1)
in (FStar_All.pipe_right uu____3387 head_match))
end
| uu____3388 -> begin
(

let uu____3391 = (

let uu____3396 = (delta_depth_of_term env t11)
in (

let uu____3398 = (delta_depth_of_term env t21)
in ((uu____3396), (uu____3398))))
in MisMatch (uu____3391))
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let uu____3434 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____3434) with
| (head1, uu____3446) -> begin
(

let uu____3461 = (

let uu____3462 = (FStar_Syntax_Util.un_uinst head1)
in uu____3462.FStar_Syntax_Syntax.n)
in (match (uu____3461) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3467 = (

let uu____3468 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3468 FStar_Option.isSome))
in (match (uu____3467) with
| true -> begin
(

let uu____3482 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right uu____3482 (fun _0_37 -> Some (_0_37))))
end
| uu____3484 -> begin
None
end))
end
| uu____3485 -> begin
None
end))
end)))
in (

let success = (fun d r t11 t21 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
Some (((t11), (t21)))
end
| uu____3512 -> begin
None
end))))
in (

let fail = (fun r -> ((r), (None)))
in (

let rec aux = (fun retry n_delta t11 t21 -> (

let r = (head_matches env t11 t21)
in (match (r) with
| (MisMatch (Some (FStar_Syntax_Syntax.Delta_equational), _)) | (MisMatch (_, Some (FStar_Syntax_Syntax.Delta_equational))) -> begin
(match ((not (retry))) with
| true -> begin
(fail r)
end
| uu____3564 -> begin
(

let uu____3565 = (

let uu____3570 = (maybe_inline t11)
in (

let uu____3572 = (maybe_inline t21)
in ((uu____3570), (uu____3572))))
in (match (uu____3565) with
| (None, None) -> begin
(fail r)
end
| (Some (t12), None) -> begin
(aux false (n_delta + (Prims.parse_int "1")) t12 t21)
end
| (None, Some (t22)) -> begin
(aux false (n_delta + (Prims.parse_int "1")) t11 t22)
end
| (Some (t12), Some (t22)) -> begin
(aux false (n_delta + (Prims.parse_int "1")) t12 t22)
end))
end)
end
| MisMatch (Some (d1), Some (d2)) when (d1 = d2) -> begin
(

let uu____3597 = (FStar_TypeChecker_Common.decr_delta_depth d1)
in (match (uu____3597) with
| None -> begin
(fail r)
end
| Some (d) -> begin
(

let t12 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (

let t22 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t21)
in (aux retry (n_delta + (Prims.parse_int "1")) t12 t22)))
end))
end
| MisMatch (Some (d1), Some (d2)) -> begin
(

let d1_greater_than_d2 = (FStar_TypeChecker_Common.delta_depth_greater_than d1 d2)
in (

let uu____3612 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in ((t1'), (t21)))
end
| uu____3618 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t21)
in (

let uu____3620 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t21)
in ((t11), (uu____3620))))
end)
in (match (uu____3612) with
| (t12, t22) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
end)))
end
| MisMatch (uu____3628) -> begin
(fail r)
end
| uu____3633 -> begin
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
| uu____3658 -> begin
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
| uu____3688 -> begin
false
end))


let __proj__C__item___0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_0) -> begin
_0
end))


type tcs =
tc Prims.list


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____3703 = (FStar_Syntax_Util.type_u ())
in (match (uu____3703) with
| (t, uu____3707) -> begin
(

let uu____3708 = (new_uvar r binders t)
in (Prims.fst uu____3708))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____3717 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____3717 Prims.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (

let uu____3759 = (head_matches env t1 t')
in (match (uu____3759) with
| MisMatch (uu____3760) -> begin
false
end
| uu____3765 -> begin
true
end)))
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let rebuild = (fun args' -> (

let args1 = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((uu____3825, imp), T (t2, uu____3828)) -> begin
((t2), (imp))
end
| uu____3845 -> begin
(failwith "Bad reconstruction")
end)) args args')
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd1), (args1))))) None t1.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun uu____3889 -> (match (uu____3889) with
| (t2, uu____3897) -> begin
((None), (INVARIANT), (T (((t2), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let fail = (fun uu____3930 -> (failwith "Bad reconstruction"))
in (

let uu____3931 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3931) with
| (bs1, c1) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs2 tcs1 -> (match (((bs2), (tcs1))) with
| (((x, imp))::bs3, (T (t2, uu____3984))::tcs2) -> begin
(aux (((((

let uu___145_4006 = x
in {FStar_Syntax_Syntax.ppname = uu___145_4006.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___145_4006.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (imp)))::out) bs3 tcs2)
end
| ([], (C (c2))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c2)
end
| uu____4016 -> begin
(failwith "Bad reconstruction")
end))
in (aux [] bs1 tcs)))
in (

let rec decompose1 = (fun out uu___122_4047 -> (match (uu___122_4047) with
| [] -> begin
(FStar_List.rev ((((None), (COVARIANT), (C (c1))))::out))
end
| (hd1)::rest -> begin
(decompose1 ((((Some (hd1)), (CONTRAVARIANT), (T ((((Prims.fst hd1).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (

let uu____4110 = (decompose1 [] bs1)
in ((rebuild), (matches), (uu____4110)))))
end)))
end
| uu____4138 -> begin
(

let rebuild = (fun uu___123_4143 -> (match (uu___123_4143) with
| [] -> begin
t1
end
| uu____4145 -> begin
(failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t2 -> true)), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun uu___124_4164 -> (match (uu___124_4164) with
| T (t, uu____4166) -> begin
t
end
| uu____4175 -> begin
(failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun uu___125_4178 -> (match (uu___125_4178) with
| T (t, uu____4180) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| uu____4189 -> begin
(failwith "Impossible")
end))


let imitation_sub_probs : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list  ->  (FStar_TypeChecker_Common.prob Prims.list * tc Prims.list * FStar_Syntax_Syntax.formula) = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope1 args q -> (match (q) with
| (uu____4258, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope1 r)
in (

let uu____4277 = (new_uvar r scope1 k)
in (match (uu____4277) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| uu____4289 -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args))))) None r)
end)
in (

let uu____4308 = (

let uu____4309 = (mk_problem scope1 orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _0_38 -> FStar_TypeChecker_Common.TProb (_0_38)) uu____4309))
in ((T (((gi_xs), (mk_kind)))), (uu____4308))))
end)))
end
| (uu____4318, uu____4319, C (uu____4320)) -> begin
(failwith "impos")
end))
in (

let rec aux = (fun scope1 args qs1 -> (match (qs1) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs2 -> begin
(

let uu____4407 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.tk = uu____4418; FStar_Syntax_Syntax.pos = uu____4419; FStar_Syntax_Syntax.vars = uu____4420})) -> begin
(

let uu____4435 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____4435) with
| (T (gi_xs, uu____4451), prob) -> begin
(

let uu____4461 = (

let uu____4462 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_39 -> C (_0_39)) uu____4462))
in ((uu____4461), ((prob)::[])))
end
| uu____4464 -> begin
(failwith "impossible")
end))
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.tk = uu____4474; FStar_Syntax_Syntax.pos = uu____4475; FStar_Syntax_Syntax.vars = uu____4476})) -> begin
(

let uu____4491 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____4491) with
| (T (gi_xs, uu____4507), prob) -> begin
(

let uu____4517 = (

let uu____4518 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_40 -> C (_0_40)) uu____4518))
in ((uu____4517), ((prob)::[])))
end
| uu____4520 -> begin
(failwith "impossible")
end))
end
| (uu____4526, uu____4527, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = uu____4529; FStar_Syntax_Syntax.pos = uu____4530; FStar_Syntax_Syntax.vars = uu____4531})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((None), (INVARIANT), (T ((((Prims.fst t)), (generic_kind))))))))
in (

let components1 = (((None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let uu____4605 = (

let uu____4610 = (FStar_List.map (sub_prob scope1 args) components1)
in (FStar_All.pipe_right uu____4610 FStar_List.unzip))
in (match (uu____4605) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (

let uu____4639 = (

let uu____4640 = (

let uu____4643 = (FStar_List.hd tcs)
in (FStar_All.pipe_right uu____4643 un_T))
in (

let uu____4644 = (

let uu____4650 = (FStar_List.tl tcs)
in (FStar_All.pipe_right uu____4650 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____4640; FStar_Syntax_Syntax.effect_args = uu____4644; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____4639))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| uu____4655 -> begin
(

let uu____4662 = (sub_prob scope1 args q)
in (match (uu____4662) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (uu____4407) with
| (tc, probs) -> begin
(

let uu____4680 = (match (q) with
| (Some (b), uu____4706, uu____4707) -> begin
(

let uu____4715 = (

let uu____4719 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (uu____4719)::args)
in ((Some (b)), ((b)::scope1), (uu____4715)))
end
| uu____4737 -> begin
((None), (scope1), (args))
end)
in (match (uu____4680) with
| (bopt, scope2, args1) -> begin
(

let uu____4780 = (aux scope2 args1 qs2)
in (match (uu____4780) with
| (sub_probs, tcs, f) -> begin
(

let f1 = (match (bopt) with
| None -> begin
(

let uu____4801 = (

let uu____4803 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::uu____4803)
in (FStar_Syntax_Util.mk_conj_l uu____4801))
end
| Some (b) -> begin
(

let u_b = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst b).FStar_Syntax_Syntax.sort)
in (

let uu____4816 = (

let uu____4818 = (FStar_Syntax_Util.mk_forall u_b (Prims.fst b) f)
in (

let uu____4819 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (uu____4818)::uu____4819))
in (FStar_Syntax_Util.mk_conj_l uu____4816)))
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
(((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) * FStar_Syntax_Syntax.arg Prims.list * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list))


let rigid_rigid : Prims.int = (Prims.parse_int "0")


let flex_rigid_eq : Prims.int = (Prims.parse_int "1")


let flex_refine_inner : Prims.int = (Prims.parse_int "2")


let flex_refine : Prims.int = (Prims.parse_int "3")


let flex_rigid : Prims.int = (Prims.parse_int "4")


let rigid_flex : Prims.int = (Prims.parse_int "5")


let refine_flex : Prims.int = (Prims.parse_int "6")


let flex_flex : Prims.int = (Prims.parse_int "7")


let compress_tprob = (fun wl p -> (

let uu___146_4872 = p
in (

let uu____4875 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____4876 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___146_4872.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____4875; FStar_TypeChecker_Common.relation = uu___146_4872.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____4876; FStar_TypeChecker_Common.element = uu___146_4872.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___146_4872.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___146_4872.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___146_4872.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___146_4872.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___146_4872.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p1) -> begin
(

let uu____4886 = (compress_tprob wl p1)
in (FStar_All.pipe_right uu____4886 (fun _0_41 -> FStar_TypeChecker_Common.TProb (_0_41))))
end
| FStar_TypeChecker_Common.CProb (uu____4891) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (

let uu____4905 = (compress_prob wl pr)
in (FStar_All.pipe_right uu____4905 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____4911 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____4911) with
| (lh, uu____4924) -> begin
(

let uu____4939 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____4939) with
| (rh, uu____4952) -> begin
(

let uu____4967 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____4976), FStar_Syntax_Syntax.Tm_uvar (uu____4977)) -> begin
((flex_flex), (tp))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when ((tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____5002), uu____5003) -> begin
(

let uu____5012 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (uu____5012) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((flex_rigid), (tp))
end
| uu____5052 -> begin
(

let rank = (

let uu____5059 = (is_top_level_prob prob)
in (match (uu____5059) with
| true -> begin
flex_refine
end
| uu____5060 -> begin
flex_refine_inner
end))
in (

let uu____5061 = (

let uu___147_5064 = tp
in (

let uu____5067 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___147_5064.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___147_5064.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___147_5064.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____5067; FStar_TypeChecker_Common.element = uu___147_5064.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___147_5064.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___147_5064.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___147_5064.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___147_5064.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___147_5064.FStar_TypeChecker_Common.rank}))
in ((rank), (uu____5061))))
end)
end))
end
| (uu____5077, FStar_Syntax_Syntax.Tm_uvar (uu____5078)) -> begin
(

let uu____5087 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (uu____5087) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((rigid_flex), (tp))
end
| uu____5127 -> begin
(

let uu____5133 = (

let uu___148_5138 = tp
in (

let uu____5141 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___148_5138.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____5141; FStar_TypeChecker_Common.relation = uu___148_5138.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___148_5138.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___148_5138.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___148_5138.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___148_5138.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___148_5138.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___148_5138.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___148_5138.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (uu____5133)))
end)
end))
end
| (uu____5157, uu____5158) -> begin
((rigid_rigid), (tp))
end)
in (match (uu____4967) with
| (rank, tp1) -> begin
(

let uu____5169 = (FStar_All.pipe_right (

let uu___149_5172 = tp1
in {FStar_TypeChecker_Common.pid = uu___149_5172.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___149_5172.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___149_5172.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___149_5172.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___149_5172.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___149_5172.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___149_5172.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___149_5172.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___149_5172.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _0_42 -> FStar_TypeChecker_Common.TProb (_0_42)))
in ((rank), (uu____5169)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____5178 = (FStar_All.pipe_right (

let uu___150_5181 = cp
in {FStar_TypeChecker_Common.pid = uu___150_5181.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___150_5181.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___150_5181.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___150_5181.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___150_5181.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___150_5181.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___150_5181.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___150_5181.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___150_5181.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _0_43 -> FStar_TypeChecker_Common.CProb (_0_43)))
in ((rigid_rigid), (uu____5178)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun uu____5213 probs -> (match (uu____5213) with
| (min_rank, min1, out) -> begin
(match (probs) with
| [] -> begin
((min1), (out), (min_rank))
end
| (hd1)::tl1 -> begin
(

let uu____5243 = (rank wl hd1)
in (match (uu____5243) with
| (rank1, hd2) -> begin
(match ((rank1 <= flex_rigid_eq)) with
| true -> begin
(match (min1) with
| None -> begin
((Some (hd2)), ((FStar_List.append out tl1)), (rank1))
end
| Some (m) -> begin
((Some (hd2)), ((FStar_List.append out ((m)::tl1))), (rank1))
end)
end
| uu____5268 -> begin
(match ((rank1 < min_rank)) with
| true -> begin
(match (min1) with
| None -> begin
(aux ((rank1), (Some (hd2)), (out)) tl1)
end
| Some (m) -> begin
(aux ((rank1), (Some (hd2)), ((m)::out)) tl1)
end)
end
| uu____5284 -> begin
(aux ((min_rank), (min1), ((hd2)::out)) tl1)
end)
end)
end))
end)
end))
in (aux (((flex_flex + (Prims.parse_int "1"))), (None), ([])) wl.attempting)))


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
| uu____5308 -> begin
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
| uu____5320 -> begin
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
| uu____5332 -> begin
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

let uu____5369 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____5369) with
| (k, uu____5373) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| uu____5378 -> begin
false
end)
end)))))
end
| uu____5379 -> begin
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

let uu____5422 = (really_solve_universe_eq pid_orig wl1 u13 u23)
in (match (uu____5422) with
| USolved (wl2) -> begin
(aux wl2 us12 us22)
end
| failed -> begin
failed
end))
end
| uu____5425 -> begin
USolved (wl1)
end))
in (aux wl us1 us2))
end
| uu____5430 -> begin
(

let uu____5431 = (

let uu____5432 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____5433 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" uu____5432 uu____5433)))
in UFailed (uu____5431))
end)
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(

let rec aux = (fun wl1 us1 -> (match (us1) with
| [] -> begin
USolved (wl1)
end
| (u)::us2 -> begin
(

let uu____5450 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____5450) with
| USolved (wl2) -> begin
(aux wl2 us2)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____5453 -> begin
(

let uu____5456 = (

let uu____5457 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____5458 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" uu____5457 uu____5458 msg)))
in UFailed (uu____5456))
end))
in (match (((u11), (u21))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(

let uu____5465 = (

let uu____5466 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____5467 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____5466 uu____5467)))
in (failwith uu____5465))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((x.FStar_Ident.idText = y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____5470 -> begin
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

let uu____5479 = (FStar_Unionfind.equivalent v1 v2)
in (match (uu____5479) with
| true -> begin
USolved (wl)
end
| uu____5481 -> begin
(

let wl1 = (extend_solution pid_orig ((UNIV (((v1), (u21))))::[]) wl)
in USolved (wl1))
end))
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____5492 = (occurs_univ v1 u3)
in (match (uu____5492) with
| true -> begin
(

let uu____5493 = (

let uu____5494 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____5495 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____5494 uu____5495)))
in (try_umax_components u11 u21 uu____5493))
end
| uu____5496 -> begin
(

let uu____5497 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____5497))
end)))
end
| ((FStar_Syntax_Syntax.U_max (_), _)) | ((_, FStar_Syntax_Syntax.U_max (_))) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____5504 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____5507 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____5507) with
| true -> begin
USolved (wl)
end
| uu____5508 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| ((FStar_Syntax_Syntax.U_succ (_), FStar_Syntax_Syntax.U_zero)) | ((FStar_Syntax_Syntax.U_succ (_), FStar_Syntax_Syntax.U_name (_))) | ((FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ (_))) | ((FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name (_))) | ((FStar_Syntax_Syntax.U_name (_), FStar_Syntax_Syntax.U_succ (_))) | ((FStar_Syntax_Syntax.U_name (_), FStar_Syntax_Syntax.U_zero)) -> begin
UFailed ("Incompatible universes")
end))))))


let solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (match (wl.tcenv.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
USolved (wl)
end
| uu____5529 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders = (fun bc1 bc2 -> (

let uu____5578 = bc1
in (match (uu____5578) with
| (bs1, mk_cod1) -> begin
(

let uu____5603 = bc2
in (match (uu____5603) with
| (bs2, mk_cod2) -> begin
(

let curry = (fun n1 bs mk_cod -> (

let uu____5650 = (FStar_Util.first_N n1 bs)
in (match (uu____5650) with
| (bs3, rest) -> begin
(

let uu____5664 = (mk_cod rest)
in ((bs3), (uu____5664)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(

let uu____5682 = (

let uu____5686 = (mk_cod1 [])
in ((bs1), (uu____5686)))
in (

let uu____5688 = (

let uu____5692 = (mk_cod2 [])
in ((bs2), (uu____5692)))
in ((uu____5682), (uu____5688))))
end
| uu____5700 -> begin
(match ((l1 > l2)) with
| true -> begin
(

let uu____5714 = (curry l2 bs1 mk_cod1)
in (

let uu____5721 = (

let uu____5725 = (mk_cod2 [])
in ((bs2), (uu____5725)))
in ((uu____5714), (uu____5721))))
end
| uu____5733 -> begin
(

let uu____5734 = (

let uu____5738 = (mk_cod1 [])
in ((bs1), (uu____5738)))
in (

let uu____5740 = (curry l1 bs2 mk_cod2)
in ((uu____5734), (uu____5740))))
end)
end))))
end))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____5844 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5844) with
| true -> begin
(

let uu____5845 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" uu____5845))
end
| uu____5846 -> begin
()
end));
(

let uu____5847 = (next_prob probs)
in (match (uu____5847) with
| (Some (hd1), tl1, rank1) -> begin
(

let probs1 = (

let uu___151_5860 = probs
in {attempting = tl1; wl_deferred = uu___151_5860.wl_deferred; ctr = uu___151_5860.ctr; defer_ok = uu___151_5860.defer_ok; smt_ok = uu___151_5860.smt_ok; tcenv = uu___151_5860.tcenv})
in (match (hd1) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs1)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match ((((not (probs1.defer_ok)) && (flex_refine_inner <= rank1)) && (rank1 <= flex_rigid))) with
| true -> begin
(

let uu____5867 = (solve_flex_rigid_join env tp probs1)
in (match (uu____5867) with
| None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| Some (wl) -> begin
(solve env wl)
end))
end
| uu____5870 -> begin
(match ((((not (probs1.defer_ok)) && (rigid_flex <= rank1)) && (rank1 <= refine_flex))) with
| true -> begin
(

let uu____5871 = (solve_rigid_flex_meet env tp probs1)
in (match (uu____5871) with
| None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| Some (wl) -> begin
(solve env wl)
end))
end
| uu____5874 -> begin
(solve_t' env (maybe_invert tp) probs1)
end)
end)
end))
end
| (None, uu____5875, uu____5876) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| uu____5885 -> begin
(

let uu____5890 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____5918 -> (match (uu____5918) with
| (c, uu____5923, uu____5924) -> begin
(c < probs.ctr)
end))))
in (match (uu____5890) with
| (attempt1, rest) -> begin
(match (attempt1) with
| [] -> begin
(

let uu____5946 = (FStar_List.map (fun uu____5952 -> (match (uu____5952) with
| (uu____5958, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (uu____5946))
end
| uu____5961 -> begin
(

let uu____5966 = (

let uu___152_5967 = probs
in (

let uu____5968 = (FStar_All.pipe_right attempt1 (FStar_List.map (fun uu____5977 -> (match (uu____5977) with
| (uu____5981, uu____5982, y) -> begin
y
end))))
in {attempting = uu____5968; wl_deferred = rest; ctr = uu___152_5967.ctr; defer_ok = uu___152_5967.defer_ok; smt_ok = uu___152_5967.smt_ok; tcenv = uu___152_5967.tcenv}))
in (solve env uu____5966))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____5989 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____5989) with
| USolved (wl1) -> begin
(

let uu____5991 = (solve_prob orig None [] wl1)
in (solve env uu____5991))
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

let uu____6025 = (solve_universe_eq (p_pid orig) wl1 u1 u2)
in (match (uu____6025) with
| USolved (wl2) -> begin
(aux wl2 us11 us21)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____6028 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t11 = (whnf env t1)
in (

let t21 = (whnf env t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = uu____6036; FStar_Syntax_Syntax.pos = uu____6037; FStar_Syntax_Syntax.vars = uu____6038}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = uu____6041; FStar_Syntax_Syntax.pos = uu____6042; FStar_Syntax_Syntax.vars = uu____6043}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____6059 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____6067 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6067) with
| true -> begin
(

let uu____6068 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" uu____6068 msg))
end
| uu____6069 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____6070 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> ((

let uu____6076 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6076) with
| true -> begin
(

let uu____6077 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" uu____6077))
end
| uu____6078 -> begin
()
end));
(

let uu____6079 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____6079) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let uu____6121 = (head_matches_delta env () t1 t2)
in (match (uu____6121) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (uu____6143) -> begin
None
end
| FullMatch -> begin
(match (ts) with
| None -> begin
Some (((t1), ([])))
end
| Some (t11, t21) -> begin
Some (((t11), ([])))
end)
end
| HeadMatch -> begin
(

let uu____6169 = (match (ts) with
| Some (t11, t21) -> begin
(

let uu____6178 = (FStar_Syntax_Subst.compress t11)
in (

let uu____6179 = (FStar_Syntax_Subst.compress t21)
in ((uu____6178), (uu____6179))))
end
| None -> begin
(

let uu____6182 = (FStar_Syntax_Subst.compress t1)
in (

let uu____6183 = (FStar_Syntax_Subst.compress t2)
in ((uu____6182), (uu____6183))))
end)
in (match (uu____6169) with
| (t11, t21) -> begin
(

let eq_prob = (fun t12 t22 -> (

let uu____6205 = (new_problem env t12 FStar_TypeChecker_Common.EQ t22 None t12.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _0_44 -> FStar_TypeChecker_Common.TProb (_0_44)) uu____6205)))
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(

let uu____6228 = (

let uu____6234 = (

let uu____6237 = (

let uu____6240 = (

let uu____6241 = (

let uu____6246 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (uu____6246)))
in FStar_Syntax_Syntax.Tm_refine (uu____6241))
in (FStar_Syntax_Syntax.mk uu____6240))
in (uu____6237 None t11.FStar_Syntax_Syntax.pos))
in (

let uu____6259 = (

let uu____6261 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (uu____6261)::[])
in ((uu____6234), (uu____6259))))
in Some (uu____6228))
end
| (uu____6270, FStar_Syntax_Syntax.Tm_refine (x, uu____6272)) -> begin
(

let uu____6277 = (

let uu____6281 = (

let uu____6283 = (eq_prob x.FStar_Syntax_Syntax.sort t11)
in (uu____6283)::[])
in ((t11), (uu____6281)))
in Some (uu____6277))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____6289), uu____6290) -> begin
(

let uu____6295 = (

let uu____6299 = (

let uu____6301 = (eq_prob x.FStar_Syntax_Syntax.sort t21)
in (uu____6301)::[])
in ((t21), (uu____6299)))
in Some (uu____6295))
end
| uu____6306 -> begin
(

let uu____6309 = (FStar_Syntax_Util.head_and_args t11)
in (match (uu____6309) with
| (head1, uu____6324) -> begin
(

let uu____6339 = (

let uu____6340 = (FStar_Syntax_Util.un_uinst head1)
in uu____6340.FStar_Syntax_Syntax.n)
in (match (uu____6339) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____6347; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (i); FStar_Syntax_Syntax.fv_qual = uu____6349}) -> begin
(

let prev = (match ((i > (Prims.parse_int "1"))) with
| true -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i - (Prims.parse_int "1")))
end
| uu____6355 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
in (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t21)
in (disjoin t12 t22))))
end
| uu____6358 -> begin
None
end))
end))
end))
end))
end)
end)))
in (

let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____6367) -> begin
(

let uu____6380 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___126_6389 -> (match (uu___126_6389) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| Some (rank1) when (is_rigid_flex rank1) -> begin
(

let uu____6394 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.rhs)
in (match (uu____6394) with
| (u', uu____6405) -> begin
(

let uu____6420 = (

let uu____6421 = (whnf env u')
in uu____6421.FStar_Syntax_Syntax.n)
in (match (uu____6420) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____6425) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____6441 -> begin
false
end))
end))
end
| uu____6442 -> begin
false
end)
end
| uu____6444 -> begin
false
end))))
in (match (uu____6380) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun uu____6465 tps -> (match (uu____6465) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____6492 = (

let uu____6497 = (whnf env hd1.FStar_TypeChecker_Common.lhs)
in (disjoin bound uu____6497))
in (match (uu____6492) with
| Some (bound1, sub1) -> begin
(make_lower_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| None -> begin
None
end))
end
| uu____6516 -> begin
None
end)
end))
in (

let uu____6521 = (

let uu____6526 = (

let uu____6530 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((uu____6530), ([])))
in (make_lower_bound uu____6526 lower_bounds))
in (match (uu____6521) with
| None -> begin
((

let uu____6537 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6537) with
| true -> begin
(FStar_Util.print_string "No lower bounds\n")
end
| uu____6538 -> begin
()
end));
None;
)
end
| Some (lhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in ((

let uu____6550 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6550) with
| true -> begin
(

let wl' = (

let uu___153_6552 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___153_6552.wl_deferred; ctr = uu___153_6552.ctr; defer_ok = uu___153_6552.defer_ok; smt_ok = uu___153_6552.smt_ok; tcenv = uu___153_6552.tcenv})
in (

let uu____6553 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" uu____6553)))
end
| uu____6554 -> begin
()
end));
(

let uu____6555 = (solve_t env eq_prob (

let uu___154_6556 = wl
in {attempting = sub_probs; wl_deferred = uu___154_6556.wl_deferred; ctr = uu___154_6556.ctr; defer_ok = uu___154_6556.defer_ok; smt_ok = uu___154_6556.smt_ok; tcenv = uu___154_6556.tcenv}))
in (match (uu____6555) with
| Success (uu____6558) -> begin
(

let wl1 = (

let uu___155_6560 = wl
in {attempting = rest; wl_deferred = uu___155_6560.wl_deferred; ctr = uu___155_6560.ctr; defer_ok = uu___155_6560.defer_ok; smt_ok = uu___155_6560.smt_ok; tcenv = uu___155_6560.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl1)
in (

let uu____6562 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p None [] wl3)) wl2 lower_bounds)
in Some (wl2))))
end
| uu____6565 -> begin
None
end));
))
end)))
end))
end
| uu____6566 -> begin
(failwith "Impossible: Not a rigid-flex")
end)))
end));
))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> ((

let uu____6573 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6573) with
| true -> begin
(

let uu____6574 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" uu____6574))
end
| uu____6575 -> begin
()
end));
(

let uu____6576 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____6576) with
| (u, args) -> begin
(

let uu____6603 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (uu____6603) with
| (ok, head_match1, partial_match, fallback, failed_match) -> begin
(

let max1 = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____6622 -> begin
i
end))
in (

let base_types_match = (fun t1 t2 -> (

let uu____6634 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____6634) with
| (h1, args1) -> begin
(

let uu____6662 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____6662) with
| (h2, uu____6675) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
(

let uu____6694 = (FStar_Syntax_Syntax.fv_eq tc1 tc2)
in (match (uu____6694) with
| true -> begin
(match (((FStar_List.length args1) = (Prims.parse_int "0"))) with
| true -> begin
Some ([])
end
| uu____6706 -> begin
(

let uu____6707 = (

let uu____6709 = (

let uu____6710 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_45 -> FStar_TypeChecker_Common.TProb (_0_45)) uu____6710))
in (uu____6709)::[])
in Some (uu____6707))
end)
end
| uu____6716 -> begin
None
end))
end
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(match ((FStar_Syntax_Syntax.bv_eq a b)) with
| true -> begin
(match (((FStar_List.length args1) = (Prims.parse_int "0"))) with
| true -> begin
Some ([])
end
| uu____6731 -> begin
(

let uu____6732 = (

let uu____6734 = (

let uu____6735 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_46 -> FStar_TypeChecker_Common.TProb (_0_46)) uu____6735))
in (uu____6734)::[])
in Some (uu____6732))
end)
end
| uu____6741 -> begin
None
end)
end
| uu____6743 -> begin
None
end)
end))
end)))
in (

let conjoin = (fun t1 t2 -> (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(

let m = (base_types_match x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m1) -> begin
(

let x1 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let subst1 = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x1))))::[]
in (

let phi11 = (FStar_Syntax_Subst.subst subst1 phi1)
in (

let phi21 = (FStar_Syntax_Subst.subst subst1 phi2)
in (

let uu____6809 = (

let uu____6815 = (

let uu____6818 = (FStar_Syntax_Util.mk_conj phi11 phi21)
in (FStar_Syntax_Util.refine x1 uu____6818))
in ((uu____6815), (m1)))
in Some (uu____6809))))))
end))
end
| (uu____6827, FStar_Syntax_Syntax.Tm_refine (y, uu____6829)) -> begin
(

let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m1) -> begin
Some (((t2), (m1)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____6861), uu____6862) -> begin
(

let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m1) -> begin
Some (((t1), (m1)))
end))
end
| uu____6893 -> begin
(

let m = (base_types_match t1 t2)
in (match (m) with
| None -> begin
None
end
| Some (m1) -> begin
Some (((t1), (m1)))
end))
end))
in (

let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____6927) -> begin
(

let uu____6940 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___127_6949 -> (match (uu___127_6949) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| Some (rank1) when (is_flex_rigid rank1) -> begin
(

let uu____6954 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.lhs)
in (match (uu____6954) with
| (u', uu____6965) -> begin
(

let uu____6980 = (

let uu____6981 = (whnf env u')
in uu____6981.FStar_Syntax_Syntax.n)
in (match (uu____6980) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____6985) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____7001 -> begin
false
end))
end))
end
| uu____7002 -> begin
false
end)
end
| uu____7004 -> begin
false
end))))
in (match (uu____6940) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun uu____7029 tps -> (match (uu____7029) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____7070 = (

let uu____7077 = (whnf env hd1.FStar_TypeChecker_Common.rhs)
in (conjoin bound uu____7077))
in (match (uu____7070) with
| Some (bound1, sub1) -> begin
(make_upper_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| None -> begin
None
end))
end
| uu____7112 -> begin
None
end)
end))
in (

let uu____7119 = (

let uu____7126 = (

let uu____7132 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((uu____7132), ([])))
in (make_upper_bound uu____7126 upper_bounds))
in (match (uu____7119) with
| None -> begin
((

let uu____7141 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____7141) with
| true -> begin
(FStar_Util.print_string "No upper bounds\n")
end
| uu____7142 -> begin
()
end));
None;
)
end
| Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in ((

let uu____7160 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____7160) with
| true -> begin
(

let wl' = (

let uu___156_7162 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___156_7162.wl_deferred; ctr = uu___156_7162.ctr; defer_ok = uu___156_7162.defer_ok; smt_ok = uu___156_7162.smt_ok; tcenv = uu___156_7162.tcenv})
in (

let uu____7163 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" uu____7163)))
end
| uu____7164 -> begin
()
end));
(

let uu____7165 = (solve_t env eq_prob (

let uu___157_7166 = wl
in {attempting = sub_probs; wl_deferred = uu___157_7166.wl_deferred; ctr = uu___157_7166.ctr; defer_ok = uu___157_7166.defer_ok; smt_ok = uu___157_7166.smt_ok; tcenv = uu___157_7166.tcenv}))
in (match (uu____7165) with
| Success (uu____7168) -> begin
(

let wl1 = (

let uu___158_7170 = wl
in {attempting = rest; wl_deferred = uu___158_7170.wl_deferred; ctr = uu___158_7170.ctr; defer_ok = uu___158_7170.defer_ok; smt_ok = uu___158_7170.smt_ok; tcenv = uu___158_7170.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl1)
in (

let uu____7172 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p None [] wl3)) wl2 upper_bounds)
in Some (wl2))))
end
| uu____7175 -> begin
None
end));
))
end)))
end))
end
| uu____7176 -> begin
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

let uu____7241 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____7241) with
| true -> begin
(

let uu____7242 = (prob_to_string env1 rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" uu____7242))
end
| uu____7243 -> begin
()
end));
(

let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl ((((rhs_prob)::[]), (formula))));
))
end
| (((hd1, imp))::xs1, ((hd2, imp'))::ys1) when (imp = imp') -> begin
(

let hd11 = (

let uu___159_7274 = hd1
in (

let uu____7275 = (FStar_Syntax_Subst.subst subst1 hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___159_7274.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___159_7274.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7275}))
in (

let hd21 = (

let uu___160_7279 = hd2
in (

let uu____7280 = (FStar_Syntax_Subst.subst subst1 hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___160_7279.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___160_7279.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7280}))
in (

let prob = (

let uu____7284 = (

let uu____7287 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd11.FStar_Syntax_Syntax.sort uu____7287 hd21.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _0_47 -> FStar_TypeChecker_Common.TProb (_0_47)) uu____7284))
in (

let hd12 = (FStar_Syntax_Syntax.freshen_bv hd11)
in (

let subst2 = (

let uu____7295 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd12))))::uu____7295)
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 hd12)
in (

let uu____7298 = (aux ((((hd12), (imp)))::scope) env2 subst2 xs1 ys1)
in (match (uu____7298) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi1 = (

let uu____7316 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (

let uu____7319 = (close_forall env2 ((((hd12), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj uu____7316 uu____7319)))
in ((

let uu____7325 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____7325) with
| true -> begin
(

let uu____7326 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____7327 = (FStar_Syntax_Print.bv_to_string hd12)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" uu____7326 uu____7327)))
end
| uu____7328 -> begin
()
end));
FStar_Util.Inl ((((prob)::sub_probs), (phi1)));
))
end
| fail -> begin
fail
end))))))))
end
| uu____7342 -> begin
FStar_Util.Inr ("arity or argument-qualifier mismatch")
end))
in (

let scope = (p_scope orig)
in (

let uu____7348 = (aux scope env [] bs1 bs2)
in (match (uu____7348) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let wl1 = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl1)))
end)))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let uu____7364 = (compress_tprob wl problem)
in (solve_t' env uu____7364 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer1 = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env1 orig wl1 head1 head2 t1 t2 -> (

let uu____7397 = (head_matches_delta env1 wl1 t1 t2)
in (match (uu____7397) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____7414), uu____7415) -> begin
(

let may_relate = (fun head3 -> (

let uu____7430 = (

let uu____7431 = (FStar_Syntax_Util.un_uinst head3)
in uu____7431.FStar_Syntax_Syntax.n)
in (match (uu____7430) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____7437 -> begin
false
end)))
in (

let uu____7438 = (((may_relate head1) || (may_relate head2)) && wl1.smt_ok)
in (match (uu____7438) with
| true -> begin
(

let guard = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_eq2 env1 t1 t2)
end
| uu____7440 -> begin
(

let has_type_guard = (fun t11 t21 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t11 t t21)
end
| None -> begin
(

let x = (FStar_Syntax_Syntax.new_bv None t11)
in (

let u_x = (env1.FStar_TypeChecker_Env.universe_of env1 t11)
in (

let uu____7455 = (

let uu____7456 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t11 uu____7456 t21))
in (FStar_Syntax_Util.mk_forall u_x x uu____7455))))
end))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB)) with
| true -> begin
(has_type_guard t1 t2)
end
| uu____7457 -> begin
(has_type_guard t2 t1)
end))
end)
in (

let uu____7458 = (solve_prob orig (Some (guard)) [] wl1)
in (solve env1 uu____7458)))
end
| uu____7459 -> begin
(giveup env1 "head mismatch" orig)
end)))
end
| (uu____7460, Some (t11, t21)) -> begin
(solve_t env1 (

let uu___161_7468 = problem
in {FStar_TypeChecker_Common.pid = uu___161_7468.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___161_7468.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___161_7468.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___161_7468.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___161_7468.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___161_7468.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___161_7468.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___161_7468.FStar_TypeChecker_Common.rank}) wl1)
end
| (uu____7469, None) -> begin
((

let uu____7476 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____7476) with
| true -> begin
(

let uu____7477 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____7478 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____7479 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____7480 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" uu____7477 uu____7478 uu____7479 uu____7480)))))
end
| uu____7481 -> begin
()
end));
(

let uu____7482 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____7482) with
| (head11, args1) -> begin
(

let uu____7508 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____7508) with
| (head21, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((nargs <> (FStar_List.length args2))) with
| true -> begin
(

let uu____7548 = (

let uu____7549 = (FStar_Syntax_Print.term_to_string head11)
in (

let uu____7550 = (args_to_string args1)
in (

let uu____7551 = (FStar_Syntax_Print.term_to_string head21)
in (

let uu____7552 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____7549 uu____7550 uu____7551 uu____7552)))))
in (giveup env1 uu____7548 orig))
end
| uu____7553 -> begin
(

let uu____7554 = ((nargs = (Prims.parse_int "0")) || (

let uu____7557 = (FStar_Syntax_Util.eq_args args1 args2)
in (uu____7557 = FStar_Syntax_Util.Equal)))
in (match (uu____7554) with
| true -> begin
(

let uu____7558 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____7558) with
| USolved (wl2) -> begin
(

let uu____7560 = (solve_prob orig None [] wl2)
in (solve env1 uu____7560))
end
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end))
end
| uu____7563 -> begin
(

let uu____7564 = (base_and_refinement env1 wl1 t1)
in (match (uu____7564) with
| (base1, refinement1) -> begin
(

let uu____7590 = (base_and_refinement env1 wl1 t2)
in (match (uu____7590) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (None, None) -> begin
(

let uu____7644 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____7644) with
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end
| USolved (wl2) -> begin
(

let subprobs = (FStar_List.map2 (fun uu____7654 uu____7655 -> (match (((uu____7654), (uu____7655))) with
| ((a, uu____7665), (a', uu____7667)) -> begin
(

let uu____7672 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _0_48 -> FStar_TypeChecker_Common.TProb (_0_48)) uu____7672))
end)) args1 args2)
in (

let formula = (

let uu____7678 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____7678))
in (

let wl3 = (solve_prob orig (Some (formula)) [] wl2)
in (solve env1 (attempt subprobs wl3)))))
end))
end
| uu____7682 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env1 (

let uu___162_7715 = problem
in {FStar_TypeChecker_Common.pid = uu___162_7715.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___162_7715.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___162_7715.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_7715.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_7715.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_7715.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_7715.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_7715.FStar_TypeChecker_Common.rank}) wl1)))
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

let uu____7735 = p
in (match (uu____7735) with
| (((u, k), xs, c), ps, (h, uu____7746, qs)) -> begin
(

let xs1 = (sn_binders env1 xs)
in (

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____7795 = (imitation_sub_probs orig env1 xs1 ps qs)
in (match (uu____7795) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (

let uu____7809 = (h gs_xs)
in (

let uu____7810 = (

let uu____7817 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_49 -> FStar_Util.Inl (_0_49)))
in (FStar_All.pipe_right uu____7817 (fun _0_50 -> Some (_0_50))))
in (FStar_Syntax_Util.abs xs1 uu____7809 uu____7810)))
in ((

let uu____7848 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____7848) with
| true -> begin
(

let uu____7849 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____7850 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____7851 = (FStar_Syntax_Print.term_to_string im)
in (

let uu____7852 = (FStar_Syntax_Print.tag_of_term im)
in (

let uu____7853 = (

let uu____7854 = (FStar_List.map (prob_to_string env1) sub_probs)
in (FStar_All.pipe_right uu____7854 (FStar_String.concat ", ")))
in (

let uu____7857 = (FStar_TypeChecker_Normalize.term_to_string env1 formula)
in (FStar_Util.print6 "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" uu____7849 uu____7850 uu____7851 uu____7852 uu____7853 uu____7857)))))))
end
| uu____7858 -> begin
()
end));
(

let wl2 = (solve_prob orig (Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl1)
in (solve env1 (attempt sub_probs wl2)));
))
end))))
end)))
in (

let imitate' = (fun orig env1 wl1 uu___128_7875 -> (match (uu___128_7875) with
| None -> begin
(giveup env1 "unable to compute subterms" orig)
end
| Some (p) -> begin
(imitate orig env1 wl1 p)
end))
in (

let project = (fun orig env1 wl1 i p -> (

let uu____7904 = p
in (match (uu____7904) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____7962 = (FStar_List.nth ps i)
in (match (uu____7962) with
| (pi, uu____7965) -> begin
(

let uu____7970 = (FStar_List.nth xs i)
in (match (uu____7970) with
| (xi, uu____7977) -> begin
(

let rec gs = (fun k -> (

let uu____7986 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____7986) with
| (bs, k1) -> begin
(

let rec aux = (fun subst1 bs1 -> (match (bs1) with
| [] -> begin
(([]), ([]))
end
| ((a, uu____8038))::tl1 -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst1 a.FStar_Syntax_Syntax.sort)
in (

let uu____8046 = (new_uvar r xs k_a)
in (match (uu____8046) with
| (gi_xs, gi) -> begin
(

let gi_xs1 = (FStar_TypeChecker_Normalize.eta_expand env1 gi_xs)
in (

let gi_ps = ((FStar_Syntax_Syntax.mk_Tm_app gi ps) (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((a), (gi_xs1))))::subst1
in (

let uu____8065 = (aux subst2 tl1)
in (match (uu____8065) with
| (gi_xs', gi_ps') -> begin
(

let uu____8080 = (

let uu____8082 = (FStar_Syntax_Syntax.as_arg gi_xs1)
in (uu____8082)::gi_xs')
in (

let uu____8083 = (

let uu____8085 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (uu____8085)::gi_ps')
in ((uu____8080), (uu____8083))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in (

let uu____8088 = (

let uu____8089 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation uu____8089))
in (match (uu____8088) with
| true -> begin
None
end
| uu____8091 -> begin
(

let uu____8092 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (uu____8092) with
| (g_xs, uu____8099) -> begin
(

let xi1 = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (

let uu____8106 = ((FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs) None r)
in (

let uu____8111 = (

let uu____8118 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_51 -> FStar_Util.Inl (_0_51)))
in (FStar_All.pipe_right uu____8118 (fun _0_52 -> Some (_0_52))))
in (FStar_Syntax_Util.abs xs uu____8106 uu____8111)))
in (

let sub1 = (

let uu____8149 = (

let uu____8152 = ((FStar_Syntax_Syntax.mk_Tm_app proj ps) None r)
in (

let uu____8159 = (

let uu____8162 = (FStar_List.map (fun uu____8168 -> (match (uu____8168) with
| (uu____8173, uu____8174, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h uu____8162))
in (mk_problem (p_scope orig) orig uu____8152 (p_rel orig) uu____8159 None "projection")))
in (FStar_All.pipe_left (fun _0_53 -> FStar_TypeChecker_Common.TProb (_0_53)) uu____8149))
in ((

let uu____8184 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____8184) with
| true -> begin
(

let uu____8185 = (FStar_Syntax_Print.term_to_string proj)
in (

let uu____8186 = (prob_to_string env1 sub1)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" uu____8185 uu____8186)))
end
| uu____8187 -> begin
()
end));
(

let wl2 = (

let uu____8189 = (

let uu____8191 = (FStar_All.pipe_left Prims.fst (p_guard sub1))
in Some (uu____8191))
in (solve_prob orig uu____8189 ((TERM (((u), (proj))))::[]) wl1))
in (

let uu____8196 = (solve env1 (attempt ((sub1)::[]) wl2))
in (FStar_All.pipe_left (fun _0_54 -> Some (_0_54)) uu____8196)));
))))
end))
end)))
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl1 -> (

let uu____8220 = lhs
in (match (uu____8220) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let uu____8243 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (uu____8243) with
| (xs, c) -> begin
(match (((FStar_List.length xs) = (FStar_List.length ps))) with
| true -> begin
(

let uu____8265 = (

let uu____8291 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____8291)))
in Some (uu____8265))
end
| uu____8357 -> begin
(

let k_uv1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (

let uu____8374 = (

let uu____8378 = (

let uu____8379 = (FStar_Syntax_Subst.compress k)
in uu____8379.FStar_Syntax_Syntax.n)
in ((uu____8378), (args)))
in (match (uu____8374) with
| (uu____8386, []) -> begin
(

let uu____8388 = (

let uu____8394 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____8394)))
in Some (uu____8388))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(

let uu____8411 = (FStar_Syntax_Util.head_and_args k)
in (match (uu____8411) with
| (uv1, uv_args) -> begin
(

let uu____8440 = (

let uu____8441 = (FStar_Syntax_Subst.compress uv1)
in uu____8441.FStar_Syntax_Syntax.n)
in (match (uu____8440) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____8448) -> begin
(

let uu____8461 = (pat_vars env [] uv_args)
in (match (uu____8461) with
| None -> begin
None
end
| Some (scope) -> begin
(

let xs1 = (FStar_All.pipe_right args (FStar_List.map (fun uu____8475 -> (

let uu____8476 = (

let uu____8477 = (

let uu____8478 = (

let uu____8481 = (

let uu____8482 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8482 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____8481))
in (Prims.fst uu____8478))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) uu____8477))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____8476)))))
in (

let c1 = (

let uu____8488 = (

let uu____8489 = (

let uu____8492 = (

let uu____8493 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8493 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____8492))
in (Prims.fst uu____8489))
in (FStar_Syntax_Syntax.mk_Total uu____8488))
in (

let k' = (FStar_Syntax_Util.arrow xs1 c1)
in (

let uv_sol = (

let uu____8502 = (

let uu____8509 = (

let uu____8515 = (

let uu____8516 = (

let uu____8519 = (

let uu____8520 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8520 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total uu____8519))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8516))
in FStar_Util.Inl (uu____8515))
in Some (uu____8509))
in (FStar_Syntax_Util.abs scope k' uu____8502))
in ((FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)));
Some (((xs1), (c1)));
)))))
end))
end
| uu____8543 -> begin
None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs1, c1), uu____8548) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs1)
in (match ((n_xs = n_args)) with
| true -> begin
(

let uu____8574 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (FStar_All.pipe_right uu____8574 (fun _0_55 -> Some (_0_55))))
end
| uu____8584 -> begin
(match ((n_xs < n_args)) with
| true -> begin
(

let uu____8593 = (FStar_Util.first_N n_xs args)
in (match (uu____8593) with
| (args1, rest) -> begin
(

let uu____8609 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (match (uu____8609) with
| (xs2, c2) -> begin
(

let uu____8617 = (elim (FStar_Syntax_Util.comp_result c2) rest)
in (FStar_Util.bind_opt uu____8617 (fun uu____8628 -> (match (uu____8628) with
| (xs', c3) -> begin
Some ((((FStar_List.append xs2 xs')), (c3)))
end))))
end))
end))
end
| uu____8649 -> begin
(

let uu____8650 = (FStar_Util.first_N n_args xs1)
in (match (uu____8650) with
| (xs2, rest) -> begin
(

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c1))))) None k.FStar_Syntax_Syntax.pos)
in (

let uu____8696 = (

let uu____8699 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs2 uu____8699))
in (FStar_All.pipe_right uu____8696 (fun _0_56 -> Some (_0_56)))))
end))
end)
end)))
end
| uu____8707 -> begin
(

let uu____8711 = (

let uu____8712 = (FStar_Syntax_Print.uvar_to_string uv)
in (

let uu____8716 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____8717 = (FStar_Syntax_Print.term_to_string k_uv1)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" uu____8712 uu____8716 uu____8717))))
in (failwith uu____8711))
end)))
in (

let uu____8721 = (elim k_uv1 ps)
in (FStar_Util.bind_opt uu____8721 (fun uu____8749 -> (match (uu____8749) with
| (xs1, c1) -> begin
(

let uu____8777 = (

let uu____8800 = (decompose env t2)
in ((((((uv), (k_uv1))), (xs1), (c1))), (ps), (uu____8800)))
in Some (uu____8777))
end))))))
end)
end)))
in (

let rec imitate_or_project = (fun n1 stopt i -> (match (((i >= n1) || (FStar_Option.isNone stopt))) with
| true -> begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end
| uu____8869 -> begin
(

let st = (FStar_Option.get stopt)
in (

let tx = (FStar_Unionfind.new_transaction ())
in (match ((i = (~- ((Prims.parse_int "1"))))) with
| true -> begin
(

let uu____8872 = (imitate orig env wl1 st)
in (match (uu____8872) with
| Failed (uu____8877) -> begin
((FStar_Unionfind.rollback tx);
(imitate_or_project n1 stopt (i + (Prims.parse_int "1")));
)
end
| sol -> begin
sol
end))
end
| uu____8882 -> begin
(

let uu____8883 = (project orig env wl1 i st)
in (match (uu____8883) with
| (None) | (Some (Failed (_))) -> begin
((FStar_Unionfind.rollback tx);
(imitate_or_project n1 stopt (i + (Prims.parse_int "1")));
)
end
| Some (sol) -> begin
sol
end))
end)))
end))
in (

let check_head = (fun fvs1 t21 -> (

let uu____8901 = (FStar_Syntax_Util.head_and_args t21)
in (match (uu____8901) with
| (hd1, uu____8912) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| uu____8930 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd1)
in (

let uu____8933 = (FStar_Util.set_is_subset_of fvs_hd fvs1)
in (match (uu____8933) with
| true -> begin
true
end
| uu____8934 -> begin
((

let uu____8936 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8936) with
| true -> begin
(

let uu____8937 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" uu____8937))
end
| uu____8938 -> begin
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

let uu____8945 = (

let uu____8948 = (FStar_Syntax_Util.head_and_args t21)
in (FStar_All.pipe_right uu____8948 Prims.fst))
in (FStar_All.pipe_right uu____8945 FStar_Syntax_Free.names))
in (

let uu____8979 = (FStar_Util.set_is_empty fvs_hd)
in (match (uu____8979) with
| true -> begin
(~- ((Prims.parse_int "1")))
end
| uu____8980 -> begin
(Prims.parse_int "0")
end))))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(

let t11 = (sn env t1)
in (

let t21 = (sn env t2)
in (

let fvs1 = (FStar_Syntax_Free.names t11)
in (

let fvs2 = (FStar_Syntax_Free.names t21)
in (

let uu____8988 = (occurs_check env wl1 ((uv), (k_uv)) t21)
in (match (uu____8988) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____8996 = (

let uu____8997 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____8997))
in (giveup_or_defer1 orig uu____8996))
end
| uu____8998 -> begin
(

let uu____8999 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____8999) with
| true -> begin
(

let uu____9000 = (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t21)) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))
in (match (uu____9000) with
| true -> begin
(

let uu____9001 = (subterms args_lhs)
in (imitate' orig env wl1 uu____9001))
end
| uu____9003 -> begin
((

let uu____9005 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9005) with
| true -> begin
(

let uu____9006 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____9007 = (names_to_string fvs1)
in (

let uu____9008 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" uu____9006 uu____9007 uu____9008))))
end
| uu____9009 -> begin
()
end));
(

let sol = (match (vars) with
| [] -> begin
t21
end
| uu____9013 -> begin
(

let uu____9014 = (sn_binders env vars)
in (u_abs k_uv uu____9014 t21))
end)
in (

let wl2 = (solve_prob orig None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl1)
in (solve env wl2)));
)
end))
end
| uu____9021 -> begin
(match ((((not (patterns_only)) && wl1.defer_ok) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl1))
end
| uu____9022 -> begin
(

let uu____9023 = ((not (patterns_only)) && (check_head fvs1 t21))
in (match (uu____9023) with
| true -> begin
((

let uu____9025 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9025) with
| true -> begin
(

let uu____9026 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____9027 = (names_to_string fvs1)
in (

let uu____9028 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" uu____9026 uu____9027 uu____9028))))
end
| uu____9029 -> begin
()
end));
(

let uu____9030 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____9030 (~- ((Prims.parse_int "1")))));
)
end
| uu____9039 -> begin
(giveup env "free-variable check failed on a non-redex" orig)
end))
end)
end))
end)
end))))))
end
| None when patterns_only -> begin
(giveup env "not a pattern" orig)
end
| None -> begin
(match (wl1.defer_ok) with
| true -> begin
(solve env (defer "not a pattern" orig wl1))
end
| uu____9040 -> begin
(

let uu____9041 = (

let uu____9042 = (FStar_Syntax_Free.names t1)
in (check_head uu____9042 t2))
in (match (uu____9041) with
| true -> begin
(

let im_ok = (imitate_ok t2)
in ((

let uu____9046 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9046) with
| true -> begin
(

let uu____9047 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" uu____9047 (match ((im_ok < (Prims.parse_int "0"))) with
| true -> begin
"imitating"
end
| uu____9048 -> begin
"projecting"
end)))
end
| uu____9049 -> begin
()
end));
(

let uu____9050 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____9050 im_ok));
))
end
| uu____9059 -> begin
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
| uu____9070 -> begin
(

let force_quasi_pattern = (fun xs_opt uu____9092 -> (match (uu____9092) with
| (t, u, k, args) -> begin
(

let uu____9122 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____9122) with
| (all_formals, uu____9133) -> begin
(

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args1 -> (match (((formals), (args1))) with
| ([], []) -> begin
(

let pat_args1 = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun uu____9225 -> (match (uu____9225) with
| (x, imp) -> begin
(

let uu____9232 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____9232), (imp)))
end))))
in (

let pattern_vars1 = (FStar_List.rev pattern_vars)
in (

let kk = (

let uu____9240 = (FStar_Syntax_Util.type_u ())
in (match (uu____9240) with
| (t1, uu____9244) -> begin
(

let uu____9245 = (new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1 t1)
in (Prims.fst uu____9245))
end))
in (

let uu____9248 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk)
in (match (uu____9248) with
| (t', tm_u1) -> begin
(

let uu____9255 = (destruct_flex_t t')
in (match (uu____9255) with
| (uu____9275, u1, k1, uu____9278) -> begin
(

let sol = (

let uu____9306 = (

let uu____9311 = (u_abs k all_formals t')
in ((((u), (k))), (uu____9311)))
in TERM (uu____9306))
in (

let t_app = ((FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1) None t.FStar_Syntax_Syntax.pos)
in ((sol), (((t_app), (u1), (k1), (pat_args1))))))
end))
end)))))
end
| ((formal)::formals1, (hd1)::tl1) -> begin
(

let uu____9371 = (pat_var_opt env pat_args hd1)
in (match (uu____9371) with
| None -> begin
(aux pat_args pattern_vars pattern_var_set formals1 tl1)
end
| Some (y) -> begin
(

let maybe_pat = (match (xs_opt) with
| None -> begin
true
end
| Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun uu____9400 -> (match (uu____9400) with
| (x, uu____9404) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in (match ((not (maybe_pat))) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals1 tl1)
end
| uu____9407 -> begin
(

let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____9410 = (

let uu____9411 = (FStar_Util.set_is_subset_of fvs pattern_var_set)
in (not (uu____9411)))
in (match (uu____9410) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals1 tl1)
end
| uu____9414 -> begin
(

let uu____9415 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) uu____9415 formals1 tl1))
end)))
end))
end))
end
| uu____9421 -> begin
(failwith "Impossible")
end))
in (

let uu____9432 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] uu____9432 all_formals args)))
end))
end))
in (

let solve_both_pats = (fun wl1 uu____9480 uu____9481 r -> (match (((uu____9480), (uu____9481))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
(

let uu____9635 = ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys))
in (match (uu____9635) with
| true -> begin
(

let uu____9639 = (solve_prob orig None [] wl1)
in (solve env uu____9639))
end
| uu____9640 -> begin
(

let xs1 = (sn_binders env xs)
in (

let ys1 = (sn_binders env ys)
in (

let zs = (intersect_vars xs1 ys1)
in ((

let uu____9654 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9654) with
| true -> begin
(

let uu____9655 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____9656 = (FStar_Syntax_Print.binders_to_string ", " ys1)
in (

let uu____9657 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (

let uu____9658 = (FStar_Syntax_Print.term_to_string k1)
in (

let uu____9659 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" uu____9655 uu____9656 uu____9657 uu____9658 uu____9659))))))
end
| uu____9660 -> begin
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

let uu____9701 = (FStar_Syntax_Util.subst_of_list xs2 args)
in (FStar_Syntax_Subst.subst uu____9701 k))
end
| uu____9703 -> begin
(match ((args_len < xs_len)) with
| true -> begin
(

let uu____9709 = (FStar_Util.first_N args_len xs2)
in (match (uu____9709) with
| (xs3, xs_rest) -> begin
(

let k3 = (

let uu____9739 = (FStar_Syntax_Syntax.mk_GTotal k)
in (FStar_Syntax_Util.arrow xs_rest uu____9739))
in (

let uu____9742 = (FStar_Syntax_Util.subst_of_list xs3 args)
in (FStar_Syntax_Subst.subst uu____9742 k3)))
end))
end
| uu____9744 -> begin
(

let uu____9745 = (

let uu____9746 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____9747 = (FStar_Syntax_Print.binders_to_string ", " xs2)
in (

let uu____9748 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" uu____9746 uu____9747 uu____9748))))
in (failwith uu____9745))
end)
end))))
in (

let uu____9749 = (

let uu____9755 = (

let uu____9763 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals uu____9763))
in (match (uu____9755) with
| (bs, k1') -> begin
(

let uu____9781 = (

let uu____9789 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals uu____9789))
in (match (uu____9781) with
| (cs, k2') -> begin
(

let k1'_xs = (subst_k k1' bs args1)
in (

let k2'_ys = (subst_k k2' cs args2)
in (

let sub_prob = (

let uu____9810 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_57 -> FStar_TypeChecker_Common.TProb (_0_57)) uu____9810))
in (

let uu____9815 = (

let uu____9818 = (

let uu____9819 = (FStar_Syntax_Subst.compress k1')
in uu____9819.FStar_Syntax_Syntax.n)
in (

let uu____9822 = (

let uu____9823 = (FStar_Syntax_Subst.compress k2')
in uu____9823.FStar_Syntax_Syntax.n)
in ((uu____9818), (uu____9822))))
in (match (uu____9815) with
| (FStar_Syntax_Syntax.Tm_type (uu____9831), uu____9832) -> begin
((k1'), ((sub_prob)::[]))
end
| (uu____9836, FStar_Syntax_Syntax.Tm_type (uu____9837)) -> begin
((k2'), ((sub_prob)::[]))
end
| uu____9841 -> begin
(

let uu____9844 = (FStar_Syntax_Util.type_u ())
in (match (uu____9844) with
| (t, uu____9853) -> begin
(

let uu____9854 = (new_uvar r zs t)
in (match (uu____9854) with
| (k_zs, uu____9863) -> begin
(

let kprob = (

let uu____9865 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k_zs None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_58 -> FStar_TypeChecker_Common.TProb (_0_58)) uu____9865))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end)))))
end))
end))
in (match (uu____9749) with
| (k_u', sub_probs) -> begin
(

let uu____9879 = (

let uu____9887 = (

let uu____9888 = (new_uvar r zs k_u')
in (FStar_All.pipe_left Prims.fst uu____9888))
in (

let uu____9893 = (

let uu____9896 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs1 uu____9896))
in (

let uu____9899 = (

let uu____9902 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys1 uu____9902))
in ((uu____9887), (uu____9893), (uu____9899)))))
in (match (uu____9879) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs1 u_zs)
in (

let uu____9921 = (occurs_check env wl1 ((u1), (k1)) sub1)
in (match (uu____9921) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occcurs check")
end
| uu____9933 -> begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in (

let uu____9945 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____9945) with
| true -> begin
(

let wl2 = (solve_prob orig None ((sol1)::[]) wl1)
in (solve env wl2))
end
| uu____9950 -> begin
(

let sub2 = (u_abs knew2 ys1 u_zs)
in (

let uu____9952 = (occurs_check env wl1 ((u2), (k2)) sub2)
in (match (uu____9952) with
| (occurs_ok1, msg1) -> begin
(match ((not (occurs_ok1))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occurs check")
end
| uu____9964 -> begin
(

let sol2 = TERM (((((u2), (k2))), (sub2)))
in (

let wl2 = (solve_prob orig None ((sol1)::(sol2)::[]) wl1)
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

let solve_one_pat = (fun uu____10004 uu____10005 -> (match (((uu____10004), (uu____10005))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
((

let uu____10109 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10109) with
| true -> begin
(

let uu____10110 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10111 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" uu____10110 uu____10111)))
end
| uu____10112 -> begin
()
end));
(

let uu____10113 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____10113) with
| true -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____10123 uu____10124 -> (match (((uu____10123), (uu____10124))) with
| ((a, uu____10134), (t21, uu____10136)) -> begin
(

let uu____10141 = (

let uu____10144 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig uu____10144 FStar_TypeChecker_Common.EQ t21 None "flex-flex index"))
in (FStar_All.pipe_right uu____10141 (fun _0_59 -> FStar_TypeChecker_Common.TProb (_0_59))))
end)) xs args2)
in (

let guard = (

let uu____10148 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____10148))
in (

let wl1 = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))))
end
| uu____10154 -> begin
(

let t21 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t21)
in (

let uu____10158 = (occurs_check env wl ((u1), (k1)) t21)
in (match (uu____10158) with
| (occurs_ok, uu____10167) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in (

let uu____10172 = (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars))
in (match (uu____10172) with
| true -> begin
(

let sol = (

let uu____10174 = (

let uu____10179 = (u_abs k1 xs t21)
in ((((u1), (k1))), (uu____10179)))
in TERM (uu____10174))
in (

let wl1 = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl1)))
end
| uu____10191 -> begin
(

let uu____10192 = (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok))
in (match (uu____10192) with
| true -> begin
(

let uu____10193 = (force_quasi_pattern (Some (xs)) ((t21), (u2), (k2), (args2)))
in (match (uu____10193) with
| (sol, (uu____10207, u21, k21, ys)) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____10217 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____10217) with
| true -> begin
(

let uu____10218 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" uu____10218))
end
| uu____10219 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____10223 -> begin
(giveup env "impossible" orig)
end);
))
end))
end
| uu____10224 -> begin
(giveup_or_defer1 orig "flex-flex constraint")
end))
end)))
end))))
end));
)
end))
in (

let uu____10225 = lhs
in (match (uu____10225) with
| (t1, u1, k1, args1) -> begin
(

let uu____10230 = rhs
in (match (uu____10230) with
| (t2, u2, k2, args2) -> begin
(

let maybe_pat_vars1 = (pat_vars env [] args1)
in (

let maybe_pat_vars2 = (pat_vars env [] args2)
in (

let r = t2.FStar_Syntax_Syntax.pos
in (match (((maybe_pat_vars1), (maybe_pat_vars2))) with
| (Some (xs), Some (ys)) -> begin
(solve_both_pats wl ((u1), (k1), (xs), (args1)) ((u2), (k2), (ys), (args2)) t2.FStar_Syntax_Syntax.pos)
end
| (Some (xs), None) -> begin
(solve_one_pat ((t1), (u1), (k1), (xs)) rhs)
end
| (None, Some (ys)) -> begin
(solve_one_pat ((t2), (u2), (k2), (ys)) lhs)
end
| uu____10256 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: neither side is a pattern")
end
| uu____10261 -> begin
(

let uu____10262 = (force_quasi_pattern None ((t1), (u1), (k1), (args1)))
in (match (uu____10262) with
| (sol, uu____10269) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____10272 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____10272) with
| true -> begin
(

let uu____10273 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" uu____10273))
end
| uu____10274 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____10278 -> begin
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

let uu____10280 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____10280) with
| true -> begin
(

let uu____10281 = (solve_prob orig None [] wl)
in (solve env uu____10281))
end
| uu____10282 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in (

let uu____10285 = (FStar_Util.physical_equality t1 t2)
in (match (uu____10285) with
| true -> begin
(

let uu____10286 = (solve_prob orig None [] wl)
in (solve env uu____10286))
end
| uu____10287 -> begin
((

let uu____10289 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____10289) with
| true -> begin
(

let uu____10290 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" uu____10290))
end
| uu____10291 -> begin
()
end));
(

let r = (FStar_TypeChecker_Env.get_range env)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| ((FStar_Syntax_Syntax.Tm_bvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_bvar (_))) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (FStar_Syntax_Syntax.Tm_type (u1), FStar_Syntax_Syntax.Tm_type (u2)) -> begin
(solve_one_universe_eq env orig u1 u2 wl)
end
| (FStar_Syntax_Syntax.Tm_arrow (bs1, c1), FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) -> begin
(

let mk_c = (fun c uu___129_10336 -> (match (uu___129_10336) with
| [] -> begin
c
end
| bs -> begin
(

let uu____10350 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c))))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____10350))
end))
in (

let uu____10364 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____10364) with
| ((bs11, c11), (bs21, c21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let c12 = (FStar_Syntax_Subst.subst_comp subst1 c11)
in (

let c22 = (FStar_Syntax_Subst.subst_comp subst1 c21)
in (

let rel = (

let uu____10450 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____10450) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____10451 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (

let uu____10452 = (mk_problem scope orig c12 rel c22 None "function co-domain")
in (FStar_All.pipe_left (fun _0_60 -> FStar_TypeChecker_Common.CProb (_0_60)) uu____10452)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___130_10529 -> (match (uu___130_10529) with
| [] -> begin
t
end
| bs -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l))))) None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____10568 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____10568) with
| ((bs11, tbody11), (bs21, tbody21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let uu____10651 = (

let uu____10654 = (FStar_Syntax_Subst.subst subst1 tbody11)
in (

let uu____10655 = (FStar_Syntax_Subst.subst subst1 tbody21)
in (mk_problem scope orig uu____10654 problem.FStar_TypeChecker_Common.relation uu____10655 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _0_61 -> FStar_TypeChecker_Common.TProb (_0_61)) uu____10651))))
end)))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____10670) -> begin
true
end
| uu____10685 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____10704 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____10710 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let uu____10713 = (

let uu____10724 = (maybe_eta t1)
in (

let uu____10729 = (maybe_eta t2)
in ((uu____10724), (uu____10729))))
in (match (uu____10713) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___163_10760 = problem
in {FStar_TypeChecker_Common.pid = uu___163_10760.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___163_10760.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___163_10760.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___163_10760.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___163_10760.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___163_10760.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___163_10760.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___163_10760.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs))) | ((FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs))) -> begin
(

let uu____10793 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____10793) with
| true -> begin
(

let uu____10794 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____10794 t_abs wl))
end
| uu____10798 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| uu____10799 -> begin
(failwith "Impossible: at least one side is an abstraction")
end))))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____10810), FStar_Syntax_Syntax.Tm_refine (uu____10811)) -> begin
(

let uu____10820 = (as_refinement env wl t1)
in (match (uu____10820) with
| (x1, phi1) -> begin
(

let uu____10825 = (as_refinement env wl t2)
in (match (uu____10825) with
| (x2, phi2) -> begin
(

let base_prob = (

let uu____10831 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _0_62 -> FStar_TypeChecker_Common.TProb (_0_62)) uu____10831))
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

let uu____10864 = (imp phi12 phi22)
in (FStar_All.pipe_right uu____10864 (guard_on_element wl problem x11))))
in (

let fallback = (fun uu____10868 -> (

let impl = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp1 FStar_Syntax_Util.mk_iff phi11 phi21)
end
| uu____10870 -> begin
(mk_imp1 FStar_Syntax_Util.mk_imp phi11 phi21)
end)
in (

let guard = (

let uu____10874 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____10874 impl))
in (

let wl1 = (solve_prob orig (Some (guard)) [] wl)
in (solve env1 (attempt ((base_prob)::[]) wl1))))))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let ref_prob = (

let uu____10881 = (

let uu____10884 = (

let uu____10885 = (FStar_Syntax_Syntax.mk_binder x11)
in (uu____10885)::(p_scope orig))
in (mk_problem uu____10884 orig phi11 FStar_TypeChecker_Common.EQ phi21 None "refinement formula"))
in (FStar_All.pipe_left (fun _0_63 -> FStar_TypeChecker_Common.TProb (_0_63)) uu____10881))
in (

let uu____10888 = (solve env1 (

let uu___164_10889 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___164_10889.ctr; defer_ok = false; smt_ok = uu___164_10889.smt_ok; tcenv = uu___164_10889.tcenv}))
in (match (uu____10888) with
| Failed (uu____10893) -> begin
(fallback ())
end
| Success (uu____10896) -> begin
(

let guard = (

let uu____10900 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (

let uu____10903 = (

let uu____10904 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right uu____10904 (guard_on_element wl problem x11)))
in (FStar_Syntax_Util.mk_conj uu____10900 uu____10903)))
in (

let wl1 = (solve_prob orig (Some (guard)) [] wl)
in (

let wl2 = (

let uu___165_10911 = wl1
in {attempting = uu___165_10911.attempting; wl_deferred = uu___165_10911.wl_deferred; ctr = (wl1.ctr + (Prims.parse_int "1")); defer_ok = uu___165_10911.defer_ok; smt_ok = uu___165_10911.smt_ok; tcenv = uu___165_10911.tcenv})
in (solve env1 (attempt ((base_prob)::[]) wl2)))))
end)))
end
| uu____10912 -> begin
(fallback ())
end)))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(

let uu____10965 = (destruct_flex_t t1)
in (

let uu____10966 = (destruct_flex_t t2)
in (flex_flex1 orig uu____10965 uu____10966)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(

let uu____10982 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____10982 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_arrow (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
(solve_t' env (

let uu___166_11031 = problem
in {FStar_TypeChecker_Common.pid = uu___166_11031.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___166_11031.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___166_11031.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___166_11031.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_11031.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___166_11031.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___166_11031.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_11031.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_11031.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____11047 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____11049 = (

let uu____11050 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____11050))
in (match (uu____11049) with
| true -> begin
(

let uu____11051 = (FStar_All.pipe_left (fun _0_64 -> FStar_TypeChecker_Common.TProb (_0_64)) (

let uu___167_11054 = problem
in {FStar_TypeChecker_Common.pid = uu___167_11054.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___167_11054.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___167_11054.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___167_11054.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___167_11054.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___167_11054.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___167_11054.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___167_11054.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___167_11054.FStar_TypeChecker_Common.rank}))
in (

let uu____11055 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____11051 uu____11055 t2 wl)))
end
| uu____11059 -> begin
(

let uu____11060 = (base_and_refinement env wl t2)
in (match (uu____11060) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(

let uu____11090 = (FStar_All.pipe_left (fun _0_65 -> FStar_TypeChecker_Common.TProb (_0_65)) (

let uu___168_11093 = problem
in {FStar_TypeChecker_Common.pid = uu___168_11093.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___168_11093.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___168_11093.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___168_11093.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___168_11093.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___168_11093.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___168_11093.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___168_11093.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___168_11093.FStar_TypeChecker_Common.rank}))
in (

let uu____11094 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____11090 uu____11094 t_base wl)))
end
| Some (y, phi) -> begin
(

let y' = (

let uu___169_11109 = y
in {FStar_Syntax_Syntax.ppname = uu___169_11109.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___169_11109.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let base_prob = (

let uu____11112 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_66 -> FStar_TypeChecker_Common.TProb (_0_66)) uu____11112))
in (

let guard = (

let uu____11120 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____11120 impl))
in (

let wl1 = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl1)))))))
end)
end))
end)))
end)
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| uu____11141 -> begin
(

let uu____11142 = (base_and_refinement env wl t1)
in (match (uu____11142) with
| (t_base, uu____11153) -> begin
(solve_t env (

let uu___170_11168 = problem
in {FStar_TypeChecker_Common.pid = uu___170_11168.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___170_11168.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___170_11168.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___170_11168.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___170_11168.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___170_11168.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___170_11168.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___170_11168.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (FStar_Syntax_Syntax.Tm_refine (uu____11171), uu____11172) -> begin
(

let t21 = (

let uu____11180 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement uu____11180))
in (solve_t env (

let uu___171_11193 = problem
in {FStar_TypeChecker_Common.pid = uu___171_11193.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___171_11193.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___171_11193.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___171_11193.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___171_11193.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___171_11193.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___171_11193.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___171_11193.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___171_11193.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____11194, FStar_Syntax_Syntax.Tm_refine (uu____11195)) -> begin
(

let t11 = (

let uu____11203 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement uu____11203))
in (solve_t env (

let uu___172_11216 = problem
in {FStar_TypeChecker_Common.pid = uu___172_11216.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___172_11216.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___172_11216.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___172_11216.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___172_11216.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___172_11216.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___172_11216.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___172_11216.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___172_11216.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(

let head1 = (

let uu____11246 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____11246 Prims.fst))
in (

let head2 = (

let uu____11277 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____11277 Prims.fst))
in (

let uu____11305 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____11305) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____11314 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____11314) with
| true -> begin
(

let guard = (

let uu____11321 = (

let uu____11322 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____11322 = FStar_Syntax_Util.Equal))
in (match (uu____11321) with
| true -> begin
None
end
| uu____11324 -> begin
(

let uu____11325 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_67 -> Some (_0_67)) uu____11325))
end))
in (

let uu____11327 = (solve_prob orig guard [] wl)
in (solve env uu____11327)))
end
| uu____11328 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____11329 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t11, uu____11331, uu____11332), uu____11333) -> begin
(solve_t' env (

let uu___173_11362 = problem
in {FStar_TypeChecker_Common.pid = uu___173_11362.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___173_11362.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___173_11362.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___173_11362.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___173_11362.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___173_11362.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___173_11362.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___173_11362.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___173_11362.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____11365, FStar_Syntax_Syntax.Tm_ascribed (t21, uu____11367, uu____11368)) -> begin
(solve_t' env (

let uu___174_11397 = problem
in {FStar_TypeChecker_Common.pid = uu___174_11397.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___174_11397.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___174_11397.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___174_11397.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___174_11397.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___174_11397.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___174_11397.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___174_11397.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___174_11397.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(

let uu____11410 = (

let uu____11411 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____11412 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____11411 uu____11412)))
in (failwith uu____11410))
end
| uu____11413 -> begin
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

let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (

let solve_eq = (fun c1_comp c2_comp -> ((

let uu____11445 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____11445) with
| true -> begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end
| uu____11446 -> begin
()
end));
(

let sub_probs = (FStar_List.map2 (fun uu____11453 uu____11454 -> (match (((uu____11453), (uu____11454))) with
| ((a1, uu____11464), (a2, uu____11466)) -> begin
(

let uu____11471 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _0_68 -> FStar_TypeChecker_Common.TProb (_0_68)) uu____11471))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (

let uu____11477 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____11477))
in (

let wl1 = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))));
))
in (

let solve_sub = (fun c11 edge c21 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let lift_c1 = (fun uu____11497 -> (

let wp = (match (c11.FStar_Syntax_Syntax.effect_args) with
| ((wp1, uu____11504))::[] -> begin
wp1
end
| uu____11517 -> begin
(

let uu____11523 = (

let uu____11524 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c11.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" uu____11524))
in (failwith uu____11523))
end)
in (

let uu____11527 = (

let uu____11533 = (

let uu____11534 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c11.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____11534))
in (uu____11533)::[])
in {FStar_Syntax_Syntax.comp_univs = c11.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c21.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c11.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____11527; FStar_Syntax_Syntax.flags = c11.FStar_Syntax_Syntax.flags})))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____11535 = (lift_c1 ())
in (solve_eq uu____11535 c21))
end
| uu____11536 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___131_11539 -> (match (uu___131_11539) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| uu____11540 -> begin
false
end))))
in (

let uu____11541 = (match (((c11.FStar_Syntax_Syntax.effect_args), (c21.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____11565))::uu____11566, ((wp2, uu____11568))::uu____11569) -> begin
((wp1), (wp2))
end
| uu____11610 -> begin
(

let uu____11623 = (

let uu____11624 = (

let uu____11627 = (

let uu____11628 = (FStar_Syntax_Print.lid_to_string c11.FStar_Syntax_Syntax.effect_name)
in (

let uu____11629 = (FStar_Syntax_Print.lid_to_string c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____11628 uu____11629)))
in ((uu____11627), (env.FStar_TypeChecker_Env.range)))
in FStar_Errors.Error (uu____11624))
in (Prims.raise uu____11623))
end)
in (match (uu____11541) with
| (wpc1, wpc2) -> begin
(

let uu____11646 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____11646) with
| true -> begin
(

let uu____11649 = (problem_using_guard orig c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env uu____11649 wl))
end
| uu____11652 -> begin
(

let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c21.FStar_Syntax_Syntax.effect_name)
in (

let uu____11654 = (FStar_All.pipe_right c2_decl.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____11654) with
| true -> begin
(

let c1_repr = (

let uu____11657 = (

let uu____11658 = (

let uu____11659 = (lift_c1 ())
in (FStar_Syntax_Syntax.mk_Comp uu____11659))
in (

let uu____11660 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____11658 uu____11660)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____11657))
in (

let c2_repr = (

let uu____11662 = (

let uu____11663 = (FStar_Syntax_Syntax.mk_Comp c21)
in (

let uu____11664 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____11663 uu____11664)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____11662))
in (

let prob = (

let uu____11666 = (

let uu____11669 = (

let uu____11670 = (FStar_Syntax_Print.term_to_string c1_repr)
in (

let uu____11671 = (FStar_Syntax_Print.term_to_string c2_repr)
in (FStar_Util.format2 "sub effect repr: %s <: %s" uu____11670 uu____11671)))
in (sub_prob c1_repr problem.FStar_TypeChecker_Common.relation c2_repr uu____11669))
in FStar_TypeChecker_Common.TProb (uu____11666))
in (

let wl1 = (

let uu____11673 = (

let uu____11675 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in Some (uu____11675))
in (solve_prob orig uu____11673 [] wl))
in (solve env (attempt ((prob)::[]) wl1))))))
end
| uu____11678 -> begin
(

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____11680 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____11682 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11682) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____11683 -> begin
()
end));
(

let uu____11684 = (

let uu____11687 = (

let uu____11688 = (

let uu____11698 = (

let uu____11699 = (

let uu____11700 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (uu____11700)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____11699 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (

let uu____11701 = (

let uu____11703 = (FStar_Syntax_Syntax.as_arg c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____11704 = (

let uu____11706 = (

let uu____11707 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11707))
in (uu____11706)::[])
in (uu____11703)::uu____11704))
in ((uu____11698), (uu____11701))))
in FStar_Syntax_Syntax.Tm_app (uu____11688))
in (FStar_Syntax_Syntax.mk uu____11687))
in (uu____11684 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r));
)
end
| uu____11717 -> begin
(

let uu____11718 = (

let uu____11721 = (

let uu____11722 = (

let uu____11732 = (

let uu____11733 = (

let uu____11734 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (uu____11734)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____11733 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (

let uu____11735 = (

let uu____11737 = (FStar_Syntax_Syntax.as_arg c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____11738 = (

let uu____11740 = (FStar_Syntax_Syntax.as_arg wpc2)
in (

let uu____11741 = (

let uu____11743 = (

let uu____11744 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11744))
in (uu____11743)::[])
in (uu____11740)::uu____11741))
in (uu____11737)::uu____11738))
in ((uu____11732), (uu____11735))))
in FStar_Syntax_Syntax.Tm_app (uu____11722))
in (FStar_Syntax_Syntax.mk uu____11721))
in (uu____11718 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r))
end)
end)
in (

let base_prob = (

let uu____11755 = (sub_prob c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _0_69 -> FStar_TypeChecker_Common.TProb (_0_69)) uu____11755))
in (

let wl1 = (

let uu____11761 = (

let uu____11763 = (

let uu____11766 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____11766 g))
in (FStar_All.pipe_left (fun _0_70 -> Some (_0_70)) uu____11763))
in (solve_prob orig uu____11761 [] wl))
in (solve env (attempt ((base_prob)::[]) wl1)))))
end)))
end))
end)))
end))))
in (

let uu____11776 = (FStar_Util.physical_equality c1 c2)
in (match (uu____11776) with
| true -> begin
(

let uu____11777 = (solve_prob orig None [] wl)
in (solve env uu____11777))
end
| uu____11778 -> begin
((

let uu____11780 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11780) with
| true -> begin
(

let uu____11781 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____11782 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____11781 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____11782)))
end
| uu____11783 -> begin
()
end));
(

let uu____11784 = (

let uu____11787 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____11788 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____11787), (uu____11788))))
in (match (uu____11784) with
| (c11, c21) -> begin
(match (((c11.FStar_Syntax_Syntax.n), (c21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____11792), FStar_Syntax_Syntax.Total (t2, uu____11794)) when (FStar_Syntax_Util.non_informative t2) -> begin
(

let uu____11807 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env uu____11807 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____11810), FStar_Syntax_Syntax.Total (uu____11811)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.Total (t2, _))) | ((FStar_Syntax_Syntax.GTotal (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) | ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) -> begin
(

let uu____11860 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env uu____11860 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(

let uu____11867 = (

let uu___175_11870 = problem
in (

let uu____11873 = (

let uu____11874 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____11874))
in {FStar_TypeChecker_Common.pid = uu___175_11870.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____11873; FStar_TypeChecker_Common.relation = uu___175_11870.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___175_11870.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___175_11870.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___175_11870.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___175_11870.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___175_11870.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___175_11870.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___175_11870.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____11867 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(

let uu____11879 = (

let uu___176_11882 = problem
in (

let uu____11885 = (

let uu____11886 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____11886))
in {FStar_TypeChecker_Common.pid = uu___176_11882.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___176_11882.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___176_11882.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____11885; FStar_TypeChecker_Common.element = uu___176_11882.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___176_11882.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___176_11882.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___176_11882.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___176_11882.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___176_11882.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____11879 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____11887), FStar_Syntax_Syntax.Comp (uu____11888)) -> begin
(

let uu____11889 = (((FStar_Syntax_Util.is_ml_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) || ((FStar_Syntax_Util.is_total_comp c11) && ((FStar_Syntax_Util.is_total_comp c21) || (FStar_Syntax_Util.is_ml_comp c21))))
in (match (uu____11889) with
| true -> begin
(

let uu____11890 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c11) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c21) None "result type")
in (solve_t env uu____11890 wl))
end
| uu____11893 -> begin
(

let c1_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (

let c2_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (match (((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name))) with
| true -> begin
(solve_eq c1_comp c2_comp)
end
| uu____11896 -> begin
(

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((

let uu____11900 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11900) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c12.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c22.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____11901 -> begin
()
end));
(

let uu____11902 = (FStar_TypeChecker_Env.monad_leq env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____11902) with
| None -> begin
(

let uu____11904 = (((FStar_Syntax_Util.is_ghost_effect c12.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c22.FStar_Syntax_Syntax.effect_name)) && (

let uu____11905 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c22.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative uu____11905)))
in (match (uu____11904) with
| true -> begin
(

let edge = {FStar_TypeChecker_Env.msource = c12.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c22.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = FStar_TypeChecker_Env.identity_mlift}
in (solve_sub c12 edge c22))
end
| uu____11907 -> begin
(

let uu____11908 = (

let uu____11909 = (FStar_Syntax_Print.lid_to_string c12.FStar_Syntax_Syntax.effect_name)
in (

let uu____11910 = (FStar_Syntax_Print.lid_to_string c22.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____11909 uu____11910)))
in (giveup env uu____11908 orig))
end))
end
| Some (edge) -> begin
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

let uu____11915 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____11935 -> (match (uu____11935) with
| (uu____11946, uu____11947, u, uu____11949, uu____11950, uu____11951) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____11915 (FStar_String.concat ", "))))


let ineqs_to_string : (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.string = (fun ineqs -> (

let vars = (

let uu____11980 = (FStar_All.pipe_right (Prims.fst ineqs) (FStar_List.map FStar_Syntax_Print.univ_to_string))
in (FStar_All.pipe_right uu____11980 (FStar_String.concat ", ")))
in (

let ineqs1 = (

let uu____11990 = (FStar_All.pipe_right (Prims.snd ineqs) (FStar_List.map (fun uu____12002 -> (match (uu____12002) with
| (u1, u2) -> begin
(

let uu____12007 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____12008 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "%s < %s" uu____12007 uu____12008)))
end))))
in (FStar_All.pipe_right uu____11990 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred), (g.FStar_TypeChecker_Env.univ_ineqs))) with
| (FStar_TypeChecker_Common.Trivial, [], (uu____12020, [])) -> begin
"{}"
end
| uu____12033 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____12043 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____12043) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____12044 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____12046 = (FStar_List.map (fun uu____12050 -> (match (uu____12050) with
| (uu____12053, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right uu____12046 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (

let uu____12057 = (ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs)
in (FStar_Util.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n" form carry uu____12057 imps)))))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = (

let uu____12095 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____12095) with
| true -> begin
(

let uu____12096 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____12097 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____12096 (rel_to_string rel) uu____12097)))
end
| uu____12098 -> begin
"TOP"
end))
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (

let uu____12117 = (

let uu____12119 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_71 -> Some (_0_71)) uu____12119))
in (FStar_Syntax_Syntax.new_bv uu____12117 t1))
in (

let env1 = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (

let uu____12125 = (

let uu____12127 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _0_72 -> Some (_0_72)) uu____12127))
in (

let uu____12129 = (FStar_TypeChecker_Env.get_range env1)
in (new_t_problem env1 t1 rel t2 uu____12125 uu____12129)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err1 -> (

let probs1 = (

let uu____12152 = (FStar_Options.eager_inference ())
in (match (uu____12152) with
| true -> begin
(

let uu___177_12153 = probs
in {attempting = uu___177_12153.attempting; wl_deferred = uu___177_12153.wl_deferred; ctr = uu___177_12153.ctr; defer_ok = false; smt_ok = uu___177_12153.smt_ok; tcenv = uu___177_12153.tcenv})
end
| uu____12154 -> begin
probs
end))
in (

let tx = (FStar_Unionfind.new_transaction ())
in (

let sol = (solve env probs1)
in (match (sol) with
| Success (deferred) -> begin
((FStar_Unionfind.commit tx);
Some (deferred);
)
end
| Failed (d, s) -> begin
((FStar_Unionfind.rollback tx);
(

let uu____12164 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____12164) with
| true -> begin
(

let uu____12165 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____12165))
end
| uu____12166 -> begin
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

let uu____12175 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____12175) with
| true -> begin
(

let uu____12176 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____12176))
end
| uu____12177 -> begin
()
end));
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in ((

let uu____12180 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____12180) with
| true -> begin
(

let uu____12181 = (FStar_Syntax_Print.term_to_string f1)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____12181))
end
| uu____12182 -> begin
()
end));
(

let f2 = (

let uu____12184 = (

let uu____12185 = (FStar_Syntax_Util.unmeta f1)
in uu____12185.FStar_Syntax_Syntax.n)
in (match (uu____12184) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____12189 -> begin
FStar_TypeChecker_Common.NonTrivial (f1)
end))
in (

let uu___178_12190 = g
in {FStar_TypeChecker_Env.guard_f = f2; FStar_TypeChecker_Env.deferred = uu___178_12190.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___178_12190.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___178_12190.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(

let uu____12205 = (

let uu____12206 = (

let uu____12207 = (

let uu____12208 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right uu____12208 (fun _0_73 -> FStar_TypeChecker_Common.NonTrivial (_0_73))))
in {FStar_TypeChecker_Env.guard_f = uu____12207; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env uu____12206))
in (FStar_All.pipe_left (fun _0_74 -> Some (_0_74)) uu____12205))
end))


let try_teq : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun smt_ok env t1 t2 -> ((

let uu____12235 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12235) with
| true -> begin
(

let uu____12236 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12237 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" uu____12236 uu____12237)))
end
| uu____12238 -> begin
()
end));
(

let prob = (

let uu____12240 = (

let uu____12243 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None uu____12243))
in (FStar_All.pipe_left (fun _0_75 -> FStar_TypeChecker_Common.TProb (_0_75)) uu____12240))
in (

let g = (

let uu____12248 = (

let uu____12250 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____12250 (fun uu____12251 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12248))
in g));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____12265 = (try_teq true env t1 t2)
in (match (uu____12265) with
| None -> begin
(

let uu____12267 = (

let uu____12268 = (

let uu____12271 = (FStar_TypeChecker_Err.basic_type_error env None t2 t1)
in (

let uu____12272 = (FStar_TypeChecker_Env.get_range env)
in ((uu____12271), (uu____12272))))
in FStar_Errors.Error (uu____12268))
in (Prims.raise uu____12267))
end
| Some (g) -> begin
((

let uu____12275 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12275) with
| true -> begin
(

let uu____12276 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12277 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____12278 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____12276 uu____12277 uu____12278))))
end
| uu____12279 -> begin
()
end));
g;
)
end)))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 smt_ok -> ((

let uu____12294 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12294) with
| true -> begin
(

let uu____12295 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____12296 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" uu____12295 uu____12296)))
end
| uu____12297 -> begin
()
end));
(

let uu____12298 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____12298) with
| (prob, x) -> begin
(

let g = (

let uu____12306 = (

let uu____12308 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____12308 (fun uu____12309 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12306))
in ((

let uu____12315 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____12315) with
| true -> begin
(

let uu____12316 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____12317 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____12318 = (

let uu____12319 = (FStar_Util.must g)
in (guard_to_string env uu____12319))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" uu____12316 uu____12317 uu____12318))))
end
| uu____12320 -> begin
()
end));
(abstract_guard x g);
))
end));
))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env e t1 t2 -> (

let uu____12343 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12344 = (FStar_TypeChecker_Err.basic_type_error env (Some (e)) t2 t1)
in (FStar_Errors.err uu____12343 uu____12344))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> ((

let uu____12356 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12356) with
| true -> begin
(

let uu____12357 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____12358 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" uu____12357 uu____12358)))
end
| uu____12359 -> begin
()
end));
(

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____12361 -> begin
FStar_TypeChecker_Common.SUB
end)
in (

let prob = (

let uu____12363 = (

let uu____12366 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None uu____12366 "sub_comp"))
in (FStar_All.pipe_left (fun _0_76 -> FStar_TypeChecker_Common.CProb (_0_76)) uu____12363))
in (

let uu____12369 = (

let uu____12371 = (singleton env prob)
in (solve_and_commit env uu____12371 (fun uu____12372 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12369))));
))


let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun tx env uu____12391 -> (match (uu____12391) with
| (variables, ineqs) -> begin
(

let fail = (fun u1 u2 -> ((FStar_Unionfind.rollback tx);
(

let uu____12416 = (

let uu____12417 = (

let uu____12420 = (

let uu____12421 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____12422 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Universe %s and %s are incompatible" uu____12421 uu____12422)))
in (

let uu____12423 = (FStar_TypeChecker_Env.get_range env)
in ((uu____12420), (uu____12423))))
in FStar_Errors.Error (uu____12417))
in (Prims.raise uu____12416));
))
in (

let equiv = (fun v1 v' -> (

let uu____12431 = (

let uu____12434 = (FStar_Syntax_Subst.compress_univ v1)
in (

let uu____12435 = (FStar_Syntax_Subst.compress_univ v')
in ((uu____12434), (uu____12435))))
in (match (uu____12431) with
| (FStar_Syntax_Syntax.U_unif (v0), FStar_Syntax_Syntax.U_unif (v0')) -> begin
(FStar_Unionfind.equivalent v0 v0')
end
| uu____12443 -> begin
false
end)))
in (

let sols = (FStar_All.pipe_right variables (FStar_List.collect (fun v1 -> (

let uu____12457 = (FStar_Syntax_Subst.compress_univ v1)
in (match (uu____12457) with
| FStar_Syntax_Syntax.U_unif (uu____12461) -> begin
(

let lower_bounds_of_v = (FStar_All.pipe_right ineqs (FStar_List.collect (fun uu____12472 -> (match (uu____12472) with
| (u, v') -> begin
(

let uu____12478 = (equiv v1 v')
in (match (uu____12478) with
| true -> begin
(

let uu____12480 = (FStar_All.pipe_right variables (FStar_Util.for_some (equiv u)))
in (match (uu____12480) with
| true -> begin
[]
end
| uu____12483 -> begin
(u)::[]
end))
end
| uu____12484 -> begin
[]
end))
end))))
in (

let lb = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max (lower_bounds_of_v)))
in (((lb), (v1)))::[]))
end
| uu____12490 -> begin
[]
end)))))
in (

let uu____12493 = (

let wl = (

let uu___179_12496 = (empty_worklist env)
in {attempting = uu___179_12496.attempting; wl_deferred = uu___179_12496.wl_deferred; ctr = uu___179_12496.ctr; defer_ok = false; smt_ok = uu___179_12496.smt_ok; tcenv = uu___179_12496.tcenv})
in (FStar_All.pipe_right sols (FStar_List.map (fun uu____12503 -> (match (uu____12503) with
| (lb, v1) -> begin
(

let uu____12508 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl lb v1)
in (match (uu____12508) with
| USolved (wl1) -> begin
()
end
| uu____12510 -> begin
(fail lb v1)
end))
end)))))
in (

let rec check_ineq = (fun uu____12516 -> (match (uu____12516) with
| (u, v1) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u)
in (

let v2 = (FStar_TypeChecker_Normalize.normalize_universe env v1)
in (match (((u1), (v2))) with
| (FStar_Syntax_Syntax.U_zero, uu____12523) -> begin
true
end
| (FStar_Syntax_Syntax.U_succ (u0), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u0), (v0)))
end
| (FStar_Syntax_Syntax.U_name (u0), FStar_Syntax_Syntax.U_name (v0)) -> begin
(FStar_Ident.ident_equals u0 v0)
end
| (FStar_Syntax_Syntax.U_unif (u0), FStar_Syntax_Syntax.U_unif (v0)) -> begin
(FStar_Unionfind.equivalent u0 v0)
end
| ((FStar_Syntax_Syntax.U_name (_), FStar_Syntax_Syntax.U_succ (v0))) | ((FStar_Syntax_Syntax.U_unif (_), FStar_Syntax_Syntax.U_succ (v0))) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_max (us), uu____12539) -> begin
(FStar_All.pipe_right us (FStar_Util.for_all (fun u2 -> (check_ineq ((u2), (v2))))))
end
| (uu____12543, FStar_Syntax_Syntax.U_max (vs)) -> begin
(FStar_All.pipe_right vs (FStar_Util.for_some (fun v3 -> (check_ineq ((u1), (v3))))))
end
| uu____12548 -> begin
false
end)))
end))
in (

let uu____12551 = (FStar_All.pipe_right ineqs (FStar_Util.for_all (fun uu____12557 -> (match (uu____12557) with
| (u, v1) -> begin
(

let uu____12562 = (check_ineq ((u), (v1)))
in (match (uu____12562) with
| true -> begin
true
end
| uu____12563 -> begin
((

let uu____12565 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____12565) with
| true -> begin
(

let uu____12566 = (FStar_Syntax_Print.univ_to_string u)
in (

let uu____12567 = (FStar_Syntax_Print.univ_to_string v1)
in (FStar_Util.print2 "%s </= %s" uu____12566 uu____12567)))
end
| uu____12568 -> begin
()
end));
false;
)
end))
end))))
in (match (uu____12551) with
| true -> begin
()
end
| uu____12569 -> begin
((

let uu____12571 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____12571) with
| true -> begin
((

let uu____12573 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Partially solved inequality constraints are: %s\n" uu____12573));
(FStar_Unionfind.rollback tx);
(

let uu____12579 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Original solved inequality constraints are: %s\n" uu____12579));
)
end
| uu____12584 -> begin
()
end));
(

let uu____12585 = (

let uu____12586 = (

let uu____12589 = (FStar_TypeChecker_Env.get_range env)
in (("Failed to solve universe inequalities for inductives"), (uu____12589)))
in FStar_Errors.Error (uu____12586))
in (Prims.raise uu____12585));
)
end)))))))
end))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun env ineqs -> (

let tx = (FStar_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Unionfind.commit tx);
)))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail = (fun uu____12622 -> (match (uu____12622) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Errors.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in ((

let uu____12632 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____12632) with
| true -> begin
(

let uu____12633 = (wl_to_string wl)
in (

let uu____12634 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" uu____12633 uu____12634)))
end
| uu____12644 -> begin
()
end));
(

let g1 = (

let uu____12646 = (solve_and_commit env wl fail)
in (match (uu____12646) with
| Some ([]) -> begin
(

let uu___180_12653 = g
in {FStar_TypeChecker_Env.guard_f = uu___180_12653.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu___180_12653.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___180_12653.FStar_TypeChecker_Env.implicits})
end
| uu____12656 -> begin
(failwith "impossible: Unexpected deferred constraints remain")
end))
in ((solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___181_12659 = g1
in {FStar_TypeChecker_Env.guard_f = uu___181_12659.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___181_12659.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = uu___181_12659.FStar_TypeChecker_Env.implicits});
));
))))


let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun use_env_range_msg env g use_smt -> (

let g1 = (solve_deferred_constraints env g)
in (

let ret_g = (

let uu___182_12685 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___182_12685.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___182_12685.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___182_12685.FStar_TypeChecker_Env.implicits})
in (

let uu____12686 = (

let uu____12687 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12687)))
in (match (uu____12686) with
| true -> begin
Some (ret_g)
end
| uu____12689 -> begin
(match (g1.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((

let uu____12693 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Norm")))
in (match (uu____12693) with
| true -> begin
(

let uu____12694 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12695 = (

let uu____12696 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____12696))
in (FStar_Errors.diag uu____12694 uu____12695)))
end
| uu____12697 -> begin
()
end));
(

let vc1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc1)) with
| FStar_TypeChecker_Common.Trivial -> begin
Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc2) -> begin
(match ((not (use_smt))) with
| true -> begin
None
end
| uu____12702 -> begin
((

let uu____12705 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12705) with
| true -> begin
(

let uu____12706 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12707 = (

let uu____12708 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____12708))
in (FStar_Errors.diag uu____12706 uu____12707)))
end
| uu____12709 -> begin
()
end));
(

let vcs = (

let uu____12714 = (FStar_Options.use_tactics ())
in (match (uu____12714) with
| true -> begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.preprocess env vc2)
end
| uu____12718 -> begin
(((env), (vc2)))::[]
end))
in (FStar_All.pipe_right vcs (FStar_List.iter (fun uu____12728 -> (match (uu____12728) with
| (env1, goal) -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env1 goal)
end)))));
Some (ret_g);
)
end)
end));
)
end)
end)))))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let uu____12739 = (discharge_guard' None env g true)
in (match (uu____12739) with
| Some (g1) -> begin
g1
end
| None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end)))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (

let uu____12759 = (FStar_Unionfind.find u)
in (match (uu____12759) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| uu____12768 -> begin
false
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____12783 = acc
in (match (uu____12783) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____12794 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd1)::tl1 -> begin
(

let uu____12829 = hd1
in (match (uu____12829) with
| (uu____12836, env, u, tm, k, r) -> begin
(

let uu____12842 = (unresolved u)
in (match (uu____12842) with
| true -> begin
(until_fixpoint (((hd1)::out), (changed)) tl1)
end
| uu____12856 -> begin
(

let env1 = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 tm)
in ((

let uu____12860 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("RelCheck")))
in (match (uu____12860) with
| true -> begin
(

let uu____12861 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____12865 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____12866 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" uu____12861 uu____12865 uu____12866))))
end
| uu____12867 -> begin
()
end));
(

let uu____12868 = (env1.FStar_TypeChecker_Env.type_of (

let uu___183_12872 = env1
in {FStar_TypeChecker_Env.solver = uu___183_12872.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___183_12872.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___183_12872.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___183_12872.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___183_12872.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___183_12872.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___183_12872.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___183_12872.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___183_12872.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___183_12872.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___183_12872.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___183_12872.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___183_12872.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___183_12872.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___183_12872.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___183_12872.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___183_12872.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___183_12872.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___183_12872.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___183_12872.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___183_12872.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___183_12872.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___183_12872.FStar_TypeChecker_Env.qname_and_index}) tm1)
in (match (uu____12868) with
| (uu____12873, uu____12874, g1) -> begin
(

let g2 = (match (env1.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___184_12877 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___184_12877.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___184_12877.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___184_12877.FStar_TypeChecker_Env.implicits})
end
| uu____12878 -> begin
g1
end)
in (

let g' = (

let uu____12880 = (discharge_guard' (Some ((fun uu____12884 -> (FStar_Syntax_Print.term_to_string tm1)))) env1 g2 true)
in (match (uu____12880) with
| Some (g3) -> begin
g3
end
| None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end))
in (until_fixpoint (((FStar_List.append g'.FStar_TypeChecker_Env.implicits out)), (true)) tl1)))
end));
)))
end))
end))
end)
end)))
in (

let uu___185_12899 = g
in (

let uu____12900 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___185_12899.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___185_12899.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___185_12899.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____12900})))))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g1 = (

let uu____12928 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____12928 resolve_implicits))
in (match (g1.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(

let uu____12935 = (discharge_guard env g1)
in (FStar_All.pipe_left Prims.ignore uu____12935))
end
| ((reason, uu____12937, uu____12938, e, t, r))::uu____12942 -> begin
(

let uu____12956 = (

let uu____12957 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____12958 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" uu____12957 uu____12958 reason)))
in (FStar_Errors.err r uu____12956))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___186_12965 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___186_12965.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___186_12965.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ((((u1), (u2)))::[])); FStar_TypeChecker_Env.implicits = uu___186_12965.FStar_TypeChecker_Env.implicits}))


let teq_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____12983 = (try_teq false env t1 t2)
in (match (uu____12983) with
| None -> begin
false
end
| Some (g) -> begin
(

let uu____12986 = (discharge_guard' None env g false)
in (match (uu____12986) with
| Some (uu____12990) -> begin
true
end
| None -> begin
false
end))
end)))





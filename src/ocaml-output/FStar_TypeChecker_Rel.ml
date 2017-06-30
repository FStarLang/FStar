
open Prims
open FStar_Pervasives

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


let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun x g -> (match (g) with
| FStar_Pervasives_Native.None -> begin
g
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu____56; FStar_TypeChecker_Env.univ_ineqs = uu____57; FStar_TypeChecker_Env.implicits = uu____58}) -> begin
g
end
| FStar_Pervasives_Native.Some (g1) -> begin
(

let f = (match (g1.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| uu____73 -> begin
(failwith "impossible")
end)
in (

let uu____74 = (

let uu___133_75 = g1
in (

let uu____76 = (

let uu____77 = (

let uu____78 = (

let uu____79 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____79)::[])
in (

let uu____80 = (

let uu____87 = (

let uu____93 = (

let uu____94 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____94 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____93 (fun _0_29 -> FStar_Util.Inl (_0_29))))
in FStar_Pervasives_Native.Some (uu____87))
in (FStar_Syntax_Util.abs uu____78 f uu____80)))
in (FStar_All.pipe_left (fun _0_30 -> FStar_TypeChecker_Common.NonTrivial (_0_30)) uu____77))
in {FStar_TypeChecker_Env.guard_f = uu____76; FStar_TypeChecker_Env.deferred = uu___133_75.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___133_75.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___133_75.FStar_TypeChecker_Env.implicits}))
in FStar_Pervasives_Native.Some (uu____74)))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___134_115 = g
in (

let uu____116 = (

let uu____117 = (

let uu____118 = (

let uu____121 = (

let uu____122 = (

let uu____132 = (

let uu____134 = (FStar_Syntax_Syntax.as_arg e)
in (uu____134)::[])
in ((f), (uu____132)))
in FStar_Syntax_Syntax.Tm_app (uu____122))
in (FStar_Syntax_Syntax.mk uu____121))
in (uu____118 (FStar_Pervasives_Native.Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _0_31 -> FStar_TypeChecker_Common.NonTrivial (_0_31)) uu____117))
in {FStar_TypeChecker_Env.guard_f = uu____116; FStar_TypeChecker_Env.deferred = uu___134_115.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___134_115.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___134_115.FStar_TypeChecker_Env.implicits}))
end))


let map_guard : FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  FStar_TypeChecker_Env.guard_t = (fun g map1 -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___135_156 = g
in (

let uu____157 = (

let uu____158 = (map1 f)
in FStar_TypeChecker_Common.NonTrivial (uu____158))
in {FStar_TypeChecker_Env.guard_f = uu____157; FStar_TypeChecker_Env.deferred = uu___135_156.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___135_156.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___135_156.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____162) -> begin
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

let uu____173 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (uu____173))
end))


let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____182 -> begin
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

let uu____213 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = uu____213; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (((FStar_List.append (FStar_Pervasives_Native.fst g1.FStar_TypeChecker_Env.univ_ineqs) (FStar_Pervasives_Native.fst g2.FStar_TypeChecker_Env.univ_ineqs))), ((FStar_List.append (FStar_Pervasives_Native.snd g1.FStar_TypeChecker_Env.univ_ineqs) (FStar_Pervasives_Native.snd g2.FStar_TypeChecker_Env.univ_ineqs)))); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard_univs : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun us bs g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let f1 = (FStar_List.fold_right2 (fun u b f1 -> (

let uu____258 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____258) with
| true -> begin
f1
end
| uu____259 -> begin
(FStar_Syntax_Util.mk_forall u (FStar_Pervasives_Native.fst b) f1)
end))) us bs f)
in (

let uu___136_260 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.NonTrivial (f1); FStar_TypeChecker_Env.deferred = uu___136_260.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___136_260.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___136_260.FStar_TypeChecker_Env.implicits}))
end))


let close_forall : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____274 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____274) with
| true -> begin
f1
end
| uu____275 -> begin
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

let uu___137_287 = g
in (

let uu____288 = (

let uu____289 = (close_forall env binders f)
in FStar_TypeChecker_Common.NonTrivial (uu____289))
in {FStar_TypeChecker_Env.guard_f = uu____288; FStar_TypeChecker_Env.deferred = uu___137_287.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___137_287.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___137_287.FStar_TypeChecker_Env.implicits}))
end))


let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (

let uv = (FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar)
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

let uu____361 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((uv1), (args)))) (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) r)
in ((uu____361), (uv1))))))
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
| uu____449 -> begin
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
| uu____537 -> begin
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
| uu____551 -> begin
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
| uu____568 -> begin
false
end))


let uu___is_CONTRAVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CONTRAVARIANT -> begin
true
end
| uu____572 -> begin
false
end))


let uu___is_INVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| INVARIANT -> begin
true
end
| uu____576 -> begin
false
end))


type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem


type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem


type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun uu___105_591 -> (match (uu___105_591) with
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

let uu____604 = (

let uu____605 = (FStar_Syntax_Subst.compress t)
in uu____605.FStar_Syntax_Syntax.n)
in (match (uu____604) with
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let uu____622 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____626 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s:%s)" uu____622 uu____626)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty); FStar_Syntax_Syntax.tk = uu____629; FStar_Syntax_Syntax.pos = uu____630; FStar_Syntax_Syntax.vars = uu____631}, args) -> begin
(

let uu____659 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____663 = (FStar_Syntax_Print.term_to_string ty)
in (

let uu____664 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "(%s:%s) %s" uu____659 uu____663 uu____664))))
end
| uu____665 -> begin
(FStar_Syntax_Print.term_to_string t)
end)))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env uu___106_671 -> (match (uu___106_671) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____675 = (

let uu____677 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____678 = (

let uu____680 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____681 = (

let uu____683 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (

let uu____684 = (

let uu____686 = (

let uu____688 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (

let uu____689 = (

let uu____691 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (

let uu____692 = (

let uu____694 = (FStar_TypeChecker_Normalize.term_to_string env (FStar_Pervasives_Native.fst p.FStar_TypeChecker_Common.logical_guard))
in (

let uu____695 = (

let uu____697 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (uu____697)::[])
in (uu____694)::uu____695))
in (uu____691)::uu____692))
in (uu____688)::uu____689))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::uu____686)
in (uu____683)::uu____684))
in (uu____680)::uu____681))
in (uu____677)::uu____678))
in (FStar_Util.format "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" uu____675))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____702 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____703 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____702 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____703)))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env uu___107_709 -> (match (uu___107_709) with
| UNIV (u, t) -> begin
(

let x = (

let uu____713 = (FStar_Options.hide_uvar_nums ())
in (match (uu____713) with
| true -> begin
"?"
end
| uu____714 -> begin
(

let uu____715 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____715 FStar_Util.string_of_int))
end))
in (

let uu____717 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x uu____717)))
end
| TERM ((u, uu____719), t) -> begin
(

let x = (

let uu____724 = (FStar_Options.hide_uvar_nums ())
in (match (uu____724) with
| true -> begin
"?"
end
| uu____725 -> begin
(

let uu____726 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____726 FStar_Util.string_of_int))
end))
in (

let uu____730 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x uu____730)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (

let uu____739 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right uu____739 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (

let uu____747 = (

let uu____749 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right uu____749 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right uu____747 (FStar_String.concat ", "))))


let args_to_string = (fun args -> (

let uu____767 = (FStar_All.pipe_right args (FStar_List.map (fun uu____775 -> (match (uu____775) with
| (x, uu____779) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____767 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> (

let uu____784 = (

let uu____785 = (FStar_Options.eager_inference ())
in (not (uu____785)))
in {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = uu____784; smt_ok = true; tcenv = env}))


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let uu___138_798 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = uu___138_798.wl_deferred; ctr = uu___138_798.ctr; defer_ok = uu___138_798.defer_ok; smt_ok = smt_ok; tcenv = uu___138_798.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard = (fun env g -> (

let uu___139_823 = (empty_worklist env)
in (

let uu____824 = (FStar_List.map FStar_Pervasives_Native.snd g)
in {attempting = uu____824; wl_deferred = uu___139_823.wl_deferred; ctr = uu___139_823.ctr; defer_ok = false; smt_ok = uu___139_823.smt_ok; tcenv = uu___139_823.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu___140_836 = wl
in {attempting = uu___140_836.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = uu___140_836.ctr; defer_ok = uu___140_836.defer_ok; smt_ok = uu___140_836.smt_ok; tcenv = uu___140_836.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let uu___141_848 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = uu___141_848.wl_deferred; ctr = uu___141_848.ctr; defer_ok = uu___141_848.defer_ok; smt_ok = uu___141_848.smt_ok; tcenv = uu___141_848.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> ((

let uu____859 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____859) with
| true -> begin
(

let uu____860 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason uu____860))
end
| uu____861 -> begin
()
end));
Failed (((prob), (reason)));
))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun uu___108_864 -> (match (uu___108_864) with
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

let uu___142_880 = p
in {FStar_TypeChecker_Common.pid = uu___142_880.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = uu___142_880.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___142_880.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___142_880.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___142_880.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___142_880.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___142_880.FStar_TypeChecker_Common.rank}))


let maybe_invert = (fun p -> (match ((p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV)) with
| true -> begin
(invert p)
end
| uu____898 -> begin
p
end))


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___109_901 -> (match (uu___109_901) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_32 -> FStar_TypeChecker_Common.TProb (_0_32)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_33 -> FStar_TypeChecker_Common.CProb (_0_33)))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel uu___110_917 -> (match (uu___110_917) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun uu___111_920 -> (match (uu___111_920) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun uu___112_929 -> (match (uu___112_929) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun uu___113_939 -> (match (uu___113_939) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun uu___114_949 -> (match (uu___114_949) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun uu___115_960 -> (match (uu___115_960) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun uu___116_971 -> (match (uu___116_971) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___117_980 -> (match (uu___117_980) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _0_34 -> FStar_TypeChecker_Common.TProb (_0_34)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _0_35 -> FStar_TypeChecker_Common.CProb (_0_35)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> (

let uu____994 = (FStar_All.pipe_right (p_reason p) FStar_List.length)
in (uu____994 = (Prims.parse_int "1"))))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____1005 -> ((FStar_Util.incr ctr);
(FStar_ST.read ctr);
)))


let mk_problem = (fun scope orig lhs rel rhs elt reason -> (

let uu____1055 = (next_pid ())
in (

let uu____1056 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____1055; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____1056; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None})))


let new_problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (

let uu____1103 = (next_pid ())
in (

let uu____1104 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____1103; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____1104; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (

let uu____1145 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____1145; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None}))


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

let uu____1197 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____1197) with
| true -> begin
(

let uu____1198 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (

let uu____1199 = (prob_to_string env d)
in (

let uu____1200 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" uu____1198 uu____1199 uu____1200 s))))
end
| uu____1202 -> begin
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
| uu____1205 -> begin
(failwith "impossible")
end)
in (

let uu____1206 = (match (d1) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____1214 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (

let uu____1215 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((uu____1214), (uu____1215))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____1219 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (

let uu____1220 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((uu____1219), (uu____1220))))
end)
in (match (uu____1206) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___118_1229 -> (match (uu___118_1229) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| uu____1236 -> begin
(FStar_Unionfind.change u (FStar_Pervasives_Native.Some (t)))
end)
end
| TERM ((u, uu____1239), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun uv s -> (FStar_Util.find_map s (fun uu___119_1262 -> (match (uu___119_1262) with
| UNIV (uu____1264) -> begin
FStar_Pervasives_Native.None
end
| TERM ((u, uu____1268), t) -> begin
(

let uu____1272 = (FStar_Unionfind.equivalent uv u)
in (match (uu____1272) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____1277 -> begin
FStar_Pervasives_Native.None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun u s -> (FStar_Util.find_map s (fun uu___120_1291 -> (match (uu___120_1291) with
| UNIV (u', t) -> begin
(

let uu____1295 = (FStar_Unionfind.equivalent u u')
in (match (uu____1295) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____1298 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____1299 -> begin
FStar_Pervasives_Native.None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1306 = (

let uu____1307 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____1307))
in (FStar_Syntax_Subst.compress uu____1306)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1314 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress uu____1314)))


let norm_arg = (fun env t -> (

let uu____1333 = (sn env (FStar_Pervasives_Native.fst t))
in ((uu____1333), ((FStar_Pervasives_Native.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____1350 -> (match (uu____1350) with
| (x, imp) -> begin
(

let uu____1357 = (

let uu___143_1358 = x
in (

let uu____1359 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___143_1358.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___143_1358.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1359}))
in ((uu____1357), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____1374 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____1374))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1377 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____1377))
end
| uu____1379 -> begin
u2
end)))
in (

let uu____1380 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1380))))


let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement = (fun env wl t1 -> (

let rec aux = (fun norm t11 -> (match (t11.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(match (norm) with
| true -> begin
((x.FStar_Syntax_Syntax.sort), (FStar_Pervasives_Native.Some (((x), (phi)))))
end
| uu____1486 -> begin
(

let uu____1487 = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (match (uu____1487) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x1, phi1); FStar_Syntax_Syntax.tk = uu____1499; FStar_Syntax_Syntax.pos = uu____1500; FStar_Syntax_Syntax.vars = uu____1501} -> begin
((x1.FStar_Syntax_Syntax.sort), (FStar_Pervasives_Native.Some (((x1), (phi1)))))
end
| tt -> begin
(

let uu____1522 = (

let uu____1523 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____1524 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1523 uu____1524)))
in (failwith uu____1522))
end))
end)
end
| FStar_Syntax_Syntax.Tm_uinst (uu____1534) -> begin
(match (norm) with
| true -> begin
((t11), (FStar_Pervasives_Native.None))
end
| uu____1559 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (

let uu____1561 = (

let uu____1562 = (FStar_Syntax_Subst.compress t1')
in uu____1562.FStar_Syntax_Syntax.n)
in (match (uu____1561) with
| FStar_Syntax_Syntax.Tm_refine (uu____1574) -> begin
(aux true t1')
end
| uu____1579 -> begin
((t11), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1591) -> begin
(match (norm) with
| true -> begin
((t11), (FStar_Pervasives_Native.None))
end
| uu____1612 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (

let uu____1614 = (

let uu____1615 = (FStar_Syntax_Subst.compress t1')
in uu____1615.FStar_Syntax_Syntax.n)
in (match (uu____1614) with
| FStar_Syntax_Syntax.Tm_refine (uu____1627) -> begin
(aux true t1')
end
| uu____1632 -> begin
((t11), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_app (uu____1644) -> begin
(match (norm) with
| true -> begin
((t11), (FStar_Pervasives_Native.None))
end
| uu____1674 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (

let uu____1676 = (

let uu____1677 = (FStar_Syntax_Subst.compress t1')
in uu____1677.FStar_Syntax_Syntax.n)
in (match (uu____1676) with
| FStar_Syntax_Syntax.Tm_refine (uu____1689) -> begin
(aux true t1')
end
| uu____1694 -> begin
((t11), (FStar_Pervasives_Native.None))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_type (uu____1706) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_constant (uu____1718) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_name (uu____1730) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1742) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1754) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_abs (uu____1773) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1799) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_let (uu____1819) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_match (uu____1838) -> begin
((t11), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.Tm_meta (uu____1865) -> begin
(

let uu____1870 = (

let uu____1871 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____1872 = (FStar_Syntax_Print.tag_of_term t11)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1871 uu____1872)))
in (failwith uu____1870))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____1882) -> begin
(

let uu____1900 = (

let uu____1901 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____1902 = (FStar_Syntax_Print.tag_of_term t11)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1901 uu____1902)))
in (failwith uu____1900))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1912) -> begin
(

let uu____1933 = (

let uu____1934 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____1935 = (FStar_Syntax_Print.tag_of_term t11)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1934 uu____1935)))
in (failwith uu____1933))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____1945 = (

let uu____1946 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____1947 = (FStar_Syntax_Print.tag_of_term t11)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1946 uu____1947)))
in (failwith uu____1945))
end))
in (

let uu____1957 = (whnf env t1)
in (aux false uu____1957))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____1966 = (

let uu____1976 = (empty_worklist env)
in (base_and_refinement env uu____1976 t))
in (FStar_All.pipe_right uu____1966 FStar_Pervasives_Native.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (

let uu____2000 = (FStar_Syntax_Syntax.null_bv t)
in ((uu____2000), (FStar_Syntax_Util.t_true))))


let as_refinement = (fun env wl t -> (

let uu____2020 = (base_and_refinement env wl t)
in (match (uu____2020) with
| (t_base, refinement) -> begin
(match (refinement) with
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end
| FStar_Pervasives_Native.Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement = (fun uu____2079 -> (match (uu____2079) with
| (t_base, refopt) -> begin
(

let uu____2093 = (match (refopt) with
| FStar_Pervasives_Native.Some (y, phi) -> begin
((y), (phi))
end
| FStar_Pervasives_Native.None -> begin
(trivial_refinement t_base)
end)
in (match (uu____2093) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl uu___121_2117 -> (match (uu___121_2117) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____2121 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____2122 = (

let uu____2123 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string uu____2123))
in (

let uu____2124 = (

let uu____2125 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string uu____2125))
in (FStar_Util.format4 "%s: %s  (%s)  %s" uu____2121 uu____2122 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2124))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____2129 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____2130 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____2131 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" uu____2129 uu____2130 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2131))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (

let uu____2135 = (

let uu____2137 = (

let uu____2139 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____2149 -> (match (uu____2149) with
| (uu____2153, uu____2154, x) -> begin
x
end))))
in (FStar_List.append wl.attempting uu____2139))
in (FStar_List.map (wl_prob_to_string wl) uu____2137))
in (FStar_All.pipe_right uu____2135 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____2172 = (

let uu____2182 = (

let uu____2183 = (FStar_Syntax_Subst.compress k)
in uu____2183.FStar_Syntax_Syntax.n)
in (match (uu____2182) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (((FStar_List.length bs) = (FStar_List.length ys))) with
| true -> begin
(

let uu____2224 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (uu____2224)))
end
| uu____2237 -> begin
(

let uu____2238 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____2238) with
| (ys', t1, uu____2259) -> begin
(

let uu____2272 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t1))), (uu____2272)))
end))
end)
end
| uu____2293 -> begin
(

let uu____2294 = (

let uu____2300 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____2300)))
in ((((ys), (t))), (uu____2294)))
end))
in (match (uu____2172) with
| ((ys1, t1), (xs, c)) -> begin
(match (((FStar_List.length xs) <> (FStar_List.length ys1))) with
| true -> begin
(FStar_Syntax_Util.abs ys1 t1 (FStar_Pervasives_Native.Some (FStar_Util.Inr (((FStar_Parser_Const.effect_Tot_lid), ([]))))))
end
| uu____2353 -> begin
(

let c1 = (

let uu____2355 = (FStar_Syntax_Util.rename_binders xs ys1)
in (FStar_Syntax_Subst.subst_comp uu____2355 c))
in (

let uu____2357 = (

let uu____2364 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1) (fun _0_36 -> FStar_Util.Inl (_0_36)))
in (FStar_All.pipe_right uu____2364 (fun _0_37 -> FStar_Pervasives_Native.Some (_0_37))))
in (FStar_Syntax_Util.abs ys1 t1 uu____2357)))
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

let uu____2415 = (p_guard prob)
in (match (uu____2415) with
| (uu____2418, uv) -> begin
((

let uu____2421 = (

let uu____2422 = (FStar_Syntax_Subst.compress uv)
in uu____2422.FStar_Syntax_Syntax.n)
in (match (uu____2421) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi1 = (u_abs k bs phi)
in ((

let uu____2442 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____2442) with
| true -> begin
(

let uu____2443 = (FStar_Util.string_of_int (p_pid prob))
in (

let uu____2444 = (FStar_Syntax_Print.term_to_string uv)
in (

let uu____2445 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" uu____2443 uu____2444 uu____2445))))
end
| uu____2446 -> begin
()
end));
(FStar_Syntax_Util.set_uvar uvar phi1);
)))
end
| uu____2449 -> begin
(match ((not (resolve_ok))) with
| true -> begin
(failwith "Impossible: this instance has already been assigned a solution")
end
| uu____2450 -> begin
()
end)
end));
(commit uvis);
(

let uu___144_2452 = wl
in {attempting = uu___144_2452.attempting; wl_deferred = uu___144_2452.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___144_2452.defer_ok; smt_ok = uu___144_2452.smt_ok; tcenv = uu___144_2452.tcenv});
)
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____2465 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____2465) with
| true -> begin
(

let uu____2466 = (FStar_Util.string_of_int pid)
in (

let uu____2467 = (

let uu____2468 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right uu____2468 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____2466 uu____2467)))
end
| uu____2471 -> begin
()
end));
(commit sol);
(

let uu___145_2473 = wl
in {attempting = uu___145_2473.attempting; wl_deferred = uu___145_2473.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___145_2473.defer_ok; smt_ok = uu___145_2473.smt_ok; tcenv = uu___145_2473.tcenv});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard1 = (fun t g -> (match (((t), (g))) with
| (uu____2502, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (FStar_Pervasives_Native.None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
FStar_Pervasives_Native.Some (f)
end
| (FStar_Pervasives_Native.Some (t1), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(

let uu____2510 = (FStar_Syntax_Util.mk_conj t1 f)
in FStar_Pervasives_Native.Some (uu____2510))
end))
in ((

let uu____2516 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____2516) with
| true -> begin
(

let uu____2517 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (

let uu____2518 = (

let uu____2519 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right uu____2519 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____2517 uu____2518)))
end
| uu____2522 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
)))


let rec occurs = (fun wl uk t -> (

let uu____2544 = (

let uu____2548 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right uu____2548 FStar_Util.set_elements))
in (FStar_All.pipe_right uu____2544 (FStar_Util.for_some (fun uu____2569 -> (match (uu____2569) with
| (uv, uu____2577) -> begin
(FStar_Unionfind.equivalent uv (FStar_Pervasives_Native.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (

let uu____2621 = (occurs wl uk t)
in (not (uu____2621)))
in (

let msg = (match (occurs_ok) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____2625 -> begin
(

let uu____2626 = (

let uu____2627 = (FStar_Syntax_Print.uvar_to_string (FStar_Pervasives_Native.fst uk))
in (

let uu____2631 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" uu____2627 uu____2631)))
in FStar_Pervasives_Native.Some (uu____2626))
end)
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let uu____2679 = (occurs_check env wl uk t)
in (match (uu____2679) with
| (occurs_ok, msg) -> begin
(

let uu____2696 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (uu____2696), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set1 = (fun v3 -> (FStar_All.pipe_right v3 (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set1 v1)
in (

let uu____2760 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____2784 uu____2785 -> (match (((uu____2784), (uu____2785))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____2828 = (

let uu____2829 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation uu____2829))
in (match (uu____2828) with
| true -> begin
((isect), (isect_set))
end
| uu____2840 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____2843 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____2843) with
| true -> begin
(

let uu____2850 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (uu____2850)))
end
| uu____2858 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (uu____2760) with
| (isect, uu____2872) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____2921 uu____2922 -> (match (((uu____2921), (uu____2922))) with
| ((a, uu____2932), (b, uu____2934)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd1 = (norm_arg env arg)
in (match ((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(

let uu____2978 = (FStar_All.pipe_right seen (FStar_Util.for_some (fun uu____2984 -> (match (uu____2984) with
| (b, uu____2988) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end))))
in (match (uu____2978) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____2994 -> begin
FStar_Pervasives_Native.Some (((a), ((FStar_Pervasives_Native.snd hd1))))
end))
end
| uu____2997 -> begin
FStar_Pervasives_Native.None
end)))


let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option = (fun env seen args -> (match (args) with
| [] -> begin
FStar_Pervasives_Native.Some ((FStar_List.rev seen))
end
| (hd1)::rest -> begin
(

let uu____3040 = (pat_var_opt env seen hd1)
in (match (uu____3040) with
| FStar_Pervasives_Native.None -> begin
((

let uu____3048 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____3048) with
| true -> begin
(

let uu____3049 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (FStar_Pervasives_Native.fst hd1))
in (FStar_Util.print1 "Not a pattern: %s\n" uu____3049))
end
| uu____3050 -> begin
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

let uu____3061 = (

let uu____3062 = (FStar_Syntax_Subst.compress t)
in uu____3062.FStar_Syntax_Syntax.n)
in (match (uu____3061) with
| FStar_Syntax_Syntax.Tm_uvar (uu____3065) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____3074); FStar_Syntax_Syntax.tk = uu____3075; FStar_Syntax_Syntax.pos = uu____3076; FStar_Syntax_Syntax.vars = uu____3077}, uu____3078) -> begin
true
end
| uu____3101 -> begin
false
end)))


let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = uu____3163; FStar_Syntax_Syntax.pos = uu____3164; FStar_Syntax_Syntax.vars = uu____3165}, args) -> begin
((t), (uv), (k), (args))
end
| uu____3206 -> begin
(failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let uu____3260 = (destruct_flex_t t)
in (match (uu____3260) with
| (t1, uv, k, args) -> begin
(

let uu____3328 = (pat_vars env [] args)
in (match (uu____3328) with
| FStar_Pervasives_Native.Some (vars) -> begin
((((t1), (uv), (k), (args))), (FStar_Pervasives_Native.Some (vars)))
end
| uu____3384 -> begin
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
| uu____3433 -> begin
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
| uu____3456 -> begin
false
end))


let uu___is_FullMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullMatch -> begin
true
end
| uu____3460 -> begin
false
end))


let head_match : match_result  ->  match_result = (fun uu___122_3463 -> (match (uu___122_3463) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____3472 -> begin
HeadMatch
end))


let fv_delta_depth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.delta_depth = (fun env fv -> (match (fv.FStar_Syntax_Syntax.fv_delta) with
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(match ((env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)) with
| true -> begin
d
end
| uu____3484 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
end
| FStar_Syntax_Syntax.Delta_defined_at_level (uu____3485) -> begin
(

let uu____3486 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3486) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Syntax.Delta_constant
end
| uu____3496 -> begin
fv.FStar_Syntax_Syntax.fv_delta
end))
end
| d -> begin
d
end))


let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____3510) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____3516) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3538) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_name (uu____3539) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3540) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_let (uu____3549) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_match (uu____3557) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____3574) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____3580, uu____3581) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____3611) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____3626; FStar_Syntax_Syntax.index = uu____3627; FStar_Syntax_Syntax.sort = t2}, uu____3629) -> begin
(delta_depth_of_term env t2)
end
| FStar_Syntax_Syntax.Tm_constant (uu____3636) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_type (uu____3637) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3638) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_abs (uu____3646) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3662 = (fv_delta_depth env fv)
in FStar_Pervasives_Native.Some (uu____3662))
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
| uu____3676 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____3681 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____3681) with
| true -> begin
FullMatch
end
| uu____3682 -> begin
(

let uu____3683 = (

let uu____3688 = (

let uu____3690 = (fv_delta_depth env f)
in FStar_Pervasives_Native.Some (uu____3690))
in (

let uu____3691 = (

let uu____3693 = (fv_delta_depth env g)
in FStar_Pervasives_Native.Some (uu____3693))
in ((uu____3688), (uu____3691))))
in MisMatch (uu____3683))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____3697), FStar_Syntax_Syntax.Tm_uinst (g, uu____3699)) -> begin
(

let uu____3708 = (head_matches env f g)
in (FStar_All.pipe_right uu____3708 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(match ((c = d)) with
| true -> begin
FullMatch
end
| uu____3711 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end)
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, uu____3715), FStar_Syntax_Syntax.Tm_uvar (uv', uu____3717)) -> begin
(

let uu____3742 = (FStar_Unionfind.equivalent uv uv')
in (match (uu____3742) with
| true -> begin
FullMatch
end
| uu____3746 -> begin
MisMatch (((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____3750), FStar_Syntax_Syntax.Tm_refine (y, uu____3752)) -> begin
(

let uu____3761 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____3761 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____3763), uu____3764) -> begin
(

let uu____3769 = (head_matches env x.FStar_Syntax_Syntax.sort t21)
in (FStar_All.pipe_right uu____3769 head_match))
end
| (uu____3770, FStar_Syntax_Syntax.Tm_refine (x, uu____3772)) -> begin
(

let uu____3777 = (head_matches env t11 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____3777 head_match))
end
| (FStar_Syntax_Syntax.Tm_type (uu____3778), FStar_Syntax_Syntax.Tm_type (uu____3779)) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_arrow (uu____3780), FStar_Syntax_Syntax.Tm_arrow (uu____3781)) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____3797), FStar_Syntax_Syntax.Tm_app (head', uu____3799)) -> begin
(

let uu____3828 = (head_matches env head1 head')
in (FStar_All.pipe_right uu____3828 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____3830), uu____3831) -> begin
(

let uu____3846 = (head_matches env head1 t21)
in (FStar_All.pipe_right uu____3846 head_match))
end
| (uu____3847, FStar_Syntax_Syntax.Tm_app (head1, uu____3849)) -> begin
(

let uu____3864 = (head_matches env t11 head1)
in (FStar_All.pipe_right uu____3864 head_match))
end
| uu____3865 -> begin
(

let uu____3868 = (

let uu____3873 = (delta_depth_of_term env t11)
in (

let uu____3875 = (delta_depth_of_term env t21)
in ((uu____3873), (uu____3875))))
in MisMatch (uu____3868))
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let uu____3911 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____3911) with
| (head1, uu____3923) -> begin
(

let uu____3938 = (

let uu____3939 = (FStar_Syntax_Util.un_uinst head1)
in uu____3939.FStar_Syntax_Syntax.n)
in (match (uu____3938) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3944 = (

let uu____3945 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3945 FStar_Option.isSome))
in (match (uu____3944) with
| true -> begin
(

let uu____3959 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right uu____3959 (fun _0_38 -> FStar_Pervasives_Native.Some (_0_38))))
end
| uu____3961 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____3962 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (

let success = (fun d r t11 t21 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (((t11), (t21)))
end
| uu____3989 -> begin
FStar_Pervasives_Native.None
end))))
in (

let fail = (fun r -> ((r), (FStar_Pervasives_Native.None)))
in (

let rec aux = (fun retry n_delta t11 t21 -> (

let r = (head_matches env t11 t21)
in (match (r) with
| MisMatch (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational), uu____4030) -> begin
(match ((not (retry))) with
| true -> begin
(fail r)
end
| uu____4039 -> begin
(

let uu____4040 = (

let uu____4045 = (maybe_inline t11)
in (

let uu____4047 = (maybe_inline t21)
in ((uu____4045), (uu____4047))))
in (match (uu____4040) with
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
| MisMatch (uu____4068, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational)) -> begin
(match ((not (retry))) with
| true -> begin
(fail r)
end
| uu____4077 -> begin
(

let uu____4078 = (

let uu____4083 = (maybe_inline t11)
in (

let uu____4085 = (maybe_inline t21)
in ((uu____4083), (uu____4085))))
in (match (uu____4078) with
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

let uu____4110 = (FStar_TypeChecker_Common.decr_delta_depth d1)
in (match (uu____4110) with
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

let uu____4125 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in ((t1'), (t21)))
end
| uu____4131 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t21)
in (

let uu____4133 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t21)
in ((t11), (uu____4133))))
end)
in (match (uu____4125) with
| (t12, t22) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
end)))
end
| MisMatch (uu____4141) -> begin
(fail r)
end
| uu____4146 -> begin
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
| uu____4175 -> begin
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
| uu____4205 -> begin
false
end))


let __proj__C__item___0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_0) -> begin
_0
end))


type tcs =
tc Prims.list


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____4220 = (FStar_Syntax_Util.type_u ())
in (match (uu____4220) with
| (t, uu____4224) -> begin
(

let uu____4225 = (new_uvar r binders t)
in (FStar_Pervasives_Native.fst uu____4225))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____4234 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____4234 FStar_Pervasives_Native.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * variance * tc) Prims.list) = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (

let uu____4276 = (head_matches env t1 t')
in (match (uu____4276) with
| MisMatch (uu____4277) -> begin
false
end
| uu____4282 -> begin
true
end)))
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let rebuild = (fun args' -> (

let args1 = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((uu____4342, imp), T (t2, uu____4345)) -> begin
((t2), (imp))
end
| uu____4362 -> begin
(failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd1), (args1)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun uu____4402 -> (match (uu____4402) with
| (t2, uu____4410) -> begin
((FStar_Pervasives_Native.None), (INVARIANT), (T (((t2), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____4440 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4440) with
| (bs1, c1) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs2 tcs1 -> (match (((bs2), (tcs1))) with
| (((x, imp))::bs3, (T (t2, uu____4493))::tcs2) -> begin
(aux (((((

let uu___146_4515 = x
in {FStar_Syntax_Syntax.ppname = uu___146_4515.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___146_4515.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (imp)))::out) bs3 tcs2)
end
| ([], (C (c2))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c2)
end
| uu____4525 -> begin
(failwith "Bad reconstruction")
end))
in (aux [] bs1 tcs)))
in (

let rec decompose1 = (fun out uu___123_4556 -> (match (uu___123_4556) with
| [] -> begin
(FStar_List.rev ((((FStar_Pervasives_Native.None), (COVARIANT), (C (c1))))::out))
end
| (hd1)::rest -> begin
(decompose1 ((((FStar_Pervasives_Native.Some (hd1)), (CONTRAVARIANT), (T ((((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (

let uu____4619 = (decompose1 [] bs1)
in ((rebuild), (matches), (uu____4619)))))
end))
end
| uu____4647 -> begin
(

let rebuild = (fun uu___124_4652 -> (match (uu___124_4652) with
| [] -> begin
t1
end
| uu____4654 -> begin
(failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t2 -> true)), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun uu___125_4673 -> (match (uu___125_4673) with
| T (t, uu____4675) -> begin
t
end
| uu____4684 -> begin
(failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun uu___126_4687 -> (match (uu___126_4687) with
| T (t, uu____4689) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| uu____4698 -> begin
(failwith "Impossible")
end))


let imitation_sub_probs : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * variance * tc) Prims.list  ->  (FStar_TypeChecker_Common.prob Prims.list * tc Prims.list * FStar_Syntax_Syntax.formula) = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope1 args q -> (match (q) with
| (uu____4767, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope1 r)
in (

let uu____4786 = (new_uvar r scope1 k)
in (match (uu____4786) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| uu____4798 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) FStar_Pervasives_Native.None r)
end)
in (

let uu____4813 = (

let uu____4814 = (mk_problem scope1 orig gi_ps (vary_rel rel variance) ti FStar_Pervasives_Native.None "type subterm")
in (FStar_All.pipe_left (fun _0_39 -> FStar_TypeChecker_Common.TProb (_0_39)) uu____4814))
in ((T (((gi_xs), (mk_kind)))), (uu____4813))))
end)))
end
| (uu____4823, uu____4824, C (uu____4825)) -> begin
(failwith "impos")
end))
in (

let rec aux = (fun scope1 args qs1 -> (match (qs1) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs2 -> begin
(

let uu____4912 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.tk = uu____4923; FStar_Syntax_Syntax.pos = uu____4924; FStar_Syntax_Syntax.vars = uu____4925})) -> begin
(

let uu____4940 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____4940) with
| (T (gi_xs, uu____4956), prob) -> begin
(

let uu____4966 = (

let uu____4967 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_40 -> C (_0_40)) uu____4967))
in ((uu____4966), ((prob)::[])))
end
| uu____4969 -> begin
(failwith "impossible")
end))
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.tk = uu____4979; FStar_Syntax_Syntax.pos = uu____4980; FStar_Syntax_Syntax.vars = uu____4981})) -> begin
(

let uu____4996 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____4996) with
| (T (gi_xs, uu____5012), prob) -> begin
(

let uu____5022 = (

let uu____5023 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_41 -> C (_0_41)) uu____5023))
in ((uu____5022), ((prob)::[])))
end
| uu____5025 -> begin
(failwith "impossible")
end))
end
| (uu____5031, uu____5032, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = uu____5034; FStar_Syntax_Syntax.pos = uu____5035; FStar_Syntax_Syntax.vars = uu____5036})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((FStar_Pervasives_Native.None), (INVARIANT), (T ((((FStar_Pervasives_Native.fst t)), (generic_kind))))))))
in (

let components1 = (((FStar_Pervasives_Native.None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let uu____5110 = (

let uu____5115 = (FStar_List.map (sub_prob scope1 args) components1)
in (FStar_All.pipe_right uu____5115 FStar_List.unzip))
in (match (uu____5110) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (

let uu____5144 = (

let uu____5145 = (

let uu____5148 = (FStar_List.hd tcs)
in (FStar_All.pipe_right uu____5148 un_T))
in (

let uu____5149 = (

let uu____5155 = (FStar_List.tl tcs)
in (FStar_All.pipe_right uu____5155 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____5145; FStar_Syntax_Syntax.effect_args = uu____5149; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____5144))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| uu____5160 -> begin
(

let uu____5167 = (sub_prob scope1 args q)
in (match (uu____5167) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (uu____4912) with
| (tc, probs) -> begin
(

let uu____5185 = (match (q) with
| (FStar_Pervasives_Native.Some (b), uu____5211, uu____5212) -> begin
(

let uu____5220 = (

let uu____5224 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (uu____5224)::args)
in ((FStar_Pervasives_Native.Some (b)), ((b)::scope1), (uu____5220)))
end
| uu____5242 -> begin
((FStar_Pervasives_Native.None), (scope1), (args))
end)
in (match (uu____5185) with
| (bopt, scope2, args1) -> begin
(

let uu____5285 = (aux scope2 args1 qs2)
in (match (uu____5285) with
| (sub_probs, tcs, f) -> begin
(

let f1 = (match (bopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5306 = (

let uu____5308 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst))))
in (f)::uu____5308)
in (FStar_Syntax_Util.mk_conj_l uu____5306))
end
| FStar_Pervasives_Native.Some (b) -> begin
(

let u_b = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (

let uu____5321 = (

let uu____5323 = (FStar_Syntax_Util.mk_forall u_b (FStar_Pervasives_Native.fst b) f)
in (

let uu____5324 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst))))
in (uu____5323)::uu____5324))
in (FStar_Syntax_Util.mk_conj_l uu____5321)))
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

let uu___147_5377 = p
in (

let uu____5380 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____5381 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___147_5377.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____5380; FStar_TypeChecker_Common.relation = uu___147_5377.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____5381; FStar_TypeChecker_Common.element = uu___147_5377.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___147_5377.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___147_5377.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___147_5377.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___147_5377.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___147_5377.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p1) -> begin
(

let uu____5391 = (compress_tprob wl p1)
in (FStar_All.pipe_right uu____5391 (fun _0_42 -> FStar_TypeChecker_Common.TProb (_0_42))))
end
| FStar_TypeChecker_Common.CProb (uu____5396) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (

let uu____5410 = (compress_prob wl pr)
in (FStar_All.pipe_right uu____5410 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____5416 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____5416) with
| (lh, uu____5429) -> begin
(

let uu____5444 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____5444) with
| (rh, uu____5457) -> begin
(

let uu____5472 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____5481), FStar_Syntax_Syntax.Tm_uvar (uu____5482)) -> begin
((flex_flex), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____5501), uu____5502) when ((tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (uu____5513, FStar_Syntax_Syntax.Tm_uvar (uu____5514)) when ((tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____5525), uu____5526) -> begin
(

let uu____5535 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (uu____5535) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
((flex_rigid), (tp))
end
| uu____5575 -> begin
(

let rank = (

let uu____5582 = (is_top_level_prob prob)
in (match (uu____5582) with
| true -> begin
flex_refine
end
| uu____5583 -> begin
flex_refine_inner
end))
in (

let uu____5584 = (

let uu___148_5587 = tp
in (

let uu____5590 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___148_5587.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___148_5587.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___148_5587.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____5590; FStar_TypeChecker_Common.element = uu___148_5587.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___148_5587.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___148_5587.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___148_5587.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___148_5587.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___148_5587.FStar_TypeChecker_Common.rank}))
in ((rank), (uu____5584))))
end)
end))
end
| (uu____5600, FStar_Syntax_Syntax.Tm_uvar (uu____5601)) -> begin
(

let uu____5610 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (uu____5610) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
((rigid_flex), (tp))
end
| uu____5650 -> begin
(

let uu____5656 = (

let uu___149_5661 = tp
in (

let uu____5664 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___149_5661.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____5664; FStar_TypeChecker_Common.relation = uu___149_5661.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___149_5661.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___149_5661.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___149_5661.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___149_5661.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___149_5661.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___149_5661.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___149_5661.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (uu____5656)))
end)
end))
end
| (uu____5680, uu____5681) -> begin
((rigid_rigid), (tp))
end)
in (match (uu____5472) with
| (rank, tp1) -> begin
(

let uu____5692 = (FStar_All.pipe_right (

let uu___150_5695 = tp1
in {FStar_TypeChecker_Common.pid = uu___150_5695.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___150_5695.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___150_5695.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___150_5695.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___150_5695.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___150_5695.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___150_5695.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___150_5695.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___150_5695.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rank)}) (fun _0_43 -> FStar_TypeChecker_Common.TProb (_0_43)))
in ((rank), (uu____5692)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____5701 = (FStar_All.pipe_right (

let uu___151_5704 = cp
in {FStar_TypeChecker_Common.pid = uu___151_5704.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___151_5704.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___151_5704.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___151_5704.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___151_5704.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___151_5704.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___151_5704.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___151_5704.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___151_5704.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.Some (rigid_rigid)}) (fun _0_44 -> FStar_TypeChecker_Common.CProb (_0_44)))
in ((rigid_rigid), (uu____5701)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun uu____5736 probs -> (match (uu____5736) with
| (min_rank, min1, out) -> begin
(match (probs) with
| [] -> begin
((min1), (out), (min_rank))
end
| (hd1)::tl1 -> begin
(

let uu____5766 = (rank wl hd1)
in (match (uu____5766) with
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
| uu____5791 -> begin
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
| uu____5807 -> begin
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
| uu____5834 -> begin
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
| uu____5846 -> begin
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
| uu____5858 -> begin
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

let uu____5895 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____5895) with
| (k, uu____5899) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| uu____5904 -> begin
false
end)
end)))))
end
| uu____5905 -> begin
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

let uu____5948 = (really_solve_universe_eq pid_orig wl1 u13 u23)
in (match (uu____5948) with
| USolved (wl2) -> begin
(aux wl2 us12 us22)
end
| failed -> begin
failed
end))
end
| uu____5951 -> begin
USolved (wl1)
end))
in (aux wl us1 us2))
end
| uu____5956 -> begin
(

let uu____5957 = (

let uu____5958 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____5959 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" uu____5958 uu____5959)))
in UFailed (uu____5957))
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

let uu____5975 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____5975) with
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

let uu____5993 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____5993) with
| USolved (wl2) -> begin
(aux wl2 us2)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____5996 -> begin
(

let uu____5999 = (

let uu____6000 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____6001 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" uu____6000 uu____6001 msg)))
in UFailed (uu____5999))
end))
in (match (((u11), (u21))) with
| (FStar_Syntax_Syntax.U_bvar (uu____6002), uu____6003) -> begin
(

let uu____6004 = (

let uu____6005 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____6006 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____6005 uu____6006)))
in (failwith uu____6004))
end
| (FStar_Syntax_Syntax.U_unknown, uu____6007) -> begin
(

let uu____6008 = (

let uu____6009 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____6010 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____6009 uu____6010)))
in (failwith uu____6008))
end
| (uu____6011, FStar_Syntax_Syntax.U_bvar (uu____6012)) -> begin
(

let uu____6013 = (

let uu____6014 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____6015 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____6014 uu____6015)))
in (failwith uu____6013))
end
| (uu____6016, FStar_Syntax_Syntax.U_unknown) -> begin
(

let uu____6017 = (

let uu____6018 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____6019 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____6018 uu____6019)))
in (failwith uu____6017))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((x.FStar_Ident.idText = y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____6022 -> begin
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

let uu____6031 = (FStar_Unionfind.equivalent v1 v2)
in (match (uu____6031) with
| true -> begin
USolved (wl)
end
| uu____6033 -> begin
(

let wl1 = (extend_solution pid_orig ((UNIV (((v1), (u21))))::[]) wl)
in USolved (wl1))
end))
end
| (FStar_Syntax_Syntax.U_unif (v1), u) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____6042 = (occurs_univ v1 u3)
in (match (uu____6042) with
| true -> begin
(

let uu____6043 = (

let uu____6044 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____6045 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____6044 uu____6045)))
in (try_umax_components u11 u21 uu____6043))
end
| uu____6046 -> begin
(

let uu____6047 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____6047))
end)))
end
| (u, FStar_Syntax_Syntax.U_unif (v1)) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____6055 = (occurs_univ v1 u3)
in (match (uu____6055) with
| true -> begin
(

let uu____6056 = (

let uu____6057 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____6058 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____6057 uu____6058)))
in (try_umax_components u11 u21 uu____6056))
end
| uu____6059 -> begin
(

let uu____6060 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____6060))
end)))
end
| (FStar_Syntax_Syntax.U_max (uu____6063), uu____6064) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____6066 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____6069 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____6069) with
| true -> begin
USolved (wl)
end
| uu____6070 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (uu____6071, FStar_Syntax_Syntax.U_max (uu____6072)) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____6074 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____6077 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____6077) with
| true -> begin
USolved (wl)
end
| uu____6078 -> begin
(try_umax_components u12 u22 "")
end))))
end)
end
| (FStar_Syntax_Syntax.U_succ (uu____6079), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_succ (uu____6080), FStar_Syntax_Syntax.U_name (uu____6081)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ (uu____6082)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name (uu____6083)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____6084), FStar_Syntax_Syntax.U_succ (uu____6085)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (uu____6086), FStar_Syntax_Syntax.U_zero) -> begin
UFailed ("Incompatible universes")
end))))))


let solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (match (wl.tcenv.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
USolved (wl)
end
| uu____6099 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders = (fun bc1 bc2 -> (

let uu____6148 = bc1
in (match (uu____6148) with
| (bs1, mk_cod1) -> begin
(

let uu____6173 = bc2
in (match (uu____6173) with
| (bs2, mk_cod2) -> begin
(

let curry = (fun n1 bs mk_cod -> (

let uu____6220 = (FStar_Util.first_N n1 bs)
in (match (uu____6220) with
| (bs3, rest) -> begin
(

let uu____6234 = (mk_cod rest)
in ((bs3), (uu____6234)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(

let uu____6252 = (

let uu____6256 = (mk_cod1 [])
in ((bs1), (uu____6256)))
in (

let uu____6258 = (

let uu____6262 = (mk_cod2 [])
in ((bs2), (uu____6262)))
in ((uu____6252), (uu____6258))))
end
| uu____6270 -> begin
(match ((l1 > l2)) with
| true -> begin
(

let uu____6284 = (curry l2 bs1 mk_cod1)
in (

let uu____6291 = (

let uu____6295 = (mk_cod2 [])
in ((bs2), (uu____6295)))
in ((uu____6284), (uu____6291))))
end
| uu____6303 -> begin
(

let uu____6304 = (

let uu____6308 = (mk_cod1 [])
in ((bs1), (uu____6308)))
in (

let uu____6310 = (curry l1 bs2 mk_cod2)
in ((uu____6304), (uu____6310))))
end)
end))))
end))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____6414 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6414) with
| true -> begin
(

let uu____6415 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" uu____6415))
end
| uu____6416 -> begin
()
end));
(

let uu____6417 = (next_prob probs)
in (match (uu____6417) with
| (FStar_Pervasives_Native.Some (hd1), tl1, rank1) -> begin
(

let probs1 = (

let uu___152_6430 = probs
in {attempting = tl1; wl_deferred = uu___152_6430.wl_deferred; ctr = uu___152_6430.ctr; defer_ok = uu___152_6430.defer_ok; smt_ok = uu___152_6430.smt_ok; tcenv = uu___152_6430.tcenv})
in (match (hd1) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs1)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match ((((not (probs1.defer_ok)) && (flex_refine_inner <= rank1)) && (rank1 <= flex_rigid))) with
| true -> begin
(

let uu____6437 = (solve_flex_rigid_join env tp probs1)
in (match (uu____6437) with
| FStar_Pervasives_Native.None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| FStar_Pervasives_Native.Some (wl) -> begin
(solve env wl)
end))
end
| uu____6440 -> begin
(match ((((not (probs1.defer_ok)) && (rigid_flex <= rank1)) && (rank1 <= refine_flex))) with
| true -> begin
(

let uu____6441 = (solve_rigid_flex_meet env tp probs1)
in (match (uu____6441) with
| FStar_Pervasives_Native.None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| FStar_Pervasives_Native.Some (wl) -> begin
(solve env wl)
end))
end
| uu____6444 -> begin
(solve_t' env (maybe_invert tp) probs1)
end)
end)
end))
end
| (FStar_Pervasives_Native.None, uu____6445, uu____6446) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| uu____6455 -> begin
(

let uu____6460 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____6488 -> (match (uu____6488) with
| (c, uu____6493, uu____6494) -> begin
(c < probs.ctr)
end))))
in (match (uu____6460) with
| (attempt1, rest) -> begin
(match (attempt1) with
| [] -> begin
(

let uu____6516 = (FStar_List.map (fun uu____6522 -> (match (uu____6522) with
| (uu____6528, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (uu____6516))
end
| uu____6531 -> begin
(

let uu____6536 = (

let uu___153_6537 = probs
in (

let uu____6538 = (FStar_All.pipe_right attempt1 (FStar_List.map (fun uu____6547 -> (match (uu____6547) with
| (uu____6551, uu____6552, y) -> begin
y
end))))
in {attempting = uu____6538; wl_deferred = rest; ctr = uu___153_6537.ctr; defer_ok = uu___153_6537.defer_ok; smt_ok = uu___153_6537.smt_ok; tcenv = uu___153_6537.tcenv}))
in (solve env uu____6536))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____6559 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____6559) with
| USolved (wl1) -> begin
(

let uu____6561 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____6561))
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

let uu____6595 = (solve_universe_eq (p_pid orig) wl1 u1 u2)
in (match (uu____6595) with
| USolved (wl2) -> begin
(aux wl2 us11 us21)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____6598 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t11 = (whnf env t1)
in (

let t21 = (whnf env t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = uu____6606; FStar_Syntax_Syntax.pos = uu____6607; FStar_Syntax_Syntax.vars = uu____6608}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = uu____6611; FStar_Syntax_Syntax.pos = uu____6612; FStar_Syntax_Syntax.vars = uu____6613}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____6625), uu____6626) -> begin
(failwith "Impossible: expect head symbols to match")
end
| (uu____6631, FStar_Syntax_Syntax.Tm_uinst (uu____6632)) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____6637 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____6645 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6645) with
| true -> begin
(

let uu____6646 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" uu____6646 msg))
end
| uu____6647 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____6648 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist FStar_Pervasives_Native.option = (fun env tp wl -> ((

let uu____6654 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6654) with
| true -> begin
(

let uu____6655 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" uu____6655))
end
| uu____6656 -> begin
()
end));
(

let uu____6657 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____6657) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let uu____6699 = (head_matches_delta env () t1 t2)
in (match (uu____6699) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (uu____6721) -> begin
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

let uu____6747 = (match (ts) with
| FStar_Pervasives_Native.Some (t11, t21) -> begin
(

let uu____6756 = (FStar_Syntax_Subst.compress t11)
in (

let uu____6757 = (FStar_Syntax_Subst.compress t21)
in ((uu____6756), (uu____6757))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6760 = (FStar_Syntax_Subst.compress t1)
in (

let uu____6761 = (FStar_Syntax_Subst.compress t2)
in ((uu____6760), (uu____6761))))
end)
in (match (uu____6747) with
| (t11, t21) -> begin
(

let eq_prob = (fun t12 t22 -> (

let uu____6783 = (new_problem env t12 FStar_TypeChecker_Common.EQ t22 FStar_Pervasives_Native.None t12.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _0_45 -> FStar_TypeChecker_Common.TProb (_0_45)) uu____6783)))
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(

let uu____6806 = (

let uu____6812 = (

let uu____6815 = (

let uu____6818 = (

let uu____6819 = (

let uu____6824 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (uu____6824)))
in FStar_Syntax_Syntax.Tm_refine (uu____6819))
in (FStar_Syntax_Syntax.mk uu____6818))
in (uu____6815 FStar_Pervasives_Native.None t11.FStar_Syntax_Syntax.pos))
in (

let uu____6837 = (

let uu____6839 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (uu____6839)::[])
in ((uu____6812), (uu____6837))))
in FStar_Pervasives_Native.Some (uu____6806))
end
| (uu____6848, FStar_Syntax_Syntax.Tm_refine (x, uu____6850)) -> begin
(

let uu____6855 = (

let uu____6859 = (

let uu____6861 = (eq_prob x.FStar_Syntax_Syntax.sort t11)
in (uu____6861)::[])
in ((t11), (uu____6859)))
in FStar_Pervasives_Native.Some (uu____6855))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____6867), uu____6868) -> begin
(

let uu____6873 = (

let uu____6877 = (

let uu____6879 = (eq_prob x.FStar_Syntax_Syntax.sort t21)
in (uu____6879)::[])
in ((t21), (uu____6877)))
in FStar_Pervasives_Native.Some (uu____6873))
end
| uu____6884 -> begin
(

let uu____6887 = (FStar_Syntax_Util.head_and_args t11)
in (match (uu____6887) with
| (head1, uu____6902) -> begin
(

let uu____6917 = (

let uu____6918 = (FStar_Syntax_Util.un_uinst head1)
in uu____6918.FStar_Syntax_Syntax.n)
in (match (uu____6917) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____6925; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (i); FStar_Syntax_Syntax.fv_qual = uu____6927}) -> begin
(

let prev = (match ((i > (Prims.parse_int "1"))) with
| true -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i - (Prims.parse_int "1")))
end
| uu____6933 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
in (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t21)
in (disjoin t12 t22))))
end
| uu____6936 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____6945) -> begin
(

let uu____6958 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___127_6967 -> (match (uu___127_6967) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| FStar_Pervasives_Native.Some (rank1) when (is_rigid_flex rank1) -> begin
(

let uu____6972 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.rhs)
in (match (uu____6972) with
| (u', uu____6983) -> begin
(

let uu____6998 = (

let uu____6999 = (whnf env u')
in uu____6999.FStar_Syntax_Syntax.n)
in (match (uu____6998) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____7003) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____7019 -> begin
false
end))
end))
end
| uu____7020 -> begin
false
end)
end
| uu____7022 -> begin
false
end))))
in (match (uu____6958) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun uu____7043 tps -> (match (uu____7043) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
FStar_Pervasives_Native.Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____7070 = (

let uu____7075 = (whnf env hd1.FStar_TypeChecker_Common.lhs)
in (disjoin bound uu____7075))
in (match (uu____7070) with
| FStar_Pervasives_Native.Some (bound1, sub1) -> begin
(make_lower_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7094 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let uu____7099 = (

let uu____7104 = (

let uu____7108 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((uu____7108), ([])))
in (make_lower_bound uu____7104 lower_bounds))
in (match (uu____7099) with
| FStar_Pervasives_Native.None -> begin
((

let uu____7115 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____7115) with
| true -> begin
(FStar_Util.print_string "No lower bounds\n")
end
| uu____7116 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (lhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in ((

let uu____7128 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____7128) with
| true -> begin
(

let wl' = (

let uu___154_7130 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___154_7130.wl_deferred; ctr = uu___154_7130.ctr; defer_ok = uu___154_7130.defer_ok; smt_ok = uu___154_7130.smt_ok; tcenv = uu___154_7130.tcenv})
in (

let uu____7131 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" uu____7131)))
end
| uu____7132 -> begin
()
end));
(

let uu____7133 = (solve_t env eq_prob (

let uu___155_7134 = wl
in {attempting = sub_probs; wl_deferred = uu___155_7134.wl_deferred; ctr = uu___155_7134.ctr; defer_ok = uu___155_7134.defer_ok; smt_ok = uu___155_7134.smt_ok; tcenv = uu___155_7134.tcenv}))
in (match (uu____7133) with
| Success (uu____7136) -> begin
(

let wl1 = (

let uu___156_7138 = wl
in {attempting = rest; wl_deferred = uu___156_7138.wl_deferred; ctr = uu___156_7138.ctr; defer_ok = uu___156_7138.defer_ok; smt_ok = uu___156_7138.smt_ok; tcenv = uu___156_7138.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) FStar_Pervasives_Native.None [] wl1)
in (

let uu____7140 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p FStar_Pervasives_Native.None [] wl3)) wl2 lower_bounds)
in FStar_Pervasives_Native.Some (wl2))))
end
| uu____7143 -> begin
FStar_Pervasives_Native.None
end));
))
end)))
end))
end
| uu____7144 -> begin
(failwith "Impossible: Not a rigid-flex")
end)))
end));
))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist FStar_Pervasives_Native.option = (fun env tp wl -> ((

let uu____7151 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____7151) with
| true -> begin
(

let uu____7152 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" uu____7152))
end
| uu____7153 -> begin
()
end));
(

let uu____7154 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____7154) with
| (u, args) -> begin
(

let uu____7181 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (uu____7181) with
| (ok, head_match1, partial_match, fallback, failed_match) -> begin
(

let max1 = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____7200 -> begin
i
end))
in (

let base_types_match = (fun t1 t2 -> (

let uu____7212 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____7212) with
| (h1, args1) -> begin
(

let uu____7240 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____7240) with
| (h2, uu____7253) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
(

let uu____7272 = (FStar_Syntax_Syntax.fv_eq tc1 tc2)
in (match (uu____7272) with
| true -> begin
(match (((FStar_List.length args1) = (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____7284 -> begin
(

let uu____7285 = (

let uu____7287 = (

let uu____7288 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_46 -> FStar_TypeChecker_Common.TProb (_0_46)) uu____7288))
in (uu____7287)::[])
in FStar_Pervasives_Native.Some (uu____7285))
end)
end
| uu____7294 -> begin
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
| uu____7309 -> begin
(

let uu____7310 = (

let uu____7312 = (

let uu____7313 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_47 -> FStar_TypeChecker_Common.TProb (_0_47)) uu____7313))
in (uu____7312)::[])
in FStar_Pervasives_Native.Some (uu____7310))
end)
end
| uu____7319 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____7321 -> begin
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

let uu____7387 = (

let uu____7393 = (

let uu____7396 = (FStar_Syntax_Util.mk_conj phi11 phi21)
in (FStar_Syntax_Util.refine x1 uu____7396))
in ((uu____7393), (m1)))
in FStar_Pervasives_Native.Some (uu____7387))))))
end))
end
| (uu____7405, FStar_Syntax_Syntax.Tm_refine (y, uu____7407)) -> begin
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
| (FStar_Syntax_Syntax.Tm_refine (x, uu____7439), uu____7440) -> begin
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
| uu____7471 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____7505) -> begin
(

let uu____7518 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___128_7527 -> (match (uu___128_7527) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| FStar_Pervasives_Native.Some (rank1) when (is_flex_rigid rank1) -> begin
(

let uu____7532 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.lhs)
in (match (uu____7532) with
| (u', uu____7543) -> begin
(

let uu____7558 = (

let uu____7559 = (whnf env u')
in uu____7559.FStar_Syntax_Syntax.n)
in (match (uu____7558) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____7563) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____7579 -> begin
false
end))
end))
end
| uu____7580 -> begin
false
end)
end
| uu____7582 -> begin
false
end))))
in (match (uu____7518) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun uu____7607 tps -> (match (uu____7607) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
FStar_Pervasives_Native.Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____7648 = (

let uu____7655 = (whnf env hd1.FStar_TypeChecker_Common.rhs)
in (conjoin bound uu____7655))
in (match (uu____7648) with
| FStar_Pervasives_Native.Some (bound1, sub1) -> begin
(make_upper_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7690 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let uu____7697 = (

let uu____7704 = (

let uu____7710 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((uu____7710), ([])))
in (make_upper_bound uu____7704 upper_bounds))
in (match (uu____7697) with
| FStar_Pervasives_Native.None -> begin
((

let uu____7719 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____7719) with
| true -> begin
(FStar_Util.print_string "No upper bounds\n")
end
| uu____7720 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound FStar_Pervasives_Native.None tp.FStar_TypeChecker_Common.loc "joining refinements")
in ((

let uu____7738 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____7738) with
| true -> begin
(

let wl' = (

let uu___157_7740 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___157_7740.wl_deferred; ctr = uu___157_7740.ctr; defer_ok = uu___157_7740.defer_ok; smt_ok = uu___157_7740.smt_ok; tcenv = uu___157_7740.tcenv})
in (

let uu____7741 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" uu____7741)))
end
| uu____7742 -> begin
()
end));
(

let uu____7743 = (solve_t env eq_prob (

let uu___158_7744 = wl
in {attempting = sub_probs; wl_deferred = uu___158_7744.wl_deferred; ctr = uu___158_7744.ctr; defer_ok = uu___158_7744.defer_ok; smt_ok = uu___158_7744.smt_ok; tcenv = uu___158_7744.tcenv}))
in (match (uu____7743) with
| Success (uu____7746) -> begin
(

let wl1 = (

let uu___159_7748 = wl
in {attempting = rest; wl_deferred = uu___159_7748.wl_deferred; ctr = uu___159_7748.ctr; defer_ok = uu___159_7748.defer_ok; smt_ok = uu___159_7748.smt_ok; tcenv = uu___159_7748.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) FStar_Pervasives_Native.None [] wl1)
in (

let uu____7750 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p FStar_Pervasives_Native.None [] wl3)) wl2 upper_bounds)
in FStar_Pervasives_Native.Some (wl2))))
end
| uu____7753 -> begin
FStar_Pervasives_Native.None
end));
))
end)))
end))
end
| uu____7754 -> begin
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

let uu____7819 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____7819) with
| true -> begin
(

let uu____7820 = (prob_to_string env1 rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" uu____7820))
end
| uu____7821 -> begin
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

let uu___160_7852 = hd1
in (

let uu____7853 = (FStar_Syntax_Subst.subst subst1 hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___160_7852.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___160_7852.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7853}))
in (

let hd21 = (

let uu___161_7857 = hd2
in (

let uu____7858 = (FStar_Syntax_Subst.subst subst1 hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___161_7857.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___161_7857.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7858}))
in (

let prob = (

let uu____7862 = (

let uu____7865 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd11.FStar_Syntax_Syntax.sort uu____7865 hd21.FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None "Formal parameter"))
in (FStar_All.pipe_left (fun _0_48 -> FStar_TypeChecker_Common.TProb (_0_48)) uu____7862))
in (

let hd12 = (FStar_Syntax_Syntax.freshen_bv hd11)
in (

let subst2 = (

let uu____7873 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd12))))::uu____7873)
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 hd12)
in (

let uu____7876 = (aux ((((hd12), (imp)))::scope) env2 subst2 xs1 ys1)
in (match (uu____7876) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi1 = (

let uu____7894 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (

let uu____7897 = (close_forall env2 ((((hd12), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj uu____7894 uu____7897)))
in ((

let uu____7903 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____7903) with
| true -> begin
(

let uu____7904 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____7905 = (FStar_Syntax_Print.bv_to_string hd12)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" uu____7904 uu____7905)))
end
| uu____7906 -> begin
()
end));
FStar_Util.Inl ((((prob)::sub_probs), (phi1)));
))
end
| fail -> begin
fail
end))))))))
end
| uu____7920 -> begin
FStar_Util.Inr ("arity or argument-qualifier mismatch")
end))
in (

let scope = (p_scope orig)
in (

let uu____7926 = (aux scope env [] bs1 bs2)
in (match (uu____7926) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (phi)) [] wl)
in (solve env (attempt sub_probs wl1)))
end)))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let uu____7942 = (compress_tprob wl problem)
in (solve_t' env uu____7942 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer1 = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env1 orig wl1 head1 head2 t1 t2 -> (

let uu____7975 = (head_matches_delta env1 wl1 t1 t2)
in (match (uu____7975) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____7992), uu____7993) -> begin
(

let may_relate = (fun head3 -> (

let uu____8008 = (

let uu____8009 = (FStar_Syntax_Util.un_uinst head3)
in uu____8009.FStar_Syntax_Syntax.n)
in (match (uu____8008) with
| FStar_Syntax_Syntax.Tm_name (uu____8012) -> begin
true
end
| FStar_Syntax_Syntax.Tm_match (uu____8013) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____8030 -> begin
false
end)))
in (

let uu____8031 = (((may_relate head1) || (may_relate head2)) && wl1.smt_ok)
in (match (uu____8031) with
| true -> begin
(

let guard = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_eq2 env1 t1 t2)
end
| uu____8033 -> begin
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

let uu____8048 = (

let uu____8049 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t11 uu____8049 t21))
in (FStar_Syntax_Util.mk_forall u_x x uu____8048))))
end))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB)) with
| true -> begin
(has_type_guard t1 t2)
end
| uu____8050 -> begin
(has_type_guard t2 t1)
end))
end)
in (

let uu____8051 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl1)
in (solve env1 uu____8051)))
end
| uu____8052 -> begin
(giveup env1 "head mismatch" orig)
end)))
end
| (uu____8053, FStar_Pervasives_Native.Some (t11, t21)) -> begin
(solve_t env1 (

let uu___162_8061 = problem
in {FStar_TypeChecker_Common.pid = uu___162_8061.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___162_8061.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___162_8061.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_8061.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_8061.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_8061.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_8061.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_8061.FStar_TypeChecker_Common.rank}) wl1)
end
| (uu____8062, FStar_Pervasives_Native.None) -> begin
((

let uu____8069 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____8069) with
| true -> begin
(

let uu____8070 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____8071 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____8072 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____8073 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" uu____8070 uu____8071 uu____8072 uu____8073)))))
end
| uu____8074 -> begin
()
end));
(

let uu____8075 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____8075) with
| (head11, args1) -> begin
(

let uu____8101 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____8101) with
| (head21, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((nargs <> (FStar_List.length args2))) with
| true -> begin
(

let uu____8141 = (

let uu____8142 = (FStar_Syntax_Print.term_to_string head11)
in (

let uu____8143 = (args_to_string args1)
in (

let uu____8144 = (FStar_Syntax_Print.term_to_string head21)
in (

let uu____8145 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____8142 uu____8143 uu____8144 uu____8145)))))
in (giveup env1 uu____8141 orig))
end
| uu____8146 -> begin
(

let uu____8147 = ((nargs = (Prims.parse_int "0")) || (

let uu____8150 = (FStar_Syntax_Util.eq_args args1 args2)
in (uu____8150 = FStar_Syntax_Util.Equal)))
in (match (uu____8147) with
| true -> begin
(

let uu____8151 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____8151) with
| USolved (wl2) -> begin
(

let uu____8153 = (solve_prob orig FStar_Pervasives_Native.None [] wl2)
in (solve env1 uu____8153))
end
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end))
end
| uu____8156 -> begin
(

let uu____8157 = (base_and_refinement env1 wl1 t1)
in (match (uu____8157) with
| (base1, refinement1) -> begin
(

let uu____8183 = (base_and_refinement env1 wl1 t2)
in (match (uu____8183) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(

let uu____8237 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____8237) with
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end
| USolved (wl2) -> begin
(

let subprobs = (FStar_List.map2 (fun uu____8247 uu____8248 -> (match (((uu____8247), (uu____8248))) with
| ((a, uu____8258), (a', uu____8260)) -> begin
(

let uu____8265 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' FStar_Pervasives_Native.None "index")
in (FStar_All.pipe_left (fun _0_49 -> FStar_TypeChecker_Common.TProb (_0_49)) uu____8265))
end)) args1 args2)
in (

let formula = (

let uu____8271 = (FStar_List.map (fun p -> (FStar_Pervasives_Native.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____8271))
in (

let wl3 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) [] wl2)
in (solve env1 (attempt subprobs wl3)))))
end))
end
| uu____8275 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env1 (

let uu___163_8308 = problem
in {FStar_TypeChecker_Common.pid = uu___163_8308.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___163_8308.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___163_8308.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___163_8308.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___163_8308.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___163_8308.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___163_8308.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___163_8308.FStar_TypeChecker_Common.rank}) wl1)))
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

let uu____8328 = p
in (match (uu____8328) with
| (((u, k), xs, c), ps, (h, uu____8339, qs)) -> begin
(

let xs1 = (sn_binders env1 xs)
in (

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____8388 = (imitation_sub_probs orig env1 xs1 ps qs)
in (match (uu____8388) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (

let uu____8402 = (h gs_xs)
in (

let uu____8403 = (

let uu____8410 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_50 -> FStar_Util.Inl (_0_50)))
in (FStar_All.pipe_right uu____8410 (fun _0_51 -> FStar_Pervasives_Native.Some (_0_51))))
in (FStar_Syntax_Util.abs xs1 uu____8402 uu____8403)))
in ((

let uu____8441 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____8441) with
| true -> begin
(

let uu____8442 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____8443 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____8444 = (FStar_Syntax_Print.term_to_string im)
in (

let uu____8445 = (FStar_Syntax_Print.tag_of_term im)
in (

let uu____8446 = (

let uu____8447 = (FStar_List.map (prob_to_string env1) sub_probs)
in (FStar_All.pipe_right uu____8447 (FStar_String.concat ", ")))
in (

let uu____8450 = (FStar_TypeChecker_Normalize.term_to_string env1 formula)
in (FStar_Util.print6 "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" uu____8442 uu____8443 uu____8444 uu____8445 uu____8446 uu____8450)))))))
end
| uu____8451 -> begin
()
end));
(

let wl2 = (solve_prob orig (FStar_Pervasives_Native.Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl1)
in (solve env1 (attempt sub_probs wl2)));
))
end))))
end)))
in (

let imitate' = (fun orig env1 wl1 uu___129_8468 -> (match (uu___129_8468) with
| FStar_Pervasives_Native.None -> begin
(giveup env1 "unable to compute subterms" orig)
end
| FStar_Pervasives_Native.Some (p) -> begin
(imitate orig env1 wl1 p)
end))
in (

let project = (fun orig env1 wl1 i p -> (

let uu____8497 = p
in (match (uu____8497) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____8555 = (FStar_List.nth ps i)
in (match (uu____8555) with
| (pi, uu____8558) -> begin
(

let uu____8563 = (FStar_List.nth xs i)
in (match (uu____8563) with
| (xi, uu____8570) -> begin
(

let rec gs = (fun k -> (

let uu____8579 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____8579) with
| (bs, k1) -> begin
(

let rec aux = (fun subst1 bs1 -> (match (bs1) with
| [] -> begin
(([]), ([]))
end
| ((a, uu____8631))::tl1 -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst1 a.FStar_Syntax_Syntax.sort)
in (

let uu____8639 = (new_uvar r xs k_a)
in (match (uu____8639) with
| (gi_xs, gi) -> begin
(

let gi_xs1 = (FStar_TypeChecker_Normalize.eta_expand env1 gi_xs)
in (

let gi_ps = ((FStar_Syntax_Syntax.mk_Tm_app gi ps) (FStar_Pervasives_Native.Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((a), (gi_xs1))))::subst1
in (

let uu____8658 = (aux subst2 tl1)
in (match (uu____8658) with
| (gi_xs', gi_ps') -> begin
(

let uu____8673 = (

let uu____8675 = (FStar_Syntax_Syntax.as_arg gi_xs1)
in (uu____8675)::gi_xs')
in (

let uu____8676 = (

let uu____8678 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (uu____8678)::gi_ps')
in ((uu____8673), (uu____8676))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in (

let uu____8681 = (

let uu____8682 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation uu____8682))
in (match (uu____8681) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____8684 -> begin
(

let uu____8685 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (uu____8685) with
| (g_xs, uu____8692) -> begin
(

let xi1 = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (

let uu____8699 = ((FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs) FStar_Pervasives_Native.None r)
in (

let uu____8704 = (

let uu____8711 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_52 -> FStar_Util.Inl (_0_52)))
in (FStar_All.pipe_right uu____8711 (fun _0_53 -> FStar_Pervasives_Native.Some (_0_53))))
in (FStar_Syntax_Util.abs xs uu____8699 uu____8704)))
in (

let sub1 = (

let uu____8742 = (

let uu____8745 = ((FStar_Syntax_Syntax.mk_Tm_app proj ps) FStar_Pervasives_Native.None r)
in (

let uu____8752 = (

let uu____8755 = (FStar_List.map (fun uu____8761 -> (match (uu____8761) with
| (uu____8766, uu____8767, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h uu____8755))
in (mk_problem (p_scope orig) orig uu____8745 (p_rel orig) uu____8752 FStar_Pervasives_Native.None "projection")))
in (FStar_All.pipe_left (fun _0_54 -> FStar_TypeChecker_Common.TProb (_0_54)) uu____8742))
in ((

let uu____8777 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____8777) with
| true -> begin
(

let uu____8778 = (FStar_Syntax_Print.term_to_string proj)
in (

let uu____8779 = (prob_to_string env1 sub1)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" uu____8778 uu____8779)))
end
| uu____8780 -> begin
()
end));
(

let wl2 = (

let uu____8782 = (

let uu____8784 = (FStar_All.pipe_left FStar_Pervasives_Native.fst (p_guard sub1))
in FStar_Pervasives_Native.Some (uu____8784))
in (solve_prob orig uu____8782 ((TERM (((u), (proj))))::[]) wl1))
in (

let uu____8789 = (solve env1 (attempt ((sub1)::[]) wl2))
in (FStar_All.pipe_left (fun _0_55 -> FStar_Pervasives_Native.Some (_0_55)) uu____8789)));
))))
end))
end)))
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl1 -> (

let uu____8813 = lhs
in (match (uu____8813) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let uu____8836 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (uu____8836) with
| (xs, c) -> begin
(match (((FStar_List.length xs) = (FStar_List.length ps))) with
| true -> begin
(

let uu____8858 = (

let uu____8884 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____8884)))
in FStar_Pervasives_Native.Some (uu____8858))
end
| uu____8950 -> begin
(

let k_uv1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (

let uu____8967 = (

let uu____8971 = (

let uu____8972 = (FStar_Syntax_Subst.compress k)
in uu____8972.FStar_Syntax_Syntax.n)
in ((uu____8971), (args)))
in (match (uu____8967) with
| (uu____8979, []) -> begin
(

let uu____8981 = (

let uu____8987 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____8987)))
in FStar_Pervasives_Native.Some (uu____8981))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____8998), uu____8999) -> begin
(

let uu____9010 = (FStar_Syntax_Util.head_and_args k)
in (match (uu____9010) with
| (uv1, uv_args) -> begin
(

let uu____9039 = (

let uu____9040 = (FStar_Syntax_Subst.compress uv1)
in uu____9040.FStar_Syntax_Syntax.n)
in (match (uu____9039) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____9047) -> begin
(

let uu____9060 = (pat_vars env [] uv_args)
in (match (uu____9060) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (scope) -> begin
(

let xs1 = (FStar_All.pipe_right args (FStar_List.map (fun uu____9074 -> (

let uu____9075 = (

let uu____9076 = (

let uu____9077 = (

let uu____9080 = (

let uu____9081 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____9081 FStar_Pervasives_Native.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____9080))
in (FStar_Pervasives_Native.fst uu____9077))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.pos)) uu____9076))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____9075)))))
in (

let c1 = (

let uu____9087 = (

let uu____9088 = (

let uu____9091 = (

let uu____9092 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____9092 FStar_Pervasives_Native.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____9091))
in (FStar_Pervasives_Native.fst uu____9088))
in (FStar_Syntax_Syntax.mk_Total uu____9087))
in (

let k' = (FStar_Syntax_Util.arrow xs1 c1)
in (

let uv_sol = (

let uu____9101 = (

let uu____9108 = (

let uu____9114 = (

let uu____9115 = (

let uu____9118 = (

let uu____9119 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____9119 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.mk_Total uu____9118))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____9115))
in FStar_Util.Inl (uu____9114))
in FStar_Pervasives_Native.Some (uu____9108))
in (FStar_Syntax_Util.abs scope k' uu____9101))
in ((FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)));
FStar_Pervasives_Native.Some (((xs1), (c1)));
)))))
end))
end
| uu____9142 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_app (uu____9145), uu____9146) -> begin
(

let uu____9158 = (FStar_Syntax_Util.head_and_args k)
in (match (uu____9158) with
| (uv1, uv_args) -> begin
(

let uu____9187 = (

let uu____9188 = (FStar_Syntax_Subst.compress uv1)
in uu____9188.FStar_Syntax_Syntax.n)
in (match (uu____9187) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____9195) -> begin
(

let uu____9208 = (pat_vars env [] uv_args)
in (match (uu____9208) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (scope) -> begin
(

let xs1 = (FStar_All.pipe_right args (FStar_List.map (fun uu____9222 -> (

let uu____9223 = (

let uu____9224 = (

let uu____9225 = (

let uu____9228 = (

let uu____9229 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____9229 FStar_Pervasives_Native.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____9228))
in (FStar_Pervasives_Native.fst uu____9225))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.pos)) uu____9224))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____9223)))))
in (

let c1 = (

let uu____9235 = (

let uu____9236 = (

let uu____9239 = (

let uu____9240 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____9240 FStar_Pervasives_Native.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____9239))
in (FStar_Pervasives_Native.fst uu____9236))
in (FStar_Syntax_Syntax.mk_Total uu____9235))
in (

let k' = (FStar_Syntax_Util.arrow xs1 c1)
in (

let uv_sol = (

let uu____9249 = (

let uu____9256 = (

let uu____9262 = (

let uu____9263 = (

let uu____9266 = (

let uu____9267 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____9267 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.mk_Total uu____9266))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____9263))
in FStar_Util.Inl (uu____9262))
in FStar_Pervasives_Native.Some (uu____9256))
in (FStar_Syntax_Util.abs scope k' uu____9249))
in ((FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)));
FStar_Pervasives_Native.Some (((xs1), (c1)));
)))))
end))
end
| uu____9290 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs1, c1), uu____9295) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs1)
in (match ((n_xs = n_args)) with
| true -> begin
(

let uu____9321 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (FStar_All.pipe_right uu____9321 (fun _0_56 -> FStar_Pervasives_Native.Some (_0_56))))
end
| uu____9331 -> begin
(match ((n_xs < n_args)) with
| true -> begin
(

let uu____9340 = (FStar_Util.first_N n_xs args)
in (match (uu____9340) with
| (args1, rest) -> begin
(

let uu____9356 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (match (uu____9356) with
| (xs2, c2) -> begin
(

let uu____9364 = (elim (FStar_Syntax_Util.comp_result c2) rest)
in (FStar_Util.bind_opt uu____9364 (fun uu____9375 -> (match (uu____9375) with
| (xs', c3) -> begin
FStar_Pervasives_Native.Some ((((FStar_List.append xs2 xs')), (c3)))
end))))
end))
end))
end
| uu____9396 -> begin
(

let uu____9397 = (FStar_Util.first_N n_args xs1)
in (match (uu____9397) with
| (xs2, rest) -> begin
(

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c1))))) FStar_Pervasives_Native.None k.FStar_Syntax_Syntax.pos)
in (

let uu____9443 = (

let uu____9446 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs2 uu____9446))
in (FStar_All.pipe_right uu____9443 (fun _0_57 -> FStar_Pervasives_Native.Some (_0_57)))))
end))
end)
end)))
end
| uu____9454 -> begin
(

let uu____9458 = (

let uu____9459 = (FStar_Syntax_Print.uvar_to_string uv)
in (

let uu____9463 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____9464 = (FStar_Syntax_Print.term_to_string k_uv1)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" uu____9459 uu____9463 uu____9464))))
in (failwith uu____9458))
end)))
in (

let uu____9468 = (elim k_uv1 ps)
in (FStar_Util.bind_opt uu____9468 (fun uu____9496 -> (match (uu____9496) with
| (xs1, c1) -> begin
(

let uu____9524 = (

let uu____9547 = (decompose env t2)
in ((((((uv), (k_uv1))), (xs1), (c1))), (ps), (uu____9547)))
in FStar_Pervasives_Native.Some (uu____9524))
end))))))
end)
end)))
in (

let rec imitate_or_project = (fun n1 stopt i -> (match (((i >= n1) || (FStar_Option.isNone stopt))) with
| true -> begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end
| uu____9616 -> begin
(

let st = (FStar_Option.get stopt)
in (

let tx = (FStar_Unionfind.new_transaction ())
in (match ((i = (~- ((Prims.parse_int "1"))))) with
| true -> begin
(

let uu____9619 = (imitate orig env wl1 st)
in (match (uu____9619) with
| Failed (uu____9624) -> begin
((FStar_Unionfind.rollback tx);
(imitate_or_project n1 stopt (i + (Prims.parse_int "1")));
)
end
| sol -> begin
sol
end))
end
| uu____9629 -> begin
(

let uu____9630 = (project orig env wl1 i st)
in (match (uu____9630) with
| FStar_Pervasives_Native.None -> begin
((FStar_Unionfind.rollback tx);
(imitate_or_project n1 stopt (i + (Prims.parse_int "1")));
)
end
| FStar_Pervasives_Native.Some (Failed (uu____9637)) -> begin
((FStar_Unionfind.rollback tx);
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

let uu____9651 = (FStar_Syntax_Util.head_and_args t21)
in (match (uu____9651) with
| (hd1, uu____9662) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____9677) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____9685) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____9686) -> begin
true
end
| uu____9701 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd1)
in (

let uu____9704 = (FStar_Util.set_is_subset_of fvs_hd fvs1)
in (match (uu____9704) with
| true -> begin
true
end
| uu____9705 -> begin
((

let uu____9707 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9707) with
| true -> begin
(

let uu____9708 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" uu____9708))
end
| uu____9709 -> begin
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

let uu____9716 = (

let uu____9719 = (FStar_Syntax_Util.head_and_args t21)
in (FStar_All.pipe_right uu____9719 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____9716 FStar_Syntax_Free.names))
in (

let uu____9750 = (FStar_Util.set_is_empty fvs_hd)
in (match (uu____9750) with
| true -> begin
(~- ((Prims.parse_int "1")))
end
| uu____9751 -> begin
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

let uu____9759 = (occurs_check env wl1 ((uv), (k_uv)) t21)
in (match (uu____9759) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____9767 = (

let uu____9768 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____9768))
in (giveup_or_defer1 orig uu____9767))
end
| uu____9769 -> begin
(

let uu____9770 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____9770) with
| true -> begin
(

let uu____9771 = (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t21)) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))
in (match (uu____9771) with
| true -> begin
(

let uu____9772 = (subterms args_lhs)
in (imitate' orig env wl1 uu____9772))
end
| uu____9774 -> begin
((

let uu____9776 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9776) with
| true -> begin
(

let uu____9777 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____9778 = (names_to_string fvs1)
in (

let uu____9779 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" uu____9777 uu____9778 uu____9779))))
end
| uu____9780 -> begin
()
end));
(

let sol = (match (vars) with
| [] -> begin
t21
end
| uu____9784 -> begin
(

let uu____9785 = (sn_binders env vars)
in (u_abs k_uv uu____9785 t21))
end)
in (

let wl2 = (solve_prob orig FStar_Pervasives_Native.None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl1)
in (solve env wl2)));
)
end))
end
| uu____9792 -> begin
(match ((((not (patterns_only)) && wl1.defer_ok) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl1))
end
| uu____9793 -> begin
(

let uu____9794 = ((not (patterns_only)) && (check_head fvs1 t21))
in (match (uu____9794) with
| true -> begin
((

let uu____9796 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9796) with
| true -> begin
(

let uu____9797 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____9798 = (names_to_string fvs1)
in (

let uu____9799 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" uu____9797 uu____9798 uu____9799))))
end
| uu____9800 -> begin
()
end));
(

let uu____9801 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____9801 (~- ((Prims.parse_int "1")))));
)
end
| uu____9810 -> begin
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
| uu____9811 -> begin
(

let uu____9812 = (

let uu____9813 = (FStar_Syntax_Free.names t1)
in (check_head uu____9813 t2))
in (match (uu____9812) with
| true -> begin
(

let im_ok = (imitate_ok t2)
in ((

let uu____9817 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9817) with
| true -> begin
(

let uu____9818 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" uu____9818 (match ((im_ok < (Prims.parse_int "0"))) with
| true -> begin
"imitating"
end
| uu____9819 -> begin
"projecting"
end)))
end
| uu____9820 -> begin
()
end));
(

let uu____9821 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____9821 im_ok));
))
end
| uu____9830 -> begin
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
| uu____9841 -> begin
(

let force_quasi_pattern = (fun xs_opt uu____9863 -> (match (uu____9863) with
| (t, u, k, args) -> begin
(

let k1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let uu____9894 = (FStar_Syntax_Util.arrow_formals k1)
in (match (uu____9894) with
| (all_formals, uu____9905) -> begin
(

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args1 -> (match (((formals), (args1))) with
| ([], []) -> begin
(

let pat_args1 = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun uu____9997 -> (match (uu____9997) with
| (x, imp) -> begin
(

let uu____10004 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____10004), (imp)))
end))))
in (

let pattern_vars1 = (FStar_List.rev pattern_vars)
in (

let kk = (

let uu____10012 = (FStar_Syntax_Util.type_u ())
in (match (uu____10012) with
| (t1, uu____10016) -> begin
(

let uu____10017 = (new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1 t1)
in (FStar_Pervasives_Native.fst uu____10017))
end))
in (

let uu____10020 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk)
in (match (uu____10020) with
| (t', tm_u1) -> begin
(

let uu____10027 = (destruct_flex_t t')
in (match (uu____10027) with
| (uu____10047, u1, k11, uu____10050) -> begin
(

let sol = (

let uu____10078 = (

let uu____10083 = (u_abs k1 all_formals t')
in ((((u), (k1))), (uu____10083)))
in TERM (uu____10078))
in (

let t_app = ((FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in ((sol), (((t_app), (u1), (k11), (pat_args1))))))
end))
end)))))
end
| ((formal)::formals1, (hd1)::tl1) -> begin
(

let uu____10143 = (pat_var_opt env pat_args hd1)
in (match (uu____10143) with
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun uu____10172 -> (match (uu____10172) with
| (x, uu____10176) -> begin
(FStar_Syntax_Syntax.bv_eq x (FStar_Pervasives_Native.fst y))
end))))
end)
in (match ((not (maybe_pat))) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals1 tl1)
end
| uu____10179 -> begin
(

let fvs = (FStar_Syntax_Free.names (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____10182 = (

let uu____10183 = (FStar_Util.set_is_subset_of fvs pattern_var_set)
in (not (uu____10183)))
in (match (uu____10182) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals1 tl1)
end
| uu____10186 -> begin
(

let uu____10187 = (FStar_Util.set_add (FStar_Pervasives_Native.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) uu____10187 formals1 tl1))
end)))
end))
end))
end
| uu____10193 -> begin
(failwith "Impossible")
end))
in (

let uu____10204 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] uu____10204 all_formals args)))
end)))
end))
in (

let solve_both_pats = (fun wl1 uu____10252 uu____10253 r -> (match (((uu____10252), (uu____10253))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
(

let uu____10407 = ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys))
in (match (uu____10407) with
| true -> begin
(

let uu____10411 = (solve_prob orig FStar_Pervasives_Native.None [] wl1)
in (solve env uu____10411))
end
| uu____10412 -> begin
(

let xs1 = (sn_binders env xs)
in (

let ys1 = (sn_binders env ys)
in (

let zs = (intersect_vars xs1 ys1)
in ((

let uu____10426 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10426) with
| true -> begin
(

let uu____10427 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____10428 = (FStar_Syntax_Print.binders_to_string ", " ys1)
in (

let uu____10429 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (

let uu____10430 = (FStar_Syntax_Print.term_to_string k1)
in (

let uu____10431 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" uu____10427 uu____10428 uu____10429 uu____10430 uu____10431))))))
end
| uu____10432 -> begin
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

let uu____10473 = (FStar_Syntax_Util.subst_of_list xs2 args)
in (FStar_Syntax_Subst.subst uu____10473 k))
end
| uu____10475 -> begin
(match ((args_len < xs_len)) with
| true -> begin
(

let uu____10481 = (FStar_Util.first_N args_len xs2)
in (match (uu____10481) with
| (xs3, xs_rest) -> begin
(

let k3 = (

let uu____10511 = (FStar_Syntax_Syntax.mk_GTotal k)
in (FStar_Syntax_Util.arrow xs_rest uu____10511))
in (

let uu____10514 = (FStar_Syntax_Util.subst_of_list xs3 args)
in (FStar_Syntax_Subst.subst uu____10514 k3)))
end))
end
| uu____10516 -> begin
(

let uu____10517 = (

let uu____10518 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____10519 = (FStar_Syntax_Print.binders_to_string ", " xs2)
in (

let uu____10520 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" uu____10518 uu____10519 uu____10520))))
in (failwith uu____10517))
end)
end))))
in (

let uu____10521 = (

let uu____10527 = (

let uu____10535 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals uu____10535))
in (match (uu____10527) with
| (bs, k1') -> begin
(

let uu____10553 = (

let uu____10561 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals uu____10561))
in (match (uu____10553) with
| (cs, k2') -> begin
(

let k1'_xs = (subst_k k1' bs args1)
in (

let k2'_ys = (subst_k k2' cs args2)
in (

let sub_prob = (

let uu____10582 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys FStar_Pervasives_Native.None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_58 -> FStar_TypeChecker_Common.TProb (_0_58)) uu____10582))
in (

let uu____10587 = (

let uu____10590 = (

let uu____10591 = (FStar_Syntax_Subst.compress k1')
in uu____10591.FStar_Syntax_Syntax.n)
in (

let uu____10594 = (

let uu____10595 = (FStar_Syntax_Subst.compress k2')
in uu____10595.FStar_Syntax_Syntax.n)
in ((uu____10590), (uu____10594))))
in (match (uu____10587) with
| (FStar_Syntax_Syntax.Tm_type (uu____10603), uu____10604) -> begin
((k1'), ((sub_prob)::[]))
end
| (uu____10608, FStar_Syntax_Syntax.Tm_type (uu____10609)) -> begin
((k2'), ((sub_prob)::[]))
end
| uu____10613 -> begin
(

let uu____10616 = (FStar_Syntax_Util.type_u ())
in (match (uu____10616) with
| (t, uu____10625) -> begin
(

let uu____10626 = (new_uvar r zs t)
in (match (uu____10626) with
| (k_zs, uu____10635) -> begin
(

let kprob = (

let uu____10637 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k_zs FStar_Pervasives_Native.None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_59 -> FStar_TypeChecker_Common.TProb (_0_59)) uu____10637))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end)))))
end))
end))
in (match (uu____10521) with
| (k_u', sub_probs) -> begin
(

let uu____10651 = (

let uu____10659 = (

let uu____10660 = (new_uvar r zs k_u')
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10660))
in (

let uu____10665 = (

let uu____10668 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs1 uu____10668))
in (

let uu____10671 = (

let uu____10674 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys1 uu____10674))
in ((uu____10659), (uu____10665), (uu____10671)))))
in (match (uu____10651) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs1 u_zs)
in (

let uu____10693 = (occurs_check env wl1 ((u1), (k1)) sub1)
in (match (uu____10693) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occcurs check")
end
| uu____10705 -> begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in (

let uu____10717 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____10717) with
| true -> begin
(

let wl2 = (solve_prob orig FStar_Pervasives_Native.None ((sol1)::[]) wl1)
in (solve env wl2))
end
| uu____10722 -> begin
(

let sub2 = (u_abs knew2 ys1 u_zs)
in (

let uu____10724 = (occurs_check env wl1 ((u2), (k2)) sub2)
in (match (uu____10724) with
| (occurs_ok1, msg1) -> begin
(match ((not (occurs_ok1))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occurs check")
end
| uu____10736 -> begin
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

let solve_one_pat = (fun uu____10776 uu____10777 -> (match (((uu____10776), (uu____10777))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
((

let uu____10881 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10881) with
| true -> begin
(

let uu____10882 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10883 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" uu____10882 uu____10883)))
end
| uu____10884 -> begin
()
end));
(

let uu____10885 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____10885) with
| true -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____10895 uu____10896 -> (match (((uu____10895), (uu____10896))) with
| ((a, uu____10906), (t21, uu____10908)) -> begin
(

let uu____10913 = (

let uu____10916 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig uu____10916 FStar_TypeChecker_Common.EQ t21 FStar_Pervasives_Native.None "flex-flex index"))
in (FStar_All.pipe_right uu____10913 (fun _0_60 -> FStar_TypeChecker_Common.TProb (_0_60))))
end)) xs args2)
in (

let guard = (

let uu____10920 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) FStar_Pervasives_Native.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____10920))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))))
end
| uu____10926 -> begin
(

let t21 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t21)
in (

let uu____10930 = (occurs_check env wl ((u1), (k1)) t21)
in (match (uu____10930) with
| (occurs_ok, uu____10939) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in (

let uu____10944 = (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars))
in (match (uu____10944) with
| true -> begin
(

let sol = (

let uu____10946 = (

let uu____10951 = (u_abs k1 xs t21)
in ((((u1), (k1))), (uu____10951)))
in TERM (uu____10946))
in (

let wl1 = (solve_prob orig FStar_Pervasives_Native.None ((sol)::[]) wl)
in (solve env wl1)))
end
| uu____10963 -> begin
(

let uu____10964 = (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok))
in (match (uu____10964) with
| true -> begin
(

let uu____10965 = (force_quasi_pattern (FStar_Pervasives_Native.Some (xs)) ((t21), (u2), (k2), (args2)))
in (match (uu____10965) with
| (sol, (uu____10979, u21, k21, ys)) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____10989 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____10989) with
| true -> begin
(

let uu____10990 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" uu____10990))
end
| uu____10991 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____10995 -> begin
(giveup env "impossible" orig)
end);
))
end))
end
| uu____10996 -> begin
(giveup_or_defer1 orig "flex-flex constraint")
end))
end)))
end))))
end));
)
end))
in (

let uu____10997 = lhs
in (match (uu____10997) with
| (t1, u1, k1, args1) -> begin
(

let uu____11002 = rhs
in (match (uu____11002) with
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
| uu____11028 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: neither side is a pattern")
end
| uu____11033 -> begin
(

let uu____11034 = (force_quasi_pattern FStar_Pervasives_Native.None ((t1), (u1), (k1), (args1)))
in (match (uu____11034) with
| (sol, uu____11041) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____11044 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____11044) with
| true -> begin
(

let uu____11045 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" uu____11045))
end
| uu____11046 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____11050 -> begin
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

let uu____11052 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____11052) with
| true -> begin
(

let uu____11053 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____11053))
end
| uu____11054 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in (

let uu____11057 = (FStar_Util.physical_equality t1 t2)
in (match (uu____11057) with
| true -> begin
(

let uu____11058 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____11058))
end
| uu____11059 -> begin
((

let uu____11061 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____11061) with
| true -> begin
(

let uu____11062 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" uu____11062))
end
| uu____11063 -> begin
()
end));
(

let r = (FStar_TypeChecker_Env.get_range env)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_bvar (uu____11065), uu____11066) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (uu____11067, FStar_Syntax_Syntax.Tm_bvar (uu____11068)) -> begin
(failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (FStar_Syntax_Syntax.Tm_type (u1), FStar_Syntax_Syntax.Tm_type (u2)) -> begin
(solve_one_universe_eq env orig u1 u2 wl)
end
| (FStar_Syntax_Syntax.Tm_arrow (bs1, c1), FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) -> begin
(

let mk_c = (fun c uu___130_11108 -> (match (uu___130_11108) with
| [] -> begin
c
end
| bs -> begin
(

let uu____11122 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____11122))
end))
in (

let uu____11132 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____11132) with
| ((bs11, c11), (bs21, c21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let c12 = (FStar_Syntax_Subst.subst_comp subst1 c11)
in (

let c22 = (FStar_Syntax_Subst.subst_comp subst1 c21)
in (

let rel = (

let uu____11218 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____11218) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____11219 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (

let uu____11220 = (mk_problem scope orig c12 rel c22 FStar_Pervasives_Native.None "function co-domain")
in (FStar_All.pipe_left (fun _0_61 -> FStar_TypeChecker_Common.CProb (_0_61)) uu____11220)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___131_11297 -> (match (uu___131_11297) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____11332 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____11332) with
| ((bs11, tbody11), (bs21, tbody21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let uu____11415 = (

let uu____11418 = (FStar_Syntax_Subst.subst subst1 tbody11)
in (

let uu____11419 = (FStar_Syntax_Subst.subst subst1 tbody21)
in (mk_problem scope orig uu____11418 problem.FStar_TypeChecker_Common.relation uu____11419 FStar_Pervasives_Native.None "lambda co-domain")))
in (FStar_All.pipe_left (fun _0_62 -> FStar_TypeChecker_Common.TProb (_0_62)) uu____11415))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (uu____11422), uu____11423) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____11446) -> begin
true
end
| uu____11461 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____11480 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____11486 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let uu____11489 = (

let uu____11500 = (maybe_eta t1)
in (

let uu____11505 = (maybe_eta t2)
in ((uu____11500), (uu____11505))))
in (match (uu____11489) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___164_11536 = problem
in {FStar_TypeChecker_Common.pid = uu___164_11536.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___164_11536.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___164_11536.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_11536.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_11536.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_11536.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_11536.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_11536.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____11555 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____11555) with
| true -> begin
(

let uu____11556 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____11556 t_abs wl))
end
| uu____11560 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____11577 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____11577) with
| true -> begin
(

let uu____11578 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____11578 t_abs wl))
end
| uu____11582 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| uu____11583 -> begin
(failwith "Impossible: at least one side is an abstraction")
end))))
end
| (uu____11594, FStar_Syntax_Syntax.Tm_abs (uu____11595)) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____11618) -> begin
true
end
| uu____11633 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____11652 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____11658 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let uu____11661 = (

let uu____11672 = (maybe_eta t1)
in (

let uu____11677 = (maybe_eta t2)
in ((uu____11672), (uu____11677))))
in (match (uu____11661) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___164_11708 = problem
in {FStar_TypeChecker_Common.pid = uu___164_11708.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___164_11708.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___164_11708.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_11708.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_11708.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_11708.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_11708.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_11708.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs)) -> begin
(

let uu____11727 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____11727) with
| true -> begin
(

let uu____11728 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____11728 t_abs wl))
end
| uu____11732 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| (FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs)) -> begin
(

let uu____11749 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____11749) with
| true -> begin
(

let uu____11750 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____11750 t_abs wl))
end
| uu____11754 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| uu____11755 -> begin
(failwith "Impossible: at least one side is an abstraction")
end))))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____11766), FStar_Syntax_Syntax.Tm_refine (uu____11767)) -> begin
(

let uu____11776 = (as_refinement env wl t1)
in (match (uu____11776) with
| (x1, phi1) -> begin
(

let uu____11781 = (as_refinement env wl t2)
in (match (uu____11781) with
| (x2, phi2) -> begin
(

let base_prob = (

let uu____11787 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _0_63 -> FStar_TypeChecker_Common.TProb (_0_63)) uu____11787))
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

let uu____11820 = (imp phi12 phi22)
in (FStar_All.pipe_right uu____11820 (guard_on_element wl problem x11))))
in (

let fallback = (fun uu____11824 -> (

let impl = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp1 FStar_Syntax_Util.mk_iff phi11 phi21)
end
| uu____11826 -> begin
(mk_imp1 FStar_Syntax_Util.mk_imp phi11 phi21)
end)
in (

let guard = (

let uu____11830 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____11830 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env1 (attempt ((base_prob)::[]) wl1))))))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let ref_prob = (

let uu____11837 = (

let uu____11840 = (

let uu____11841 = (FStar_Syntax_Syntax.mk_binder x11)
in (uu____11841)::(p_scope orig))
in (mk_problem uu____11840 orig phi11 FStar_TypeChecker_Common.EQ phi21 FStar_Pervasives_Native.None "refinement formula"))
in (FStar_All.pipe_left (fun _0_64 -> FStar_TypeChecker_Common.TProb (_0_64)) uu____11837))
in (

let uu____11844 = (solve env1 (

let uu___165_11845 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___165_11845.ctr; defer_ok = false; smt_ok = uu___165_11845.smt_ok; tcenv = uu___165_11845.tcenv}))
in (match (uu____11844) with
| Failed (uu____11849) -> begin
(fallback ())
end
| Success (uu____11852) -> begin
(

let guard = (

let uu____11856 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (

let uu____11859 = (

let uu____11860 = (FStar_All.pipe_right (p_guard ref_prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____11860 (guard_on_element wl problem x11)))
in (FStar_Syntax_Util.mk_conj uu____11856 uu____11859)))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (

let wl2 = (

let uu___166_11867 = wl1
in {attempting = uu___166_11867.attempting; wl_deferred = uu___166_11867.wl_deferred; ctr = (wl1.ctr + (Prims.parse_int "1")); defer_ok = uu___166_11867.defer_ok; smt_ok = uu___166_11867.smt_ok; tcenv = uu___166_11867.tcenv})
in (solve env1 (attempt ((base_prob)::[]) wl2)))))
end)))
end
| uu____11868 -> begin
(fallback ())
end)))))))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____11869), FStar_Syntax_Syntax.Tm_uvar (uu____11870)) -> begin
(

let uu____11887 = (destruct_flex_t t1)
in (

let uu____11888 = (destruct_flex_t t2)
in (flex_flex1 orig uu____11887 uu____11888)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____11889); FStar_Syntax_Syntax.tk = uu____11890; FStar_Syntax_Syntax.pos = uu____11891; FStar_Syntax_Syntax.vars = uu____11892}, uu____11893), FStar_Syntax_Syntax.Tm_uvar (uu____11894)) -> begin
(

let uu____11925 = (destruct_flex_t t1)
in (

let uu____11926 = (destruct_flex_t t2)
in (flex_flex1 orig uu____11925 uu____11926)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____11927), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____11928); FStar_Syntax_Syntax.tk = uu____11929; FStar_Syntax_Syntax.pos = uu____11930; FStar_Syntax_Syntax.vars = uu____11931}, uu____11932)) -> begin
(

let uu____11963 = (destruct_flex_t t1)
in (

let uu____11964 = (destruct_flex_t t2)
in (flex_flex1 orig uu____11963 uu____11964)))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____11965); FStar_Syntax_Syntax.tk = uu____11966; FStar_Syntax_Syntax.pos = uu____11967; FStar_Syntax_Syntax.vars = uu____11968}, uu____11969), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____11970); FStar_Syntax_Syntax.tk = uu____11971; FStar_Syntax_Syntax.pos = uu____11972; FStar_Syntax_Syntax.vars = uu____11973}, uu____11974)) -> begin
(

let uu____12019 = (destruct_flex_t t1)
in (

let uu____12020 = (destruct_flex_t t2)
in (flex_flex1 orig uu____12019 uu____12020)))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____12021), uu____12022) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(

let uu____12031 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____12031 t2 wl))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12035); FStar_Syntax_Syntax.tk = uu____12036; FStar_Syntax_Syntax.pos = uu____12037; FStar_Syntax_Syntax.vars = uu____12038}, uu____12039), uu____12040) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(

let uu____12063 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____12063 t2 wl))
end
| (uu____12067, FStar_Syntax_Syntax.Tm_uvar (uu____12068)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (uu____12077, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12078); FStar_Syntax_Syntax.tk = uu____12079; FStar_Syntax_Syntax.pos = uu____12080; FStar_Syntax_Syntax.vars = uu____12081}, uu____12082)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____12105), FStar_Syntax_Syntax.Tm_type (uu____12106)) -> begin
(solve_t' env (

let uu___167_12115 = problem
in {FStar_TypeChecker_Common.pid = uu___167_12115.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___167_12115.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___167_12115.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___167_12115.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___167_12115.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___167_12115.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___167_12115.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___167_12115.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___167_12115.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12116); FStar_Syntax_Syntax.tk = uu____12117; FStar_Syntax_Syntax.pos = uu____12118; FStar_Syntax_Syntax.vars = uu____12119}, uu____12120), FStar_Syntax_Syntax.Tm_type (uu____12121)) -> begin
(solve_t' env (

let uu___167_12144 = problem
in {FStar_TypeChecker_Common.pid = uu___167_12144.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___167_12144.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___167_12144.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___167_12144.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___167_12144.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___167_12144.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___167_12144.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___167_12144.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___167_12144.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____12145), FStar_Syntax_Syntax.Tm_arrow (uu____12146)) -> begin
(solve_t' env (

let uu___167_12162 = problem
in {FStar_TypeChecker_Common.pid = uu___167_12162.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___167_12162.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___167_12162.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___167_12162.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___167_12162.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___167_12162.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___167_12162.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___167_12162.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___167_12162.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12163); FStar_Syntax_Syntax.tk = uu____12164; FStar_Syntax_Syntax.pos = uu____12165; FStar_Syntax_Syntax.vars = uu____12166}, uu____12167), FStar_Syntax_Syntax.Tm_arrow (uu____12168)) -> begin
(solve_t' env (

let uu___167_12198 = problem
in {FStar_TypeChecker_Common.pid = uu___167_12198.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___167_12198.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___167_12198.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___167_12198.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___167_12198.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___167_12198.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___167_12198.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___167_12198.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___167_12198.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____12199), uu____12200) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____12209 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____12211 = (

let uu____12212 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____12212))
in (match (uu____12211) with
| true -> begin
(

let uu____12213 = (FStar_All.pipe_left (fun _0_65 -> FStar_TypeChecker_Common.TProb (_0_65)) (

let uu___168_12216 = problem
in {FStar_TypeChecker_Common.pid = uu___168_12216.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___168_12216.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___168_12216.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___168_12216.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___168_12216.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___168_12216.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___168_12216.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___168_12216.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___168_12216.FStar_TypeChecker_Common.rank}))
in (

let uu____12217 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____12213 uu____12217 t2 wl)))
end
| uu____12221 -> begin
(

let uu____12222 = (base_and_refinement env wl t2)
in (match (uu____12222) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12252 = (FStar_All.pipe_left (fun _0_66 -> FStar_TypeChecker_Common.TProb (_0_66)) (

let uu___169_12255 = problem
in {FStar_TypeChecker_Common.pid = uu___169_12255.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___169_12255.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___169_12255.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___169_12255.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___169_12255.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___169_12255.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___169_12255.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___169_12255.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___169_12255.FStar_TypeChecker_Common.rank}))
in (

let uu____12256 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____12252 uu____12256 t_base wl)))
end
| FStar_Pervasives_Native.Some (y, phi) -> begin
(

let y' = (

let uu___170_12271 = y
in {FStar_Syntax_Syntax.ppname = uu___170_12271.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___170_12271.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let base_prob = (

let uu____12274 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_67 -> FStar_TypeChecker_Common.TProb (_0_67)) uu____12274))
in (

let guard = (

let uu____12282 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____12282 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl1)))))))
end)
end))
end)))
end)
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12288); FStar_Syntax_Syntax.tk = uu____12289; FStar_Syntax_Syntax.pos = uu____12290; FStar_Syntax_Syntax.vars = uu____12291}, uu____12292), uu____12293) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____12316 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____12318 = (

let uu____12319 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____12319))
in (match (uu____12318) with
| true -> begin
(

let uu____12320 = (FStar_All.pipe_left (fun _0_68 -> FStar_TypeChecker_Common.TProb (_0_68)) (

let uu___168_12323 = problem
in {FStar_TypeChecker_Common.pid = uu___168_12323.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___168_12323.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___168_12323.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___168_12323.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___168_12323.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___168_12323.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___168_12323.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___168_12323.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___168_12323.FStar_TypeChecker_Common.rank}))
in (

let uu____12324 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____12320 uu____12324 t2 wl)))
end
| uu____12328 -> begin
(

let uu____12329 = (base_and_refinement env wl t2)
in (match (uu____12329) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12359 = (FStar_All.pipe_left (fun _0_69 -> FStar_TypeChecker_Common.TProb (_0_69)) (

let uu___169_12362 = problem
in {FStar_TypeChecker_Common.pid = uu___169_12362.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___169_12362.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___169_12362.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___169_12362.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___169_12362.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___169_12362.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___169_12362.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___169_12362.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___169_12362.FStar_TypeChecker_Common.rank}))
in (

let uu____12363 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____12359 uu____12363 t_base wl)))
end
| FStar_Pervasives_Native.Some (y, phi) -> begin
(

let y' = (

let uu___170_12378 = y
in {FStar_Syntax_Syntax.ppname = uu___170_12378.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___170_12378.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let base_prob = (

let uu____12381 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_70 -> FStar_TypeChecker_Common.TProb (_0_70)) uu____12381))
in (

let guard = (

let uu____12389 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____12389 impl))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl1)))))))
end)
end))
end)))
end)
end
| (uu____12395, FStar_Syntax_Syntax.Tm_uvar (uu____12396)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| uu____12405 -> begin
(

let uu____12406 = (base_and_refinement env wl t1)
in (match (uu____12406) with
| (t_base, uu____12417) -> begin
(solve_t env (

let uu___171_12432 = problem
in {FStar_TypeChecker_Common.pid = uu___171_12432.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___171_12432.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___171_12432.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___171_12432.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___171_12432.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___171_12432.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___171_12432.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___171_12432.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (uu____12435, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____12436); FStar_Syntax_Syntax.tk = uu____12437; FStar_Syntax_Syntax.pos = uu____12438; FStar_Syntax_Syntax.vars = uu____12439}, uu____12440)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| uu____12463 -> begin
(

let uu____12464 = (base_and_refinement env wl t1)
in (match (uu____12464) with
| (t_base, uu____12475) -> begin
(solve_t env (

let uu___171_12490 = problem
in {FStar_TypeChecker_Common.pid = uu___171_12490.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___171_12490.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___171_12490.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___171_12490.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___171_12490.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___171_12490.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___171_12490.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___171_12490.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (FStar_Syntax_Syntax.Tm_refine (uu____12493), uu____12494) -> begin
(

let t21 = (

let uu____12502 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement uu____12502))
in (solve_t env (

let uu___172_12515 = problem
in {FStar_TypeChecker_Common.pid = uu___172_12515.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___172_12515.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___172_12515.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___172_12515.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___172_12515.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___172_12515.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___172_12515.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___172_12515.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___172_12515.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____12516, FStar_Syntax_Syntax.Tm_refine (uu____12517)) -> begin
(

let t11 = (

let uu____12525 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement uu____12525))
in (solve_t env (

let uu___173_12538 = problem
in {FStar_TypeChecker_Common.pid = uu___173_12538.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___173_12538.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___173_12538.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___173_12538.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___173_12538.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___173_12538.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___173_12538.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___173_12538.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___173_12538.FStar_TypeChecker_Common.rank}) wl))
end
| (FStar_Syntax_Syntax.Tm_match (uu____12541), uu____12542) -> begin
(

let head1 = (

let uu____12561 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____12561 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____12592 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____12592 FStar_Pervasives_Native.fst))
in (

let uu____12620 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____12620) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____12629 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____12629) with
| true -> begin
(

let guard = (

let uu____12636 = (

let uu____12637 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____12637 = FStar_Syntax_Util.Equal))
in (match (uu____12636) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____12639 -> begin
(

let uu____12640 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_71 -> FStar_Pervasives_Native.Some (_0_71)) uu____12640))
end))
in (

let uu____12642 = (solve_prob orig guard [] wl)
in (solve env uu____12642)))
end
| uu____12643 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____12644 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_uinst (uu____12645), uu____12646) -> begin
(

let head1 = (

let uu____12654 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____12654 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____12685 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____12685 FStar_Pervasives_Native.fst))
in (

let uu____12713 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____12713) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____12722 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____12722) with
| true -> begin
(

let guard = (

let uu____12729 = (

let uu____12730 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____12730 = FStar_Syntax_Util.Equal))
in (match (uu____12729) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____12732 -> begin
(

let uu____12733 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_72 -> FStar_Pervasives_Native.Some (_0_72)) uu____12733))
end))
in (

let uu____12735 = (solve_prob orig guard [] wl)
in (solve env uu____12735)))
end
| uu____12736 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____12737 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_name (uu____12738), uu____12739) -> begin
(

let head1 = (

let uu____12743 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____12743 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____12774 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____12774 FStar_Pervasives_Native.fst))
in (

let uu____12802 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____12802) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____12811 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____12811) with
| true -> begin
(

let guard = (

let uu____12818 = (

let uu____12819 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____12819 = FStar_Syntax_Util.Equal))
in (match (uu____12818) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____12821 -> begin
(

let uu____12822 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_73 -> FStar_Pervasives_Native.Some (_0_73)) uu____12822))
end))
in (

let uu____12824 = (solve_prob orig guard [] wl)
in (solve env uu____12824)))
end
| uu____12825 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____12826 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_constant (uu____12827), uu____12828) -> begin
(

let head1 = (

let uu____12832 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____12832 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____12863 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____12863 FStar_Pervasives_Native.fst))
in (

let uu____12891 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____12891) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____12900 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____12900) with
| true -> begin
(

let guard = (

let uu____12907 = (

let uu____12908 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____12908 = FStar_Syntax_Util.Equal))
in (match (uu____12907) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____12910 -> begin
(

let uu____12911 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_74 -> FStar_Pervasives_Native.Some (_0_74)) uu____12911))
end))
in (

let uu____12913 = (solve_prob orig guard [] wl)
in (solve env uu____12913)))
end
| uu____12914 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____12915 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____12916), uu____12917) -> begin
(

let head1 = (

let uu____12921 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____12921 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____12952 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____12952 FStar_Pervasives_Native.fst))
in (

let uu____12980 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____12980) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____12989 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____12989) with
| true -> begin
(

let guard = (

let uu____12996 = (

let uu____12997 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____12997 = FStar_Syntax_Util.Equal))
in (match (uu____12996) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____12999 -> begin
(

let uu____13000 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_75 -> FStar_Pervasives_Native.Some (_0_75)) uu____13000))
end))
in (

let uu____13002 = (solve_prob orig guard [] wl)
in (solve env uu____13002)))
end
| uu____13003 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13004 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____13005), uu____13006) -> begin
(

let head1 = (

let uu____13019 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13019 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13050 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13050 FStar_Pervasives_Native.fst))
in (

let uu____13078 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13078) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13087 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13087) with
| true -> begin
(

let guard = (

let uu____13094 = (

let uu____13095 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13095 = FStar_Syntax_Util.Equal))
in (match (uu____13094) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13097 -> begin
(

let uu____13098 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_76 -> FStar_Pervasives_Native.Some (_0_76)) uu____13098))
end))
in (

let uu____13100 = (solve_prob orig guard [] wl)
in (solve env uu____13100)))
end
| uu____13101 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13102 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____13103, FStar_Syntax_Syntax.Tm_match (uu____13104)) -> begin
(

let head1 = (

let uu____13123 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13123 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13154 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13154 FStar_Pervasives_Native.fst))
in (

let uu____13182 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13182) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13191 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13191) with
| true -> begin
(

let guard = (

let uu____13198 = (

let uu____13199 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13199 = FStar_Syntax_Util.Equal))
in (match (uu____13198) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13201 -> begin
(

let uu____13202 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_77 -> FStar_Pervasives_Native.Some (_0_77)) uu____13202))
end))
in (

let uu____13204 = (solve_prob orig guard [] wl)
in (solve env uu____13204)))
end
| uu____13205 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13206 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____13207, FStar_Syntax_Syntax.Tm_uinst (uu____13208)) -> begin
(

let head1 = (

let uu____13216 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13216 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13247 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13247 FStar_Pervasives_Native.fst))
in (

let uu____13275 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13275) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13284 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13284) with
| true -> begin
(

let guard = (

let uu____13291 = (

let uu____13292 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13292 = FStar_Syntax_Util.Equal))
in (match (uu____13291) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13294 -> begin
(

let uu____13295 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_78 -> FStar_Pervasives_Native.Some (_0_78)) uu____13295))
end))
in (

let uu____13297 = (solve_prob orig guard [] wl)
in (solve env uu____13297)))
end
| uu____13298 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13299 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____13300, FStar_Syntax_Syntax.Tm_name (uu____13301)) -> begin
(

let head1 = (

let uu____13305 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13305 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13336 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13336 FStar_Pervasives_Native.fst))
in (

let uu____13364 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13364) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13373 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13373) with
| true -> begin
(

let guard = (

let uu____13380 = (

let uu____13381 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13381 = FStar_Syntax_Util.Equal))
in (match (uu____13380) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13383 -> begin
(

let uu____13384 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_79 -> FStar_Pervasives_Native.Some (_0_79)) uu____13384))
end))
in (

let uu____13386 = (solve_prob orig guard [] wl)
in (solve env uu____13386)))
end
| uu____13387 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13388 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____13389, FStar_Syntax_Syntax.Tm_constant (uu____13390)) -> begin
(

let head1 = (

let uu____13394 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13394 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13425 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13425 FStar_Pervasives_Native.fst))
in (

let uu____13453 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13453) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13462 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13462) with
| true -> begin
(

let guard = (

let uu____13469 = (

let uu____13470 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13470 = FStar_Syntax_Util.Equal))
in (match (uu____13469) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13472 -> begin
(

let uu____13473 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_80 -> FStar_Pervasives_Native.Some (_0_80)) uu____13473))
end))
in (

let uu____13475 = (solve_prob orig guard [] wl)
in (solve env uu____13475)))
end
| uu____13476 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13477 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____13478, FStar_Syntax_Syntax.Tm_fvar (uu____13479)) -> begin
(

let head1 = (

let uu____13483 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13483 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13514 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13514 FStar_Pervasives_Native.fst))
in (

let uu____13542 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13542) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____13551 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____13551) with
| true -> begin
(

let guard = (

let uu____13558 = (

let uu____13559 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13559 = FStar_Syntax_Util.Equal))
in (match (uu____13558) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13561 -> begin
(

let uu____13562 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_81 -> FStar_Pervasives_Native.Some (_0_81)) uu____13562))
end))
in (

let uu____13564 = (solve_prob orig guard [] wl)
in (solve env uu____13564)))
end
| uu____13565 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13566 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (uu____13567, FStar_Syntax_Syntax.Tm_app (uu____13568)) -> begin
(

let head1 = (

let uu____13581 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____13581 FStar_Pervasives_Native.fst))
in (

let head2 = (

let uu____13612 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____13612 FStar_Pervasives_Native.fst))
in (

let uu____13640 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____13640) with
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

let guard = (

let uu____13656 = (

let uu____13657 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____13657 = FStar_Syntax_Util.Equal))
in (match (uu____13656) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13659 -> begin
(

let uu____13660 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_82 -> FStar_Pervasives_Native.Some (_0_82)) uu____13660))
end))
in (

let uu____13662 = (solve_prob orig guard [] wl)
in (solve env uu____13662)))
end
| uu____13663 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____13664 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t11, uu____13666, uu____13667), uu____13668) -> begin
(solve_t' env (

let uu___174_13697 = problem
in {FStar_TypeChecker_Common.pid = uu___174_13697.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___174_13697.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___174_13697.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___174_13697.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___174_13697.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___174_13697.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___174_13697.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___174_13697.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___174_13697.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____13700, FStar_Syntax_Syntax.Tm_ascribed (t21, uu____13702, uu____13703)) -> begin
(solve_t' env (

let uu___175_13732 = problem
in {FStar_TypeChecker_Common.pid = uu___175_13732.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___175_13732.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___175_13732.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___175_13732.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___175_13732.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___175_13732.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___175_13732.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___175_13732.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___175_13732.FStar_TypeChecker_Common.rank}) wl)
end
| (FStar_Syntax_Syntax.Tm_let (uu____13733), uu____13734) -> begin
(

let uu____13742 = (

let uu____13743 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____13744 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____13743 uu____13744)))
in (failwith uu____13742))
end
| (FStar_Syntax_Syntax.Tm_meta (uu____13745), uu____13746) -> begin
(

let uu____13751 = (

let uu____13752 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____13753 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____13752 uu____13753)))
in (failwith uu____13751))
end
| (FStar_Syntax_Syntax.Tm_delayed (uu____13754), uu____13755) -> begin
(

let uu____13776 = (

let uu____13777 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____13778 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____13777 uu____13778)))
in (failwith uu____13776))
end
| (uu____13779, FStar_Syntax_Syntax.Tm_meta (uu____13780)) -> begin
(

let uu____13785 = (

let uu____13786 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____13787 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____13786 uu____13787)))
in (failwith uu____13785))
end
| (uu____13788, FStar_Syntax_Syntax.Tm_delayed (uu____13789)) -> begin
(

let uu____13810 = (

let uu____13811 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____13812 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____13811 uu____13812)))
in (failwith uu____13810))
end
| (uu____13813, FStar_Syntax_Syntax.Tm_let (uu____13814)) -> begin
(

let uu____13822 = (

let uu____13823 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____13824 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____13823 uu____13824)))
in (failwith uu____13822))
end
| uu____13825 -> begin
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

let uu____13857 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____13857) with
| true -> begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end
| uu____13858 -> begin
()
end));
(

let sub_probs = (FStar_List.map2 (fun uu____13865 uu____13866 -> (match (((uu____13865), (uu____13866))) with
| ((a1, uu____13876), (a2, uu____13878)) -> begin
(

let uu____13883 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _0_83 -> FStar_TypeChecker_Common.TProb (_0_83)) uu____13883))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (

let uu____13889 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) FStar_Pervasives_Native.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____13889))
in (

let wl1 = (solve_prob orig (FStar_Pervasives_Native.Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))));
))
in (

let solve_sub = (fun c11 edge c21 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let lift_c1 = (fun uu____13909 -> (

let wp = (match (c11.FStar_Syntax_Syntax.effect_args) with
| ((wp1, uu____13916))::[] -> begin
wp1
end
| uu____13929 -> begin
(

let uu____13935 = (

let uu____13936 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c11.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" uu____13936))
in (failwith uu____13935))
end)
in (

let uu____13939 = (

let uu____13945 = (

let uu____13946 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c11.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____13946))
in (uu____13945)::[])
in {FStar_Syntax_Syntax.comp_univs = c11.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c21.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c11.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____13939; FStar_Syntax_Syntax.flags = c11.FStar_Syntax_Syntax.flags})))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____13947 = (lift_c1 ())
in (solve_eq uu____13947 c21))
end
| uu____13948 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___132_13951 -> (match (uu___132_13951) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
true
end
| uu____13952 -> begin
false
end))))
in (

let uu____13953 = (match (((c11.FStar_Syntax_Syntax.effect_args), (c21.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____13977))::uu____13978, ((wp2, uu____13980))::uu____13981) -> begin
((wp1), (wp2))
end
| uu____14022 -> begin
(

let uu____14035 = (

let uu____14036 = (

let uu____14039 = (

let uu____14040 = (FStar_Syntax_Print.lid_to_string c11.FStar_Syntax_Syntax.effect_name)
in (

let uu____14041 = (FStar_Syntax_Print.lid_to_string c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____14040 uu____14041)))
in ((uu____14039), (env.FStar_TypeChecker_Env.range)))
in FStar_Errors.Error (uu____14036))
in (FStar_Pervasives.raise uu____14035))
end)
in (match (uu____13953) with
| (wpc1, wpc2) -> begin
(

let uu____14058 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____14058) with
| true -> begin
(

let uu____14061 = (problem_using_guard orig c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ FStar_Pervasives_Native.None "result type")
in (solve_t env uu____14061 wl))
end
| uu____14064 -> begin
(

let uu____14065 = (

let uu____14069 = (FStar_TypeChecker_Env.effect_decl_opt env c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.must uu____14069))
in (match (uu____14065) with
| (c2_decl, qualifiers) -> begin
(

let uu____14081 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____14081) with
| true -> begin
(

let c1_repr = (

let uu____14084 = (

let uu____14085 = (

let uu____14086 = (lift_c1 ())
in (FStar_Syntax_Syntax.mk_Comp uu____14086))
in (

let uu____14087 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____14085 uu____14087)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____14084))
in (

let c2_repr = (

let uu____14089 = (

let uu____14090 = (FStar_Syntax_Syntax.mk_Comp c21)
in (

let uu____14091 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____14090 uu____14091)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____14089))
in (

let prob = (

let uu____14093 = (

let uu____14096 = (

let uu____14097 = (FStar_Syntax_Print.term_to_string c1_repr)
in (

let uu____14098 = (FStar_Syntax_Print.term_to_string c2_repr)
in (FStar_Util.format2 "sub effect repr: %s <: %s" uu____14097 uu____14098)))
in (sub_prob c1_repr problem.FStar_TypeChecker_Common.relation c2_repr uu____14096))
in FStar_TypeChecker_Common.TProb (uu____14093))
in (

let wl1 = (

let uu____14100 = (

let uu____14102 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in FStar_Pervasives_Native.Some (uu____14102))
in (solve_prob orig uu____14100 [] wl))
in (solve env (attempt ((prob)::[]) wl1))))))
end
| uu____14105 -> begin
(

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____14107 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____14109 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14109) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____14110 -> begin
()
end));
(

let uu____14111 = (

let uu____14114 = (

let uu____14115 = (

let uu____14125 = (

let uu____14126 = (

let uu____14127 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (uu____14127)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____14126 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (

let uu____14128 = (

let uu____14130 = (FStar_Syntax_Syntax.as_arg c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____14131 = (

let uu____14133 = (

let uu____14134 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____14134))
in (uu____14133)::[])
in (uu____14130)::uu____14131))
in ((uu____14125), (uu____14128))))
in FStar_Syntax_Syntax.Tm_app (uu____14115))
in (FStar_Syntax_Syntax.mk uu____14114))
in (uu____14111 (FStar_Pervasives_Native.Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r));
)
end
| uu____14144 -> begin
(

let uu____14145 = (

let uu____14148 = (

let uu____14149 = (

let uu____14159 = (

let uu____14160 = (

let uu____14161 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (uu____14161)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____14160 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (

let uu____14162 = (

let uu____14164 = (FStar_Syntax_Syntax.as_arg c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____14165 = (

let uu____14167 = (FStar_Syntax_Syntax.as_arg wpc2)
in (

let uu____14168 = (

let uu____14170 = (

let uu____14171 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____14171))
in (uu____14170)::[])
in (uu____14167)::uu____14168))
in (uu____14164)::uu____14165))
in ((uu____14159), (uu____14162))))
in FStar_Syntax_Syntax.Tm_app (uu____14149))
in (FStar_Syntax_Syntax.mk uu____14148))
in (uu____14145 (FStar_Pervasives_Native.Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r))
end)
end)
in (

let base_prob = (

let uu____14182 = (sub_prob c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _0_84 -> FStar_TypeChecker_Common.TProb (_0_84)) uu____14182))
in (

let wl1 = (

let uu____14188 = (

let uu____14190 = (

let uu____14193 = (FStar_All.pipe_right (p_guard base_prob) FStar_Pervasives_Native.fst)
in (FStar_Syntax_Util.mk_conj uu____14193 g))
in (FStar_All.pipe_left (fun _0_85 -> FStar_Pervasives_Native.Some (_0_85)) uu____14190))
in (solve_prob orig uu____14188 [] wl))
in (solve env (attempt ((base_prob)::[]) wl1)))))
end))
end))
end))
end)))
end))))
in (

let uu____14203 = (FStar_Util.physical_equality c1 c2)
in (match (uu____14203) with
| true -> begin
(

let uu____14204 = (solve_prob orig FStar_Pervasives_Native.None [] wl)
in (solve env uu____14204))
end
| uu____14205 -> begin
((

let uu____14207 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14207) with
| true -> begin
(

let uu____14208 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____14209 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____14208 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____14209)))
end
| uu____14210 -> begin
()
end));
(

let uu____14211 = (

let uu____14214 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____14215 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____14214), (uu____14215))))
in (match (uu____14211) with
| (c11, c21) -> begin
(match (((c11.FStar_Syntax_Syntax.n), (c21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____14219), FStar_Syntax_Syntax.Total (t2, uu____14221)) when (FStar_Syntax_Util.non_informative t2) -> begin
(

let uu____14234 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____14234 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____14237), FStar_Syntax_Syntax.Total (uu____14238)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| (FStar_Syntax_Syntax.Total (t1, uu____14250), FStar_Syntax_Syntax.Total (t2, uu____14252)) -> begin
(

let uu____14265 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____14265 wl))
end
| (FStar_Syntax_Syntax.GTotal (t1, uu____14269), FStar_Syntax_Syntax.GTotal (t2, uu____14271)) -> begin
(

let uu____14284 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____14284 wl))
end
| (FStar_Syntax_Syntax.Total (t1, uu____14288), FStar_Syntax_Syntax.GTotal (t2, uu____14290)) -> begin
(

let uu____14303 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 FStar_Pervasives_Native.None "result type")
in (solve_t env uu____14303 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____14306), FStar_Syntax_Syntax.Comp (uu____14307)) -> begin
(

let uu____14313 = (

let uu___176_14316 = problem
in (

let uu____14319 = (

let uu____14320 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____14320))
in {FStar_TypeChecker_Common.pid = uu___176_14316.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____14319; FStar_TypeChecker_Common.relation = uu___176_14316.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___176_14316.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___176_14316.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___176_14316.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___176_14316.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___176_14316.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___176_14316.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___176_14316.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____14313 wl))
end
| (FStar_Syntax_Syntax.Total (uu____14321), FStar_Syntax_Syntax.Comp (uu____14322)) -> begin
(

let uu____14328 = (

let uu___176_14331 = problem
in (

let uu____14334 = (

let uu____14335 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____14335))
in {FStar_TypeChecker_Common.pid = uu___176_14331.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____14334; FStar_TypeChecker_Common.relation = uu___176_14331.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___176_14331.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___176_14331.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___176_14331.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___176_14331.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___176_14331.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___176_14331.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___176_14331.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____14328 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____14336), FStar_Syntax_Syntax.GTotal (uu____14337)) -> begin
(

let uu____14343 = (

let uu___177_14346 = problem
in (

let uu____14349 = (

let uu____14350 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____14350))
in {FStar_TypeChecker_Common.pid = uu___177_14346.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___177_14346.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___177_14346.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____14349; FStar_TypeChecker_Common.element = uu___177_14346.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___177_14346.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___177_14346.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___177_14346.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___177_14346.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___177_14346.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____14343 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____14351), FStar_Syntax_Syntax.Total (uu____14352)) -> begin
(

let uu____14358 = (

let uu___177_14361 = problem
in (

let uu____14364 = (

let uu____14365 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____14365))
in {FStar_TypeChecker_Common.pid = uu___177_14361.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___177_14361.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___177_14361.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____14364; FStar_TypeChecker_Common.element = uu___177_14361.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___177_14361.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___177_14361.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___177_14361.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___177_14361.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___177_14361.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____14358 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____14366), FStar_Syntax_Syntax.Comp (uu____14367)) -> begin
(

let uu____14368 = (((FStar_Syntax_Util.is_ml_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) || ((FStar_Syntax_Util.is_total_comp c11) && ((FStar_Syntax_Util.is_total_comp c21) || (FStar_Syntax_Util.is_ml_comp c21))))
in (match (uu____14368) with
| true -> begin
(

let uu____14369 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c11) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c21) FStar_Pervasives_Native.None "result type")
in (solve_t env uu____14369 wl))
end
| uu____14372 -> begin
(

let c1_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (

let c2_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (match (((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name))) with
| true -> begin
(solve_eq c1_comp c2_comp)
end
| uu____14375 -> begin
(

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((

let uu____14379 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14379) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c12.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c22.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____14380 -> begin
()
end));
(

let uu____14381 = (FStar_TypeChecker_Env.monad_leq env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____14381) with
| FStar_Pervasives_Native.None -> begin
(

let uu____14383 = (((FStar_Syntax_Util.is_ghost_effect c12.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c22.FStar_Syntax_Syntax.effect_name)) && (

let uu____14384 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c22.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative uu____14384)))
in (match (uu____14383) with
| true -> begin
(

let edge = {FStar_TypeChecker_Env.msource = c12.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c22.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = FStar_TypeChecker_Env.identity_mlift}
in (solve_sub c12 edge c22))
end
| uu____14386 -> begin
(

let uu____14387 = (

let uu____14388 = (FStar_Syntax_Print.lid_to_string c12.FStar_Syntax_Syntax.effect_name)
in (

let uu____14389 = (FStar_Syntax_Print.lid_to_string c22.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____14388 uu____14389)))
in (giveup env uu____14387 orig))
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

let uu____14394 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____14414 -> (match (uu____14414) with
| (uu____14425, uu____14426, u, uu____14428, uu____14429, uu____14430) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____14394 (FStar_String.concat ", "))))


let ineqs_to_string : (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.string = (fun ineqs -> (

let vars = (

let uu____14459 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs) (FStar_List.map FStar_Syntax_Print.univ_to_string))
in (FStar_All.pipe_right uu____14459 (FStar_String.concat ", ")))
in (

let ineqs1 = (

let uu____14469 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs) (FStar_List.map (fun uu____14481 -> (match (uu____14481) with
| (u1, u2) -> begin
(

let uu____14486 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____14487 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "%s < %s" uu____14486 uu____14487)))
end))))
in (FStar_All.pipe_right uu____14469 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred), (g.FStar_TypeChecker_Env.univ_ineqs))) with
| (FStar_TypeChecker_Common.Trivial, [], (uu____14499, [])) -> begin
"{}"
end
| uu____14512 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____14522 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____14522) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____14523 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____14525 = (FStar_List.map (fun uu____14529 -> (match (uu____14529) with
| (uu____14532, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right uu____14525 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (

let uu____14536 = (ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs)
in (FStar_Util.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n" form carry uu____14536 imps)))))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = (

let uu____14574 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____14574) with
| true -> begin
(

let uu____14575 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____14576 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14575 (rel_to_string rel) uu____14576)))
end
| uu____14577 -> begin
"TOP"
end))
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (

let uu____14596 = (

let uu____14598 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_86 -> FStar_Pervasives_Native.Some (_0_86)) uu____14598))
in (FStar_Syntax_Syntax.new_bv uu____14596 t1))
in (

let env1 = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (

let uu____14604 = (

let uu____14606 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _0_87 -> FStar_Pervasives_Native.Some (_0_87)) uu____14606))
in (

let uu____14608 = (FStar_TypeChecker_Env.get_range env1)
in (new_t_problem env1 t1 rel t2 uu____14604 uu____14608)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option = (fun env probs err1 -> (

let probs1 = (

let uu____14631 = (FStar_Options.eager_inference ())
in (match (uu____14631) with
| true -> begin
(

let uu___178_14632 = probs
in {attempting = uu___178_14632.attempting; wl_deferred = uu___178_14632.wl_deferred; ctr = uu___178_14632.ctr; defer_ok = false; smt_ok = uu___178_14632.smt_ok; tcenv = uu___178_14632.tcenv})
end
| uu____14633 -> begin
probs
end))
in (

let tx = (FStar_Unionfind.new_transaction ())
in (

let sol = (solve env probs1)
in (match (sol) with
| Success (deferred) -> begin
((FStar_Unionfind.commit tx);
FStar_Pervasives_Native.Some (deferred);
)
end
| Failed (d, s) -> begin
((FStar_Unionfind.rollback tx);
(

let uu____14643 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____14643) with
| true -> begin
(

let uu____14644 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____14644))
end
| uu____14645 -> begin
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

let uu____14654 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____14654) with
| true -> begin
(

let uu____14655 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____14655))
end
| uu____14656 -> begin
()
end));
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in ((

let uu____14659 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____14659) with
| true -> begin
(

let uu____14660 = (FStar_Syntax_Print.term_to_string f1)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____14660))
end
| uu____14661 -> begin
()
end));
(

let f2 = (

let uu____14663 = (

let uu____14664 = (FStar_Syntax_Util.unmeta f1)
in uu____14664.FStar_Syntax_Syntax.n)
in (match (uu____14663) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____14668 -> begin
FStar_TypeChecker_Common.NonTrivial (f1)
end))
in (

let uu___179_14669 = g
in {FStar_TypeChecker_Env.guard_f = f2; FStar_TypeChecker_Env.deferred = uu___179_14669.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___179_14669.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___179_14669.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____14684 = (

let uu____14685 = (

let uu____14686 = (

let uu____14687 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____14687 (fun _0_88 -> FStar_TypeChecker_Common.NonTrivial (_0_88))))
in {FStar_TypeChecker_Env.guard_f = uu____14686; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env uu____14685))
in (FStar_All.pipe_left (fun _0_89 -> FStar_Pervasives_Native.Some (_0_89)) uu____14684))
end))


let with_guard_no_simp = (fun env prob dopt -> (match (dopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (d) -> begin
(

let uu____14720 = (

let uu____14721 = (

let uu____14722 = (FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____14722 (fun _0_90 -> FStar_TypeChecker_Common.NonTrivial (_0_90))))
in {FStar_TypeChecker_Env.guard_f = uu____14721; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in FStar_Pervasives_Native.Some (uu____14720))
end))


let try_teq : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun smt_ok env t1 t2 -> ((

let uu____14748 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14748) with
| true -> begin
(

let uu____14749 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____14750 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" uu____14749 uu____14750)))
end
| uu____14751 -> begin
()
end));
(

let prob = (

let uu____14753 = (

let uu____14756 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None uu____14756))
in (FStar_All.pipe_left (fun _0_91 -> FStar_TypeChecker_Common.TProb (_0_91)) uu____14753))
in (

let g = (

let uu____14761 = (

let uu____14763 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____14763 (fun uu____14764 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____14761))
in g));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____14778 = (try_teq true env t1 t2)
in (match (uu____14778) with
| FStar_Pervasives_Native.None -> begin
(

let uu____14780 = (

let uu____14781 = (

let uu____14784 = (FStar_TypeChecker_Err.basic_type_error env FStar_Pervasives_Native.None t2 t1)
in (

let uu____14785 = (FStar_TypeChecker_Env.get_range env)
in ((uu____14784), (uu____14785))))
in FStar_Errors.Error (uu____14781))
in (FStar_Pervasives.raise uu____14780))
end
| FStar_Pervasives_Native.Some (g) -> begin
((

let uu____14788 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14788) with
| true -> begin
(

let uu____14789 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____14790 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____14791 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____14789 uu____14790 uu____14791))))
end
| uu____14792 -> begin
()
end));
g;
)
end)))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 smt_ok -> ((

let uu____14807 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14807) with
| true -> begin
(

let uu____14808 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____14809 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" uu____14808 uu____14809)))
end
| uu____14810 -> begin
()
end));
(

let uu____14811 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____14811) with
| (prob, x) -> begin
(

let g = (

let uu____14819 = (

let uu____14821 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____14821 (fun uu____14822 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____14819))
in ((

let uu____14828 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____14828) with
| true -> begin
(

let uu____14829 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____14830 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____14831 = (

let uu____14832 = (FStar_Util.must g)
in (guard_to_string env uu____14832))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" uu____14829 uu____14830 uu____14831))))
end
| uu____14833 -> begin
()
end));
(abstract_guard x g);
))
end));
))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env e t1 t2 -> (

let uu____14856 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____14857 = (FStar_TypeChecker_Err.basic_type_error env (FStar_Pervasives_Native.Some (e)) t2 t1)
in (FStar_Errors.err uu____14856 uu____14857))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun env c1 c2 -> ((

let uu____14869 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____14869) with
| true -> begin
(

let uu____14870 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____14871 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" uu____14870 uu____14871)))
end
| uu____14872 -> begin
()
end));
(

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____14874 -> begin
FStar_TypeChecker_Common.SUB
end)
in (

let prob = (

let uu____14876 = (

let uu____14879 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 FStar_Pervasives_Native.None uu____14879 "sub_comp"))
in (FStar_All.pipe_left (fun _0_92 -> FStar_TypeChecker_Common.CProb (_0_92)) uu____14876))
in (

let uu____14882 = (

let uu____14884 = (singleton env prob)
in (solve_and_commit env uu____14884 (fun uu____14885 -> FStar_Pervasives_Native.None)))
in (FStar_All.pipe_left (with_guard env prob) uu____14882))));
))


let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun tx env uu____14904 -> (match (uu____14904) with
| (variables, ineqs) -> begin
(

let fail = (fun u1 u2 -> ((FStar_Unionfind.rollback tx);
(

let uu____14929 = (

let uu____14930 = (

let uu____14933 = (

let uu____14934 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____14935 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Universe %s and %s are incompatible" uu____14934 uu____14935)))
in (

let uu____14936 = (FStar_TypeChecker_Env.get_range env)
in ((uu____14933), (uu____14936))))
in FStar_Errors.Error (uu____14930))
in (FStar_Pervasives.raise uu____14929));
))
in (

let equiv = (fun v1 v' -> (

let uu____14944 = (

let uu____14947 = (FStar_Syntax_Subst.compress_univ v1)
in (

let uu____14948 = (FStar_Syntax_Subst.compress_univ v')
in ((uu____14947), (uu____14948))))
in (match (uu____14944) with
| (FStar_Syntax_Syntax.U_unif (v0), FStar_Syntax_Syntax.U_unif (v0')) -> begin
(FStar_Unionfind.equivalent v0 v0')
end
| uu____14956 -> begin
false
end)))
in (

let sols = (FStar_All.pipe_right variables (FStar_List.collect (fun v1 -> (

let uu____14970 = (FStar_Syntax_Subst.compress_univ v1)
in (match (uu____14970) with
| FStar_Syntax_Syntax.U_unif (uu____14974) -> begin
(

let lower_bounds_of_v = (FStar_All.pipe_right ineqs (FStar_List.collect (fun uu____14985 -> (match (uu____14985) with
| (u, v') -> begin
(

let uu____14991 = (equiv v1 v')
in (match (uu____14991) with
| true -> begin
(

let uu____14993 = (FStar_All.pipe_right variables (FStar_Util.for_some (equiv u)))
in (match (uu____14993) with
| true -> begin
[]
end
| uu____14996 -> begin
(u)::[]
end))
end
| uu____14997 -> begin
[]
end))
end))))
in (

let lb = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max (lower_bounds_of_v)))
in (((lb), (v1)))::[]))
end
| uu____15003 -> begin
[]
end)))))
in (

let uu____15006 = (

let wl = (

let uu___180_15009 = (empty_worklist env)
in {attempting = uu___180_15009.attempting; wl_deferred = uu___180_15009.wl_deferred; ctr = uu___180_15009.ctr; defer_ok = false; smt_ok = uu___180_15009.smt_ok; tcenv = uu___180_15009.tcenv})
in (FStar_All.pipe_right sols (FStar_List.map (fun uu____15016 -> (match (uu____15016) with
| (lb, v1) -> begin
(

let uu____15021 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl lb v1)
in (match (uu____15021) with
| USolved (wl1) -> begin
()
end
| uu____15023 -> begin
(fail lb v1)
end))
end)))))
in (

let rec check_ineq = (fun uu____15029 -> (match (uu____15029) with
| (u, v1) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u)
in (

let v2 = (FStar_TypeChecker_Normalize.normalize_universe env v1)
in (match (((u1), (v2))) with
| (FStar_Syntax_Syntax.U_zero, uu____15036) -> begin
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
| (FStar_Syntax_Syntax.U_name (uu____15048), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_unif (uu____15050), FStar_Syntax_Syntax.U_succ (v0)) -> begin
(check_ineq ((u1), (v0)))
end
| (FStar_Syntax_Syntax.U_max (us), uu____15055) -> begin
(FStar_All.pipe_right us (FStar_Util.for_all (fun u2 -> (check_ineq ((u2), (v2))))))
end
| (uu____15059, FStar_Syntax_Syntax.U_max (vs)) -> begin
(FStar_All.pipe_right vs (FStar_Util.for_some (fun v3 -> (check_ineq ((u1), (v3))))))
end
| uu____15064 -> begin
false
end)))
end))
in (

let uu____15067 = (FStar_All.pipe_right ineqs (FStar_Util.for_all (fun uu____15073 -> (match (uu____15073) with
| (u, v1) -> begin
(

let uu____15078 = (check_ineq ((u), (v1)))
in (match (uu____15078) with
| true -> begin
true
end
| uu____15079 -> begin
((

let uu____15081 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____15081) with
| true -> begin
(

let uu____15082 = (FStar_Syntax_Print.univ_to_string u)
in (

let uu____15083 = (FStar_Syntax_Print.univ_to_string v1)
in (FStar_Util.print2 "%s </= %s" uu____15082 uu____15083)))
end
| uu____15084 -> begin
()
end));
false;
)
end))
end))))
in (match (uu____15067) with
| true -> begin
()
end
| uu____15085 -> begin
((

let uu____15087 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____15087) with
| true -> begin
((

let uu____15089 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Partially solved inequality constraints are: %s\n" uu____15089));
(FStar_Unionfind.rollback tx);
(

let uu____15095 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Original solved inequality constraints are: %s\n" uu____15095));
)
end
| uu____15100 -> begin
()
end));
(

let uu____15101 = (

let uu____15102 = (

let uu____15105 = (FStar_TypeChecker_Env.get_range env)
in (("Failed to solve universe inequalities for inductives"), (uu____15105)))
in FStar_Errors.Error (uu____15102))
in (FStar_Pervasives.raise uu____15101));
)
end)))))))
end))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun env ineqs -> (

let tx = (FStar_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Unionfind.commit tx);
)))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail = (fun uu____15138 -> (match (uu____15138) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (FStar_Pervasives.raise (FStar_Errors.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in ((

let uu____15148 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____15148) with
| true -> begin
(

let uu____15149 = (wl_to_string wl)
in (

let uu____15150 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" uu____15149 uu____15150)))
end
| uu____15160 -> begin
()
end));
(

let g1 = (

let uu____15162 = (solve_and_commit env wl fail)
in (match (uu____15162) with
| FStar_Pervasives_Native.Some ([]) -> begin
(

let uu___181_15169 = g
in {FStar_TypeChecker_Env.guard_f = uu___181_15169.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu___181_15169.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___181_15169.FStar_TypeChecker_Env.implicits})
end
| uu____15172 -> begin
(failwith "impossible: Unexpected deferred constraints remain")
end))
in ((solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___182_15175 = g1
in {FStar_TypeChecker_Env.guard_f = uu___182_15175.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___182_15175.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = uu___182_15175.FStar_TypeChecker_Env.implicits});
));
))))


let discharge_guard' : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option = (fun use_env_range_msg env g use_smt -> (

let g1 = (solve_deferred_constraints env g)
in (

let ret_g = (

let uu___183_15201 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___183_15201.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___183_15201.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___183_15201.FStar_TypeChecker_Env.implicits})
in (

let uu____15202 = (

let uu____15203 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____15203)))
in (match (uu____15202) with
| true -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| uu____15205 -> begin
(match (g1.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((

let uu____15209 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Norm"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____15209) with
| true -> begin
(

let uu____15210 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____15211 = (

let uu____15212 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____15212))
in (FStar_Errors.diag uu____15210 uu____15211)))
end
| uu____15213 -> begin
()
end));
(

let vc1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc1)) with
| FStar_TypeChecker_Common.Trivial -> begin
FStar_Pervasives_Native.Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc2) -> begin
(match ((not (use_smt))) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____15218 -> begin
((

let uu____15221 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____15221) with
| true -> begin
(

let uu____15222 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____15223 = (

let uu____15224 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____15224))
in (FStar_Errors.diag uu____15222 uu____15223)))
end
| uu____15225 -> begin
()
end));
(

let vcs = (

let uu____15230 = (FStar_Options.use_tactics ())
in (match (uu____15230) with
| true -> begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.preprocess env vc2)
end
| uu____15234 -> begin
(((env), (vc2)))::[]
end))
in (FStar_All.pipe_right vcs (FStar_List.iter (fun uu____15244 -> (match (uu____15244) with
| (env1, goal) -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env1 goal)
end)))));
FStar_Pervasives_Native.Some (ret_g);
)
end)
end));
)
end)
end)))))


let discharge_guard_no_smt : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let uu____15255 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____15255) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____15260 = (

let uu____15261 = (

let uu____15264 = (FStar_TypeChecker_Env.get_range env)
in (("Expected a trivial pre-condition"), (uu____15264)))
in FStar_Errors.Error (uu____15261))
in (FStar_Pervasives.raise uu____15260))
end)))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let uu____15271 = (discharge_guard' FStar_Pervasives_Native.None env g true)
in (match (uu____15271) with
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end)))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (

let uu____15291 = (FStar_Unionfind.find u)
in (match (uu____15291) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| uu____15300 -> begin
false
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____15315 = acc
in (match (uu____15315) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____15326 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd1)::tl1 -> begin
(

let uu____15361 = hd1
in (match (uu____15361) with
| (uu____15368, env, u, tm, k, r) -> begin
(

let uu____15374 = (unresolved u)
in (match (uu____15374) with
| true -> begin
(until_fixpoint (((hd1)::out), (changed)) tl1)
end
| uu____15388 -> begin
(

let env1 = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 tm)
in ((

let uu____15392 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("RelCheck")))
in (match (uu____15392) with
| true -> begin
(

let uu____15393 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____15397 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____15398 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" uu____15393 uu____15397 uu____15398))))
end
| uu____15399 -> begin
()
end));
(

let uu____15400 = (env1.FStar_TypeChecker_Env.type_of (

let uu___184_15404 = env1
in {FStar_TypeChecker_Env.solver = uu___184_15404.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___184_15404.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___184_15404.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___184_15404.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___184_15404.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___184_15404.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___184_15404.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___184_15404.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___184_15404.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___184_15404.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___184_15404.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___184_15404.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___184_15404.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___184_15404.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___184_15404.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___184_15404.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___184_15404.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___184_15404.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___184_15404.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___184_15404.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___184_15404.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___184_15404.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___184_15404.FStar_TypeChecker_Env.qname_and_index}) tm1)
in (match (uu____15400) with
| (uu____15405, uu____15406, g1) -> begin
(

let g2 = (match (env1.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___185_15409 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___185_15409.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___185_15409.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___185_15409.FStar_TypeChecker_Env.implicits})
end
| uu____15410 -> begin
g1
end)
in (

let g' = (

let uu____15412 = (discharge_guard' (FStar_Pervasives_Native.Some ((fun uu____15416 -> (FStar_Syntax_Print.term_to_string tm1)))) env1 g2 true)
in (match (uu____15412) with
| FStar_Pervasives_Native.Some (g3) -> begin
g3
end
| FStar_Pervasives_Native.None -> begin
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

let uu___186_15431 = g
in (

let uu____15432 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___186_15431.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___186_15431.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___186_15431.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____15432})))))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g1 = (

let uu____15460 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____15460 resolve_implicits))
in (match (g1.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(

let uu____15467 = (discharge_guard env g1)
in (FStar_All.pipe_left FStar_Pervasives.ignore uu____15467))
end
| ((reason, uu____15469, uu____15470, e, t, r))::uu____15474 -> begin
(

let uu____15488 = (

let uu____15489 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____15490 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Failed to resolve implicit argument of type \'%s\' introduced in %s" uu____15489 uu____15490)))
in (FStar_Errors.err r uu____15488))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___187_15497 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___187_15497.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___187_15497.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ((((u1), (u2)))::[])); FStar_TypeChecker_Env.implicits = uu___187_15497.FStar_TypeChecker_Env.implicits}))


let teq_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____15515 = (try_teq false env t1 t2)
in (match (uu____15515) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (g) -> begin
(

let uu____15518 = (discharge_guard' FStar_Pervasives_Native.None env g false)
in (match (uu____15518) with
| FStar_Pervasives_Native.Some (uu____15522) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end))
end)))





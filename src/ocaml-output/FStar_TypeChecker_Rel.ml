
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

let uu___130_64 = g1
in (

let uu____65 = (

let uu____66 = (

let uu____67 = (

let uu____71 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____71)::[])
in (

let uu____72 = (

let uu____79 = (

let uu____85 = (

let uu____86 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____86 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____85 (fun _0_28 -> FStar_Util.Inl (_0_28))))
in Some (uu____79))
in (FStar_Syntax_Util.abs uu____67 f uu____72)))
in (FStar_All.pipe_left (fun _0_29 -> FStar_TypeChecker_Common.NonTrivial (_0_29)) uu____66))
in {FStar_TypeChecker_Env.guard_f = uu____65; FStar_TypeChecker_Env.deferred = uu___130_64.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___130_64.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___130_64.FStar_TypeChecker_Env.implicits}))
in Some (uu____63)))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___131_107 = g
in (

let uu____108 = (

let uu____109 = (

let uu____110 = (

let uu____113 = (

let uu____114 = (

let uu____124 = (

let uu____126 = (FStar_Syntax_Syntax.as_arg e)
in (uu____126)::[])
in ((f), (uu____124)))
in FStar_Syntax_Syntax.Tm_app (uu____114))
in (FStar_Syntax_Syntax.mk uu____113))
in (uu____110 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _0_30 -> FStar_TypeChecker_Common.NonTrivial (_0_30)) uu____109))
in {FStar_TypeChecker_Env.guard_f = uu____108; FStar_TypeChecker_Env.deferred = uu___131_107.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___131_107.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___131_107.FStar_TypeChecker_Env.implicits}))
end))


let map_guard : FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  FStar_TypeChecker_Env.guard_t = (fun g map1 -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___132_148 = g
in (

let uu____149 = (

let uu____150 = (map1 f)
in FStar_TypeChecker_Common.NonTrivial (uu____150))
in {FStar_TypeChecker_Env.guard_f = uu____149; FStar_TypeChecker_Env.deferred = uu___132_148.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___132_148.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___132_148.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____154) -> begin
(failwith "impossible")
end))


let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let uu____164 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (uu____164))
end))


let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____173 -> begin
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

let uu____204 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = uu____204; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (((FStar_List.append (Prims.fst g1.FStar_TypeChecker_Env.univ_ineqs) (Prims.fst g2.FStar_TypeChecker_Env.univ_ineqs))), ((FStar_List.append (Prims.snd g1.FStar_TypeChecker_Env.univ_ineqs) (Prims.snd g2.FStar_TypeChecker_Env.univ_ineqs)))); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard_univs : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun us bs g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let f1 = (FStar_List.fold_right2 (fun u b f1 -> (

let uu____249 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____249) with
| true -> begin
f1
end
| uu____250 -> begin
(FStar_Syntax_Util.mk_forall u (Prims.fst b) f1)
end))) us bs f)
in (

let uu___133_251 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.NonTrivial (f1); FStar_TypeChecker_Env.deferred = uu___133_251.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___133_251.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___133_251.FStar_TypeChecker_Env.implicits}))
end))


let close_forall : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____265 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____265) with
| true -> begin
f1
end
| uu____266 -> begin
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

let uu___134_278 = g
in (

let uu____279 = (

let uu____280 = (close_forall env binders f)
in FStar_TypeChecker_Common.NonTrivial (uu____280))
in {FStar_TypeChecker_Env.guard_f = uu____279; FStar_TypeChecker_Env.deferred = uu___134_278.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___134_278.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___134_278.FStar_TypeChecker_Env.implicits}))
end))


let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (

let uv = (FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(

let uv1 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k))))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((uv1), (uv1)))
end
| uu____325 -> begin
(

let args = (FStar_All.pipe_right binders (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder))
in (

let k' = (

let uu____340 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders uu____340))
in (

let uv1 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k'))))) None r)
in (

let uu____360 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((uv1), (args))))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((uu____360), (uv1))))))
end)))


let mk_eq2 : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t1 t2 -> (

let uu____393 = (FStar_Syntax_Util.type_u ())
in (match (uu____393) with
| (t_type, u) -> begin
(

let uu____398 = (

let uu____401 = (FStar_TypeChecker_Env.all_binders env)
in (new_uvar t1.FStar_Syntax_Syntax.pos uu____401 t_type))
in (match (uu____398) with
| (tt, uu____403) -> begin
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
| uu____424 -> begin
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
| uu____450 -> begin
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
| uu____530 -> begin
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
| uu____544 -> begin
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
| uu____561 -> begin
false
end))


let uu___is_CONTRAVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CONTRAVARIANT -> begin
true
end
| uu____565 -> begin
false
end))


let uu___is_INVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| INVARIANT -> begin
true
end
| uu____569 -> begin
false
end))


type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem


type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem


type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun uu___102_580 -> (match (uu___102_580) with
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

let uu____593 = (

let uu____594 = (FStar_Syntax_Subst.compress t)
in uu____594.FStar_Syntax_Syntax.n)
in (match (uu____593) with
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let uu____611 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____615 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s:%s)" uu____611 uu____615)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty); FStar_Syntax_Syntax.tk = uu____618; FStar_Syntax_Syntax.pos = uu____619; FStar_Syntax_Syntax.vars = uu____620}, args) -> begin
(

let uu____648 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____652 = (FStar_Syntax_Print.term_to_string ty)
in (

let uu____653 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "(%s:%s) %s" uu____648 uu____652 uu____653))))
end
| uu____654 -> begin
(FStar_Syntax_Print.term_to_string t)
end)))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env uu___103_660 -> (match (uu___103_660) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____664 = (

let uu____666 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____667 = (

let uu____669 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____670 = (

let uu____672 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (

let uu____673 = (

let uu____675 = (

let uu____677 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (

let uu____678 = (

let uu____680 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (

let uu____681 = (

let uu____683 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (

let uu____684 = (

let uu____686 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (uu____686)::[])
in (uu____683)::uu____684))
in (uu____680)::uu____681))
in (uu____677)::uu____678))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::uu____675)
in (uu____672)::uu____673))
in (uu____669)::uu____670))
in (uu____666)::uu____667))
in (FStar_Util.format "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" uu____664))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____691 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____692 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____691 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____692)))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env uu___104_698 -> (match (uu___104_698) with
| UNIV (u, t) -> begin
(

let x = (

let uu____702 = (FStar_Options.hide_uvar_nums ())
in (match (uu____702) with
| true -> begin
"?"
end
| uu____703 -> begin
(

let uu____704 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____704 FStar_Util.string_of_int))
end))
in (

let uu____706 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x uu____706)))
end
| TERM ((u, uu____708), t) -> begin
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

let uu____719 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x uu____719)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (

let uu____728 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right uu____728 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (

let uu____736 = (

let uu____738 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right uu____738 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right uu____736 (FStar_String.concat ", "))))


let args_to_string = (fun args -> (

let uu____756 = (FStar_All.pipe_right args (FStar_List.map (fun uu____764 -> (match (uu____764) with
| (x, uu____768) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____756 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> (

let uu____773 = (

let uu____774 = (FStar_Options.eager_inference ())
in (not (uu____774)))
in {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = uu____773; smt_ok = true; tcenv = env}))


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let uu___135_787 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = uu___135_787.wl_deferred; ctr = uu___135_787.ctr; defer_ok = uu___135_787.defer_ok; smt_ok = smt_ok; tcenv = uu___135_787.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard = (fun env g -> (

let uu___136_812 = (empty_worklist env)
in (

let uu____813 = (FStar_List.map Prims.snd g)
in {attempting = uu____813; wl_deferred = uu___136_812.wl_deferred; ctr = uu___136_812.ctr; defer_ok = false; smt_ok = uu___136_812.smt_ok; tcenv = uu___136_812.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu___137_825 = wl
in {attempting = uu___137_825.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = uu___137_825.ctr; defer_ok = uu___137_825.defer_ok; smt_ok = uu___137_825.smt_ok; tcenv = uu___137_825.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let uu___138_837 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = uu___138_837.wl_deferred; ctr = uu___138_837.ctr; defer_ok = uu___138_837.defer_ok; smt_ok = uu___138_837.smt_ok; tcenv = uu___138_837.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> ((

let uu____848 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____848) with
| true -> begin
(

let uu____849 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason uu____849))
end
| uu____850 -> begin
()
end));
Failed (((prob), (reason)));
))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun uu___105_853 -> (match (uu___105_853) with
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

let uu___139_869 = p
in {FStar_TypeChecker_Common.pid = uu___139_869.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = uu___139_869.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___139_869.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___139_869.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___139_869.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___139_869.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___139_869.FStar_TypeChecker_Common.rank}))


let maybe_invert = (fun p -> (match ((p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV)) with
| true -> begin
(invert p)
end
| uu____887 -> begin
p
end))


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___106_890 -> (match (uu___106_890) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_31 -> FStar_TypeChecker_Common.TProb (_0_31)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_32 -> FStar_TypeChecker_Common.CProb (_0_32)))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel uu___107_906 -> (match (uu___107_906) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun uu___108_909 -> (match (uu___108_909) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun uu___109_918 -> (match (uu___109_918) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun uu___110_928 -> (match (uu___110_928) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun uu___111_938 -> (match (uu___111_938) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun uu___112_949 -> (match (uu___112_949) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun uu___113_960 -> (match (uu___113_960) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___114_969 -> (match (uu___114_969) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _0_33 -> FStar_TypeChecker_Common.TProb (_0_33)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _0_34 -> FStar_TypeChecker_Common.CProb (_0_34)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> (

let uu____983 = (FStar_All.pipe_right (p_reason p) FStar_List.length)
in (uu____983 = (Prims.parse_int "1"))))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____994 -> ((FStar_Util.incr ctr);
(FStar_ST.read ctr);
)))


let mk_problem = (fun scope orig lhs rel rhs elt reason -> (

let uu____1044 = (next_pid ())
in (

let uu____1045 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____1044; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____1045; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))


let new_problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (

let uu____1092 = (next_pid ())
in (

let uu____1093 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____1092; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____1093; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (

let uu____1134 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____1134; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))


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

let uu____1186 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____1186) with
| true -> begin
(

let uu____1187 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (

let uu____1188 = (prob_to_string env d)
in (

let uu____1189 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" uu____1187 uu____1188 uu____1189 s))))
end
| uu____1191 -> begin
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
| uu____1194 -> begin
(failwith "impossible")
end)
in (

let uu____1195 = (match (d1) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____1203 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (

let uu____1204 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((uu____1203), (uu____1204))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____1208 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (

let uu____1209 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((uu____1208), (uu____1209))))
end)
in (match (uu____1195) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___115_1218 -> (match (uu___115_1218) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| uu____1225 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, uu____1228), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun uu___116_1251 -> (match (uu___116_1251) with
| UNIV (uu____1253) -> begin
None
end
| TERM ((u, uu____1257), t) -> begin
(

let uu____1261 = (FStar_Unionfind.equivalent uv u)
in (match (uu____1261) with
| true -> begin
Some (t)
end
| uu____1266 -> begin
None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun uu___117_1280 -> (match (uu___117_1280) with
| UNIV (u', t) -> begin
(

let uu____1284 = (FStar_Unionfind.equivalent u u')
in (match (uu____1284) with
| true -> begin
Some (t)
end
| uu____1287 -> begin
None
end))
end
| uu____1288 -> begin
None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1295 = (

let uu____1296 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____1296))
in (FStar_Syntax_Subst.compress uu____1295)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1303 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress uu____1303)))


let norm_arg = (fun env t -> (

let uu____1322 = (sn env (Prims.fst t))
in ((uu____1322), ((Prims.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____1339 -> (match (uu____1339) with
| (x, imp) -> begin
(

let uu____1346 = (

let uu___140_1347 = x
in (

let uu____1348 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___140_1347.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___140_1347.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1348}))
in ((uu____1346), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____1363 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____1363))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1366 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____1366))
end
| uu____1368 -> begin
u2
end)))
in (

let uu____1369 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1369))))


let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement = (fun env wl t1 -> (

let rec aux = (fun norm t11 -> (match (t11.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(match (norm) with
| true -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| uu____1475 -> begin
(

let uu____1476 = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (match (uu____1476) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x1, phi1); FStar_Syntax_Syntax.tk = uu____1488; FStar_Syntax_Syntax.pos = uu____1489; FStar_Syntax_Syntax.vars = uu____1490} -> begin
((x1.FStar_Syntax_Syntax.sort), (Some (((x1), (phi1)))))
end
| tt -> begin
(

let uu____1511 = (

let uu____1512 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____1513 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1512 uu____1513)))
in (failwith uu____1511))
end))
end)
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(match (norm) with
| true -> begin
((t11), (None))
end
| uu____1546 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in (

let uu____1548 = (

let uu____1549 = (FStar_Syntax_Subst.compress t1')
in uu____1549.FStar_Syntax_Syntax.n)
in (match (uu____1548) with
| FStar_Syntax_Syntax.Tm_refine (uu____1561) -> begin
(aux true t1')
end
| uu____1566 -> begin
((t11), (None))
end)))
end)
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
((t11), (None))
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(

let uu____1601 = (

let uu____1602 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____1603 = (FStar_Syntax_Print.tag_of_term t11)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1602 uu____1603)))
in (failwith uu____1601))
end))
in (

let uu____1613 = (whnf env t1)
in (aux false uu____1613))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____1622 = (

let uu____1632 = (empty_worklist env)
in (base_and_refinement env uu____1632 t))
in (FStar_All.pipe_right uu____1622 Prims.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (

let uu____1656 = (FStar_Syntax_Syntax.null_bv t)
in ((uu____1656), (FStar_Syntax_Util.t_true))))


let as_refinement = (fun env wl t -> (

let uu____1676 = (base_and_refinement env wl t)
in (match (uu____1676) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement = (fun uu____1735 -> (match (uu____1735) with
| (t_base, refopt) -> begin
(

let uu____1749 = (match (refopt) with
| Some (y, phi) -> begin
((y), (phi))
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (uu____1749) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl uu___118_1773 -> (match (uu___118_1773) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____1777 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1778 = (

let uu____1779 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string uu____1779))
in (

let uu____1780 = (

let uu____1781 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string uu____1781))
in (FStar_Util.format4 "%s: %s  (%s)  %s" uu____1777 uu____1778 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1780))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____1785 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1786 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____1787 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" uu____1785 uu____1786 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1787))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (

let uu____1791 = (

let uu____1793 = (

let uu____1795 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____1805 -> (match (uu____1805) with
| (uu____1809, uu____1810, x) -> begin
x
end))))
in (FStar_List.append wl.attempting uu____1795))
in (FStar_List.map (wl_prob_to_string wl) uu____1793))
in (FStar_All.pipe_right uu____1791 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____1828 = (

let uu____1838 = (

let uu____1839 = (FStar_Syntax_Subst.compress k)
in uu____1839.FStar_Syntax_Syntax.n)
in (match (uu____1838) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (((FStar_List.length bs) = (FStar_List.length ys))) with
| true -> begin
(

let uu____1880 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (uu____1880)))
end
| uu____1893 -> begin
(

let uu____1894 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____1894) with
| (ys', t1, uu____1915) -> begin
(

let uu____1928 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t1))), (uu____1928)))
end))
end)
end
| uu____1949 -> begin
(

let uu____1950 = (

let uu____1956 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____1956)))
in ((((ys), (t))), (uu____1950)))
end))
in (match (uu____1828) with
| ((ys1, t1), (xs, c)) -> begin
(match (((FStar_List.length xs) <> (FStar_List.length ys1))) with
| true -> begin
(FStar_Syntax_Util.abs ys1 t1 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ([]))))))
end
| uu____2009 -> begin
(

let c1 = (

let uu____2011 = (FStar_Syntax_Util.rename_binders xs ys1)
in (FStar_Syntax_Subst.subst_comp uu____2011 c))
in (

let uu____2013 = (

let uu____2020 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1) (fun _0_35 -> FStar_Util.Inl (_0_35)))
in (FStar_All.pipe_right uu____2020 (fun _0_36 -> Some (_0_36))))
in (FStar_Syntax_Util.abs ys1 t1 uu____2013)))
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

let uu____2071 = (p_guard prob)
in (match (uu____2071) with
| (uu____2074, uv) -> begin
((

let uu____2077 = (

let uu____2078 = (FStar_Syntax_Subst.compress uv)
in uu____2078.FStar_Syntax_Syntax.n)
in (match (uu____2077) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi1 = (u_abs k bs phi)
in ((

let uu____2098 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____2098) with
| true -> begin
(

let uu____2099 = (FStar_Util.string_of_int (p_pid prob))
in (

let uu____2100 = (FStar_Syntax_Print.term_to_string uv)
in (

let uu____2101 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" uu____2099 uu____2100 uu____2101))))
end
| uu____2102 -> begin
()
end));
(FStar_Syntax_Util.set_uvar uvar phi1);
)))
end
| uu____2105 -> begin
(match ((not (resolve_ok))) with
| true -> begin
(failwith "Impossible: this instance has already been assigned a solution")
end
| uu____2106 -> begin
()
end)
end));
(commit uvis);
(

let uu___141_2108 = wl
in {attempting = uu___141_2108.attempting; wl_deferred = uu___141_2108.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___141_2108.defer_ok; smt_ok = uu___141_2108.smt_ok; tcenv = uu___141_2108.tcenv});
)
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____2121 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____2121) with
| true -> begin
(

let uu____2122 = (FStar_Util.string_of_int pid)
in (

let uu____2123 = (

let uu____2124 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right uu____2124 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____2122 uu____2123)))
end
| uu____2127 -> begin
()
end));
(commit sol);
(

let uu___142_2129 = wl
in {attempting = uu___142_2129.attempting; wl_deferred = uu___142_2129.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___142_2129.defer_ok; smt_ok = uu___142_2129.smt_ok; tcenv = uu___142_2129.tcenv});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard1 = (fun t g -> (match (((t), (g))) with
| (uu____2158, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t1), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(

let uu____2166 = (FStar_Syntax_Util.mk_conj t1 f)
in Some (uu____2166))
end))
in ((

let uu____2172 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____2172) with
| true -> begin
(

let uu____2173 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (

let uu____2174 = (

let uu____2175 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right uu____2175 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____2173 uu____2174)))
end
| uu____2178 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
)))


let rec occurs = (fun wl uk t -> (

let uu____2200 = (

let uu____2204 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right uu____2204 FStar_Util.set_elements))
in (FStar_All.pipe_right uu____2200 (FStar_Util.for_some (fun uu____2225 -> (match (uu____2225) with
| (uv, uu____2233) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (

let uu____2277 = (occurs wl uk t)
in (not (uu____2277)))
in (

let msg = (match (occurs_ok) with
| true -> begin
None
end
| uu____2281 -> begin
(

let uu____2282 = (

let uu____2283 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (

let uu____2287 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" uu____2283 uu____2287)))
in Some (uu____2282))
end)
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let uu____2335 = (occurs_check env wl uk t)
in (match (uu____2335) with
| (occurs_ok, msg) -> begin
(

let uu____2352 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (uu____2352), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set = (fun v3 -> (FStar_All.pipe_right v3 (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set v1)
in (

let uu____2416 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____2440 uu____2441 -> (match (((uu____2440), (uu____2441))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____2484 = (

let uu____2485 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation uu____2485))
in (match (uu____2484) with
| true -> begin
((isect), (isect_set))
end
| uu____2496 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____2499 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____2499) with
| true -> begin
(

let uu____2506 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (uu____2506)))
end
| uu____2514 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (uu____2416) with
| (isect, uu____2528) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____2577 uu____2578 -> (match (((uu____2577), (uu____2578))) with
| ((a, uu____2588), (b, uu____2590)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd1 = (norm_arg env arg)
in (match ((Prims.fst hd1).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(

let uu____2634 = (FStar_All.pipe_right seen (FStar_Util.for_some (fun uu____2640 -> (match (uu____2640) with
| (b, uu____2644) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end))))
in (match (uu____2634) with
| true -> begin
None
end
| uu____2650 -> begin
Some (((a), ((Prims.snd hd1))))
end))
end
| uu____2653 -> begin
None
end)))


let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| (hd1)::rest -> begin
(

let uu____2696 = (pat_var_opt env seen hd1)
in (match (uu____2696) with
| None -> begin
((

let uu____2704 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____2704) with
| true -> begin
(

let uu____2705 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd1))
in (FStar_Util.print1 "Not a pattern: %s\n" uu____2705))
end
| uu____2706 -> begin
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

let uu____2717 = (

let uu____2718 = (FStar_Syntax_Subst.compress t)
in uu____2718.FStar_Syntax_Syntax.n)
in (match (uu____2717) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
true
end
| uu____2734 -> begin
false
end)))


let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = uu____2796; FStar_Syntax_Syntax.pos = uu____2797; FStar_Syntax_Syntax.vars = uu____2798}, args) -> begin
((t), (uv), (k), (args))
end
| uu____2839 -> begin
(failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let uu____2893 = (destruct_flex_t t)
in (match (uu____2893) with
| (t1, uv, k, args) -> begin
(

let uu____2961 = (pat_vars env [] args)
in (match (uu____2961) with
| Some (vars) -> begin
((((t1), (uv), (k), (args))), (Some (vars)))
end
| uu____3017 -> begin
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
| uu____3065 -> begin
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
| uu____3088 -> begin
false
end))


let uu___is_FullMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullMatch -> begin
true
end
| uu____3092 -> begin
false
end))


let head_match : match_result  ->  match_result = (fun uu___119_3095 -> (match (uu___119_3095) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____3104 -> begin
HeadMatch
end))


let fv_delta_depth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.delta_depth = (fun env fv -> (match (fv.FStar_Syntax_Syntax.fv_delta) with
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(match ((env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)) with
| true -> begin
d
end
| uu____3116 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
end
| FStar_Syntax_Syntax.Delta_defined_at_level (uu____3117) -> begin
(

let uu____3118 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3118) with
| None -> begin
FStar_Syntax_Syntax.Delta_constant
end
| uu____3128 -> begin
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

let uu____3196 = (fv_delta_depth env fv)
in Some (uu____3196))
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
| uu____3210 -> begin
MisMatch (((None), (None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____3215 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____3215) with
| true -> begin
FullMatch
end
| uu____3216 -> begin
(

let uu____3217 = (

let uu____3222 = (

let uu____3224 = (fv_delta_depth env f)
in Some (uu____3224))
in (

let uu____3225 = (

let uu____3227 = (fv_delta_depth env g)
in Some (uu____3227))
in ((uu____3222), (uu____3225))))
in MisMatch (uu____3217))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____3231), FStar_Syntax_Syntax.Tm_uinst (g, uu____3233)) -> begin
(

let uu____3242 = (head_matches env f g)
in (FStar_All.pipe_right uu____3242 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(match ((c = d)) with
| true -> begin
FullMatch
end
| uu____3245 -> begin
MisMatch (((None), (None)))
end)
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, uu____3249), FStar_Syntax_Syntax.Tm_uvar (uv', uu____3251)) -> begin
(

let uu____3276 = (FStar_Unionfind.equivalent uv uv')
in (match (uu____3276) with
| true -> begin
FullMatch
end
| uu____3280 -> begin
MisMatch (((None), (None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____3284), FStar_Syntax_Syntax.Tm_refine (y, uu____3286)) -> begin
(

let uu____3295 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____3295 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____3297), uu____3298) -> begin
(

let uu____3303 = (head_matches env x.FStar_Syntax_Syntax.sort t21)
in (FStar_All.pipe_right uu____3303 head_match))
end
| (uu____3304, FStar_Syntax_Syntax.Tm_refine (x, uu____3306)) -> begin
(

let uu____3311 = (head_matches env t11 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____3311 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____3317), FStar_Syntax_Syntax.Tm_app (head', uu____3319)) -> begin
(

let uu____3348 = (head_matches env head1 head')
in (FStar_All.pipe_right uu____3348 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head1, uu____3350), uu____3351) -> begin
(

let uu____3366 = (head_matches env head1 t21)
in (FStar_All.pipe_right uu____3366 head_match))
end
| (uu____3367, FStar_Syntax_Syntax.Tm_app (head1, uu____3369)) -> begin
(

let uu____3384 = (head_matches env t11 head1)
in (FStar_All.pipe_right uu____3384 head_match))
end
| uu____3385 -> begin
(

let uu____3388 = (

let uu____3393 = (delta_depth_of_term env t11)
in (

let uu____3395 = (delta_depth_of_term env t21)
in ((uu____3393), (uu____3395))))
in MisMatch (uu____3388))
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let uu____3431 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____3431) with
| (head1, uu____3443) -> begin
(

let uu____3458 = (

let uu____3459 = (FStar_Syntax_Util.un_uinst head1)
in uu____3459.FStar_Syntax_Syntax.n)
in (match (uu____3458) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3464 = (

let uu____3465 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3465 FStar_Option.isSome))
in (match (uu____3464) with
| true -> begin
(

let uu____3479 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right uu____3479 (fun _0_37 -> Some (_0_37))))
end
| uu____3481 -> begin
None
end))
end
| uu____3482 -> begin
None
end))
end)))
in (

let success = (fun d r t11 t21 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
Some (((t11), (t21)))
end
| uu____3509 -> begin
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
| uu____3561 -> begin
(

let uu____3562 = (

let uu____3567 = (maybe_inline t11)
in (

let uu____3569 = (maybe_inline t21)
in ((uu____3567), (uu____3569))))
in (match (uu____3562) with
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

let uu____3594 = (FStar_TypeChecker_Common.decr_delta_depth d1)
in (match (uu____3594) with
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

let uu____3609 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t11)
in ((t1'), (t21)))
end
| uu____3615 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t21)
in (

let uu____3617 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t21)
in ((t11), (uu____3617))))
end)
in (match (uu____3609) with
| (t12, t22) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
end)))
end
| MisMatch (uu____3625) -> begin
(fail r)
end
| uu____3630 -> begin
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
| uu____3655 -> begin
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
| uu____3685 -> begin
false
end))


let __proj__C__item___0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_0) -> begin
_0
end))


type tcs =
tc Prims.list


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____3700 = (FStar_Syntax_Util.type_u ())
in (match (uu____3700) with
| (t, uu____3704) -> begin
(

let uu____3705 = (new_uvar r binders t)
in (Prims.fst uu____3705))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____3714 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____3714 Prims.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (

let uu____3756 = (head_matches env t1 t')
in (match (uu____3756) with
| MisMatch (uu____3757) -> begin
false
end
| uu____3762 -> begin
true
end)))
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let rebuild = (fun args' -> (

let args1 = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((uu____3822, imp), T (t2, uu____3825)) -> begin
((t2), (imp))
end
| uu____3842 -> begin
(failwith "Bad reconstruction")
end)) args args')
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd1), (args1))))) None t1.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun uu____3886 -> (match (uu____3886) with
| (t2, uu____3894) -> begin
((None), (INVARIANT), (T (((t2), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let fail = (fun uu____3927 -> (failwith "Bad reconstruction"))
in (

let uu____3928 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3928) with
| (bs1, c1) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs2 tcs1 -> (match (((bs2), (tcs1))) with
| (((x, imp))::bs3, (T (t2, uu____3981))::tcs2) -> begin
(aux (((((

let uu___143_4003 = x
in {FStar_Syntax_Syntax.ppname = uu___143_4003.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___143_4003.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2})), (imp)))::out) bs3 tcs2)
end
| ([], (C (c2))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c2)
end
| uu____4013 -> begin
(failwith "Bad reconstruction")
end))
in (aux [] bs1 tcs)))
in (

let rec decompose1 = (fun out uu___120_4044 -> (match (uu___120_4044) with
| [] -> begin
(FStar_List.rev ((((None), (COVARIANT), (C (c1))))::out))
end
| (hd1)::rest -> begin
(decompose1 ((((Some (hd1)), (CONTRAVARIANT), (T ((((Prims.fst hd1).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (

let uu____4107 = (decompose1 [] bs1)
in ((rebuild), (matches), (uu____4107)))))
end)))
end
| uu____4135 -> begin
(

let rebuild = (fun uu___121_4140 -> (match (uu___121_4140) with
| [] -> begin
t1
end
| uu____4142 -> begin
(failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t2 -> true)), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun uu___122_4161 -> (match (uu___122_4161) with
| T (t, uu____4163) -> begin
t
end
| uu____4172 -> begin
(failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun uu___123_4175 -> (match (uu___123_4175) with
| T (t, uu____4177) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| uu____4186 -> begin
(failwith "Impossible")
end))


let imitation_sub_probs : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list  ->  (FStar_TypeChecker_Common.prob Prims.list * tc Prims.list * FStar_Syntax_Syntax.formula) = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope1 args q -> (match (q) with
| (uu____4255, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope1 r)
in (

let uu____4274 = (new_uvar r scope1 k)
in (match (uu____4274) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| uu____4286 -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args))))) None r)
end)
in (

let uu____4305 = (

let uu____4306 = (mk_problem scope1 orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _0_38 -> FStar_TypeChecker_Common.TProb (_0_38)) uu____4306))
in ((T (((gi_xs), (mk_kind)))), (uu____4305))))
end)))
end
| (uu____4315, uu____4316, C (uu____4317)) -> begin
(failwith "impos")
end))
in (

let rec aux = (fun scope1 args qs1 -> (match (qs1) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs2 -> begin
(

let uu____4404 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.tk = uu____4415; FStar_Syntax_Syntax.pos = uu____4416; FStar_Syntax_Syntax.vars = uu____4417})) -> begin
(

let uu____4432 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____4432) with
| (T (gi_xs, uu____4448), prob) -> begin
(

let uu____4458 = (

let uu____4459 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_39 -> C (_0_39)) uu____4459))
in ((uu____4458), ((prob)::[])))
end
| uu____4461 -> begin
(failwith "impossible")
end))
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.tk = uu____4471; FStar_Syntax_Syntax.pos = uu____4472; FStar_Syntax_Syntax.vars = uu____4473})) -> begin
(

let uu____4488 = (sub_prob scope1 args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____4488) with
| (T (gi_xs, uu____4504), prob) -> begin
(

let uu____4514 = (

let uu____4515 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_40 -> C (_0_40)) uu____4515))
in ((uu____4514), ((prob)::[])))
end
| uu____4517 -> begin
(failwith "impossible")
end))
end
| (uu____4523, uu____4524, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = uu____4526; FStar_Syntax_Syntax.pos = uu____4527; FStar_Syntax_Syntax.vars = uu____4528})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((None), (INVARIANT), (T ((((Prims.fst t)), (generic_kind))))))))
in (

let components1 = (((None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let uu____4602 = (

let uu____4607 = (FStar_List.map (sub_prob scope1 args) components1)
in (FStar_All.pipe_right uu____4607 FStar_List.unzip))
in (match (uu____4602) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (

let uu____4636 = (

let uu____4637 = (

let uu____4640 = (FStar_List.hd tcs)
in (FStar_All.pipe_right uu____4640 un_T))
in (

let uu____4641 = (

let uu____4647 = (FStar_List.tl tcs)
in (FStar_All.pipe_right uu____4647 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____4637; FStar_Syntax_Syntax.effect_args = uu____4641; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____4636))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| uu____4652 -> begin
(

let uu____4659 = (sub_prob scope1 args q)
in (match (uu____4659) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (uu____4404) with
| (tc, probs) -> begin
(

let uu____4677 = (match (q) with
| (Some (b), uu____4703, uu____4704) -> begin
(

let uu____4712 = (

let uu____4716 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (uu____4716)::args)
in ((Some (b)), ((b)::scope1), (uu____4712)))
end
| uu____4734 -> begin
((None), (scope1), (args))
end)
in (match (uu____4677) with
| (bopt, scope2, args1) -> begin
(

let uu____4777 = (aux scope2 args1 qs2)
in (match (uu____4777) with
| (sub_probs, tcs, f) -> begin
(

let f1 = (match (bopt) with
| None -> begin
(

let uu____4798 = (

let uu____4800 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::uu____4800)
in (FStar_Syntax_Util.mk_conj_l uu____4798))
end
| Some (b) -> begin
(

let u_b = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst b).FStar_Syntax_Syntax.sort)
in (

let uu____4813 = (

let uu____4815 = (FStar_Syntax_Util.mk_forall u_b (Prims.fst b) f)
in (

let uu____4816 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (uu____4815)::uu____4816))
in (FStar_Syntax_Util.mk_conj_l uu____4813)))
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

let uu___144_4869 = p
in (

let uu____4872 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____4873 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___144_4869.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____4872; FStar_TypeChecker_Common.relation = uu___144_4869.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____4873; FStar_TypeChecker_Common.element = uu___144_4869.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___144_4869.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___144_4869.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___144_4869.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___144_4869.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___144_4869.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p1) -> begin
(

let uu____4883 = (compress_tprob wl p1)
in (FStar_All.pipe_right uu____4883 (fun _0_41 -> FStar_TypeChecker_Common.TProb (_0_41))))
end
| FStar_TypeChecker_Common.CProb (uu____4888) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (

let uu____4902 = (compress_prob wl pr)
in (FStar_All.pipe_right uu____4902 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____4908 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____4908) with
| (lh, uu____4921) -> begin
(

let uu____4936 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____4936) with
| (rh, uu____4949) -> begin
(

let uu____4964 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____4973), FStar_Syntax_Syntax.Tm_uvar (uu____4974)) -> begin
((flex_flex), (tp))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when ((tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____4999), uu____5000) -> begin
(

let uu____5009 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (uu____5009) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((flex_rigid), (tp))
end
| uu____5049 -> begin
(

let rank = (

let uu____5056 = (is_top_level_prob prob)
in (match (uu____5056) with
| true -> begin
flex_refine
end
| uu____5057 -> begin
flex_refine_inner
end))
in (

let uu____5058 = (

let uu___145_5061 = tp
in (

let uu____5064 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___145_5061.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___145_5061.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___145_5061.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____5064; FStar_TypeChecker_Common.element = uu___145_5061.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___145_5061.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___145_5061.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___145_5061.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___145_5061.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___145_5061.FStar_TypeChecker_Common.rank}))
in ((rank), (uu____5058))))
end)
end))
end
| (uu____5074, FStar_Syntax_Syntax.Tm_uvar (uu____5075)) -> begin
(

let uu____5084 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (uu____5084) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((rigid_flex), (tp))
end
| uu____5124 -> begin
(

let uu____5130 = (

let uu___146_5135 = tp
in (

let uu____5138 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___146_5135.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____5138; FStar_TypeChecker_Common.relation = uu___146_5135.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___146_5135.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___146_5135.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___146_5135.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___146_5135.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___146_5135.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___146_5135.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___146_5135.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (uu____5130)))
end)
end))
end
| (uu____5154, uu____5155) -> begin
((rigid_rigid), (tp))
end)
in (match (uu____4964) with
| (rank, tp1) -> begin
(

let uu____5166 = (FStar_All.pipe_right (

let uu___147_5169 = tp1
in {FStar_TypeChecker_Common.pid = uu___147_5169.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___147_5169.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___147_5169.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___147_5169.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___147_5169.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___147_5169.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___147_5169.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___147_5169.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___147_5169.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _0_42 -> FStar_TypeChecker_Common.TProb (_0_42)))
in ((rank), (uu____5166)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____5175 = (FStar_All.pipe_right (

let uu___148_5178 = cp
in {FStar_TypeChecker_Common.pid = uu___148_5178.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___148_5178.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___148_5178.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___148_5178.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___148_5178.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___148_5178.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___148_5178.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___148_5178.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___148_5178.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _0_43 -> FStar_TypeChecker_Common.CProb (_0_43)))
in ((rigid_rigid), (uu____5175)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun uu____5210 probs -> (match (uu____5210) with
| (min_rank, min1, out) -> begin
(match (probs) with
| [] -> begin
((min1), (out), (min_rank))
end
| (hd1)::tl1 -> begin
(

let uu____5240 = (rank wl hd1)
in (match (uu____5240) with
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
| uu____5265 -> begin
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
| uu____5281 -> begin
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
| uu____5305 -> begin
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
| uu____5317 -> begin
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
| uu____5329 -> begin
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

let uu____5366 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____5366) with
| (k, uu____5370) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| uu____5375 -> begin
false
end)
end)))))
end
| uu____5376 -> begin
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

let uu____5419 = (really_solve_universe_eq pid_orig wl1 u13 u23)
in (match (uu____5419) with
| USolved (wl2) -> begin
(aux wl2 us12 us22)
end
| failed -> begin
failed
end))
end
| uu____5422 -> begin
USolved (wl1)
end))
in (aux wl us1 us2))
end
| uu____5427 -> begin
(

let uu____5428 = (

let uu____5429 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____5430 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" uu____5429 uu____5430)))
in UFailed (uu____5428))
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

let uu____5447 = (really_solve_universe_eq pid_orig wl1 u u')
in (match (uu____5447) with
| USolved (wl2) -> begin
(aux wl2 us2)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____5450 -> begin
(

let uu____5453 = (

let uu____5454 = (FStar_Syntax_Print.univ_to_string u12)
in (

let uu____5455 = (FStar_Syntax_Print.univ_to_string u22)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" uu____5454 uu____5455 msg)))
in UFailed (uu____5453))
end))
in (match (((u11), (u21))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(

let uu____5462 = (

let uu____5463 = (FStar_Syntax_Print.univ_to_string u11)
in (

let uu____5464 = (FStar_Syntax_Print.univ_to_string u21)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____5463 uu____5464)))
in (failwith uu____5462))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((x.FStar_Ident.idText = y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____5467 -> begin
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

let uu____5476 = (FStar_Unionfind.equivalent v1 v2)
in (match (uu____5476) with
| true -> begin
USolved (wl)
end
| uu____5478 -> begin
(

let wl1 = (extend_solution pid_orig ((UNIV (((v1), (u21))))::[]) wl)
in USolved (wl1))
end))
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(

let u3 = (norm_univ wl u)
in (

let uu____5489 = (occurs_univ v1 u3)
in (match (uu____5489) with
| true -> begin
(

let uu____5490 = (

let uu____5491 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____5492 = (FStar_Syntax_Print.univ_to_string u3)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____5491 uu____5492)))
in (try_umax_components u11 u21 uu____5490))
end
| uu____5493 -> begin
(

let uu____5494 = (extend_solution pid_orig ((UNIV (((v1), (u3))))::[]) wl)
in USolved (uu____5494))
end)))
end
| ((FStar_Syntax_Syntax.U_max (_), _)) | ((_, FStar_Syntax_Syntax.U_max (_))) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____5501 -> begin
(

let u12 = (norm_univ wl u11)
in (

let u22 = (norm_univ wl u21)
in (

let uu____5504 = (FStar_Syntax_Util.eq_univs u12 u22)
in (match (uu____5504) with
| true -> begin
USolved (wl)
end
| uu____5505 -> begin
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
| uu____5526 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders = (fun bc1 bc2 -> (

let uu____5575 = bc1
in (match (uu____5575) with
| (bs1, mk_cod1) -> begin
(

let uu____5600 = bc2
in (match (uu____5600) with
| (bs2, mk_cod2) -> begin
(

let curry = (fun n1 bs mk_cod -> (

let uu____5647 = (FStar_Util.first_N n1 bs)
in (match (uu____5647) with
| (bs3, rest) -> begin
(

let uu____5661 = (mk_cod rest)
in ((bs3), (uu____5661)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(

let uu____5679 = (

let uu____5683 = (mk_cod1 [])
in ((bs1), (uu____5683)))
in (

let uu____5685 = (

let uu____5689 = (mk_cod2 [])
in ((bs2), (uu____5689)))
in ((uu____5679), (uu____5685))))
end
| uu____5697 -> begin
(match ((l1 > l2)) with
| true -> begin
(

let uu____5711 = (curry l2 bs1 mk_cod1)
in (

let uu____5718 = (

let uu____5722 = (mk_cod2 [])
in ((bs2), (uu____5722)))
in ((uu____5711), (uu____5718))))
end
| uu____5730 -> begin
(

let uu____5731 = (

let uu____5735 = (mk_cod1 [])
in ((bs1), (uu____5735)))
in (

let uu____5737 = (curry l1 bs2 mk_cod2)
in ((uu____5731), (uu____5737))))
end)
end))))
end))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____5841 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5841) with
| true -> begin
(

let uu____5842 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" uu____5842))
end
| uu____5843 -> begin
()
end));
(

let uu____5844 = (next_prob probs)
in (match (uu____5844) with
| (Some (hd1), tl1, rank1) -> begin
(

let probs1 = (

let uu___149_5857 = probs
in {attempting = tl1; wl_deferred = uu___149_5857.wl_deferred; ctr = uu___149_5857.ctr; defer_ok = uu___149_5857.defer_ok; smt_ok = uu___149_5857.smt_ok; tcenv = uu___149_5857.tcenv})
in (match (hd1) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs1)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match ((((not (probs1.defer_ok)) && (flex_refine_inner <= rank1)) && (rank1 <= flex_rigid))) with
| true -> begin
(

let uu____5864 = (solve_flex_rigid_join env tp probs1)
in (match (uu____5864) with
| None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| Some (wl) -> begin
(solve env wl)
end))
end
| uu____5867 -> begin
(match ((((not (probs1.defer_ok)) && (rigid_flex <= rank1)) && (rank1 <= refine_flex))) with
| true -> begin
(

let uu____5868 = (solve_rigid_flex_meet env tp probs1)
in (match (uu____5868) with
| None -> begin
(solve_t' env (maybe_invert tp) probs1)
end
| Some (wl) -> begin
(solve env wl)
end))
end
| uu____5871 -> begin
(solve_t' env (maybe_invert tp) probs1)
end)
end)
end))
end
| (None, uu____5872, uu____5873) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| uu____5882 -> begin
(

let uu____5887 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____5915 -> (match (uu____5915) with
| (c, uu____5920, uu____5921) -> begin
(c < probs.ctr)
end))))
in (match (uu____5887) with
| (attempt1, rest) -> begin
(match (attempt1) with
| [] -> begin
(

let uu____5943 = (FStar_List.map (fun uu____5949 -> (match (uu____5949) with
| (uu____5955, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (uu____5943))
end
| uu____5958 -> begin
(

let uu____5963 = (

let uu___150_5964 = probs
in (

let uu____5965 = (FStar_All.pipe_right attempt1 (FStar_List.map (fun uu____5974 -> (match (uu____5974) with
| (uu____5978, uu____5979, y) -> begin
y
end))))
in {attempting = uu____5965; wl_deferred = rest; ctr = uu___150_5964.ctr; defer_ok = uu___150_5964.defer_ok; smt_ok = uu___150_5964.smt_ok; tcenv = uu___150_5964.tcenv}))
in (solve env uu____5963))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____5986 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____5986) with
| USolved (wl1) -> begin
(

let uu____5988 = (solve_prob orig None [] wl1)
in (solve env uu____5988))
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

let uu____6022 = (solve_universe_eq (p_pid orig) wl1 u1 u2)
in (match (uu____6022) with
| USolved (wl2) -> begin
(aux wl2 us11 us21)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____6025 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t11 = (whnf env t1)
in (

let t21 = (whnf env t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = uu____6033; FStar_Syntax_Syntax.pos = uu____6034; FStar_Syntax_Syntax.vars = uu____6035}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = uu____6038; FStar_Syntax_Syntax.pos = uu____6039; FStar_Syntax_Syntax.vars = uu____6040}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____6056 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____6064 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6064) with
| true -> begin
(

let uu____6065 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" uu____6065 msg))
end
| uu____6066 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____6067 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> ((

let uu____6073 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6073) with
| true -> begin
(

let uu____6074 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" uu____6074))
end
| uu____6075 -> begin
()
end));
(

let uu____6076 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____6076) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let uu____6118 = (head_matches_delta env () t1 t2)
in (match (uu____6118) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (uu____6140) -> begin
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

let uu____6166 = (match (ts) with
| Some (t11, t21) -> begin
(

let uu____6175 = (FStar_Syntax_Subst.compress t11)
in (

let uu____6176 = (FStar_Syntax_Subst.compress t21)
in ((uu____6175), (uu____6176))))
end
| None -> begin
(

let uu____6179 = (FStar_Syntax_Subst.compress t1)
in (

let uu____6180 = (FStar_Syntax_Subst.compress t2)
in ((uu____6179), (uu____6180))))
end)
in (match (uu____6166) with
| (t11, t21) -> begin
(

let eq_prob = (fun t12 t22 -> (

let uu____6202 = (new_problem env t12 FStar_TypeChecker_Common.EQ t22 None t12.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _0_44 -> FStar_TypeChecker_Common.TProb (_0_44)) uu____6202)))
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(

let uu____6225 = (

let uu____6231 = (

let uu____6234 = (

let uu____6237 = (

let uu____6238 = (

let uu____6243 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (uu____6243)))
in FStar_Syntax_Syntax.Tm_refine (uu____6238))
in (FStar_Syntax_Syntax.mk uu____6237))
in (uu____6234 None t11.FStar_Syntax_Syntax.pos))
in (

let uu____6256 = (

let uu____6258 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (uu____6258)::[])
in ((uu____6231), (uu____6256))))
in Some (uu____6225))
end
| (uu____6267, FStar_Syntax_Syntax.Tm_refine (x, uu____6269)) -> begin
(

let uu____6274 = (

let uu____6278 = (

let uu____6280 = (eq_prob x.FStar_Syntax_Syntax.sort t11)
in (uu____6280)::[])
in ((t11), (uu____6278)))
in Some (uu____6274))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____6286), uu____6287) -> begin
(

let uu____6292 = (

let uu____6296 = (

let uu____6298 = (eq_prob x.FStar_Syntax_Syntax.sort t21)
in (uu____6298)::[])
in ((t21), (uu____6296)))
in Some (uu____6292))
end
| uu____6303 -> begin
(

let uu____6306 = (FStar_Syntax_Util.head_and_args t11)
in (match (uu____6306) with
| (head1, uu____6321) -> begin
(

let uu____6336 = (

let uu____6337 = (FStar_Syntax_Util.un_uinst head1)
in uu____6337.FStar_Syntax_Syntax.n)
in (match (uu____6336) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____6344; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (i); FStar_Syntax_Syntax.fv_qual = uu____6346}) -> begin
(

let prev = (match ((i > (Prims.parse_int "1"))) with
| true -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i - (Prims.parse_int "1")))
end
| uu____6352 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
in (

let t12 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t11)
in (

let t22 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t21)
in (disjoin t12 t22))))
end
| uu____6355 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____6364) -> begin
(

let uu____6377 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___124_6386 -> (match (uu___124_6386) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| Some (rank1) when (is_rigid_flex rank1) -> begin
(

let uu____6391 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.rhs)
in (match (uu____6391) with
| (u', uu____6402) -> begin
(

let uu____6417 = (

let uu____6418 = (whnf env u')
in uu____6418.FStar_Syntax_Syntax.n)
in (match (uu____6417) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____6422) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____6438 -> begin
false
end))
end))
end
| uu____6439 -> begin
false
end)
end
| uu____6441 -> begin
false
end))))
in (match (uu____6377) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun uu____6462 tps -> (match (uu____6462) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____6489 = (

let uu____6494 = (whnf env hd1.FStar_TypeChecker_Common.lhs)
in (disjoin bound uu____6494))
in (match (uu____6489) with
| Some (bound1, sub1) -> begin
(make_lower_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| None -> begin
None
end))
end
| uu____6513 -> begin
None
end)
end))
in (

let uu____6518 = (

let uu____6523 = (

let uu____6527 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((uu____6527), ([])))
in (make_lower_bound uu____6523 lower_bounds))
in (match (uu____6518) with
| None -> begin
((

let uu____6534 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6534) with
| true -> begin
(FStar_Util.print_string "No lower bounds\n")
end
| uu____6535 -> begin
()
end));
None;
)
end
| Some (lhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in ((

let uu____6547 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6547) with
| true -> begin
(

let wl' = (

let uu___151_6549 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___151_6549.wl_deferred; ctr = uu___151_6549.ctr; defer_ok = uu___151_6549.defer_ok; smt_ok = uu___151_6549.smt_ok; tcenv = uu___151_6549.tcenv})
in (

let uu____6550 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" uu____6550)))
end
| uu____6551 -> begin
()
end));
(

let uu____6552 = (solve_t env eq_prob (

let uu___152_6553 = wl
in {attempting = sub_probs; wl_deferred = uu___152_6553.wl_deferred; ctr = uu___152_6553.ctr; defer_ok = uu___152_6553.defer_ok; smt_ok = uu___152_6553.smt_ok; tcenv = uu___152_6553.tcenv}))
in (match (uu____6552) with
| Success (uu____6555) -> begin
(

let wl1 = (

let uu___153_6557 = wl
in {attempting = rest; wl_deferred = uu___153_6557.wl_deferred; ctr = uu___153_6557.ctr; defer_ok = uu___153_6557.defer_ok; smt_ok = uu___153_6557.smt_ok; tcenv = uu___153_6557.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl1)
in (

let uu____6559 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p None [] wl3)) wl2 lower_bounds)
in Some (wl2))))
end
| uu____6562 -> begin
None
end));
))
end)))
end))
end
| uu____6563 -> begin
(failwith "Impossible: Not a rigid-flex")
end)))
end));
))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> ((

let uu____6570 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6570) with
| true -> begin
(

let uu____6571 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" uu____6571))
end
| uu____6572 -> begin
()
end));
(

let uu____6573 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____6573) with
| (u, args) -> begin
(

let uu____6600 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (uu____6600) with
| (ok, head_match1, partial_match, fallback, failed_match) -> begin
(

let max1 = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____6619 -> begin
i
end))
in (

let base_types_match = (fun t1 t2 -> (

let uu____6631 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____6631) with
| (h1, args1) -> begin
(

let uu____6659 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____6659) with
| (h2, uu____6672) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
(

let uu____6691 = (FStar_Syntax_Syntax.fv_eq tc1 tc2)
in (match (uu____6691) with
| true -> begin
(match (((FStar_List.length args1) = (Prims.parse_int "0"))) with
| true -> begin
Some ([])
end
| uu____6703 -> begin
(

let uu____6704 = (

let uu____6706 = (

let uu____6707 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_45 -> FStar_TypeChecker_Common.TProb (_0_45)) uu____6707))
in (uu____6706)::[])
in Some (uu____6704))
end)
end
| uu____6713 -> begin
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
| uu____6728 -> begin
(

let uu____6729 = (

let uu____6731 = (

let uu____6732 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_46 -> FStar_TypeChecker_Common.TProb (_0_46)) uu____6732))
in (uu____6731)::[])
in Some (uu____6729))
end)
end
| uu____6738 -> begin
None
end)
end
| uu____6740 -> begin
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

let uu____6806 = (

let uu____6812 = (

let uu____6815 = (FStar_Syntax_Util.mk_conj phi11 phi21)
in (FStar_Syntax_Util.refine x1 uu____6815))
in ((uu____6812), (m1)))
in Some (uu____6806))))))
end))
end
| (uu____6824, FStar_Syntax_Syntax.Tm_refine (y, uu____6826)) -> begin
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
| (FStar_Syntax_Syntax.Tm_refine (x, uu____6858), uu____6859) -> begin
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
| uu____6890 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____6924) -> begin
(

let uu____6937 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___125_6946 -> (match (uu___125_6946) with
| FStar_TypeChecker_Common.TProb (tp1) -> begin
(match (tp1.FStar_TypeChecker_Common.rank) with
| Some (rank1) when (is_flex_rigid rank1) -> begin
(

let uu____6951 = (FStar_Syntax_Util.head_and_args tp1.FStar_TypeChecker_Common.lhs)
in (match (uu____6951) with
| (u', uu____6962) -> begin
(

let uu____6977 = (

let uu____6978 = (whnf env u')
in uu____6978.FStar_Syntax_Syntax.n)
in (match (uu____6977) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____6982) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____6998 -> begin
false
end))
end))
end
| uu____6999 -> begin
false
end)
end
| uu____7001 -> begin
false
end))))
in (match (uu____6937) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun uu____7026 tps -> (match (uu____7026) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd1))::tl1 -> begin
(

let uu____7067 = (

let uu____7074 = (whnf env hd1.FStar_TypeChecker_Common.rhs)
in (conjoin bound uu____7074))
in (match (uu____7067) with
| Some (bound1, sub1) -> begin
(make_upper_bound ((bound1), ((FStar_List.append sub1 sub_probs))) tl1)
end
| None -> begin
None
end))
end
| uu____7109 -> begin
None
end)
end))
in (

let uu____7116 = (

let uu____7123 = (

let uu____7129 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((uu____7129), ([])))
in (make_upper_bound uu____7123 upper_bounds))
in (match (uu____7116) with
| None -> begin
((

let uu____7138 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____7138) with
| true -> begin
(FStar_Util.print_string "No upper bounds\n")
end
| uu____7139 -> begin
()
end));
None;
)
end
| Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in ((

let uu____7157 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____7157) with
| true -> begin
(

let wl' = (

let uu___154_7159 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___154_7159.wl_deferred; ctr = uu___154_7159.ctr; defer_ok = uu___154_7159.defer_ok; smt_ok = uu___154_7159.smt_ok; tcenv = uu___154_7159.tcenv})
in (

let uu____7160 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" uu____7160)))
end
| uu____7161 -> begin
()
end));
(

let uu____7162 = (solve_t env eq_prob (

let uu___155_7163 = wl
in {attempting = sub_probs; wl_deferred = uu___155_7163.wl_deferred; ctr = uu___155_7163.ctr; defer_ok = uu___155_7163.defer_ok; smt_ok = uu___155_7163.smt_ok; tcenv = uu___155_7163.tcenv}))
in (match (uu____7162) with
| Success (uu____7165) -> begin
(

let wl1 = (

let uu___156_7167 = wl
in {attempting = rest; wl_deferred = uu___156_7167.wl_deferred; ctr = uu___156_7167.ctr; defer_ok = uu___156_7167.defer_ok; smt_ok = uu___156_7167.smt_ok; tcenv = uu___156_7167.tcenv})
in (

let wl2 = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl1)
in (

let uu____7169 = (FStar_List.fold_left (fun wl3 p -> (solve_prob' true p None [] wl3)) wl2 upper_bounds)
in Some (wl2))))
end
| uu____7172 -> begin
None
end));
))
end)))
end))
end
| uu____7173 -> begin
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

let uu____7238 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____7238) with
| true -> begin
(

let uu____7239 = (prob_to_string env1 rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" uu____7239))
end
| uu____7240 -> begin
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

let uu___157_7271 = hd1
in (

let uu____7272 = (FStar_Syntax_Subst.subst subst1 hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___157_7271.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___157_7271.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7272}))
in (

let hd21 = (

let uu___158_7276 = hd2
in (

let uu____7277 = (FStar_Syntax_Subst.subst subst1 hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___158_7276.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___158_7276.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7277}))
in (

let prob = (

let uu____7281 = (

let uu____7284 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd11.FStar_Syntax_Syntax.sort uu____7284 hd21.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _0_47 -> FStar_TypeChecker_Common.TProb (_0_47)) uu____7281))
in (

let hd12 = (FStar_Syntax_Syntax.freshen_bv hd11)
in (

let subst2 = (

let uu____7292 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst1)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd12))))::uu____7292)
in (

let env2 = (FStar_TypeChecker_Env.push_bv env1 hd12)
in (

let uu____7295 = (aux ((((hd12), (imp)))::scope) env2 subst2 xs1 ys1)
in (match (uu____7295) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi1 = (

let uu____7313 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (

let uu____7316 = (close_forall env2 ((((hd12), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj uu____7313 uu____7316)))
in ((

let uu____7322 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Rel")))
in (match (uu____7322) with
| true -> begin
(

let uu____7323 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____7324 = (FStar_Syntax_Print.bv_to_string hd12)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" uu____7323 uu____7324)))
end
| uu____7325 -> begin
()
end));
FStar_Util.Inl ((((prob)::sub_probs), (phi1)));
))
end
| fail -> begin
fail
end))))))))
end
| uu____7339 -> begin
FStar_Util.Inr ("arity or argument-qualifier mismatch")
end))
in (

let scope = (p_scope orig)
in (

let uu____7345 = (aux scope env [] bs1 bs2)
in (match (uu____7345) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let wl1 = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl1)))
end)))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let uu____7361 = (compress_tprob wl problem)
in (solve_t' env uu____7361 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer1 = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env1 orig wl1 head1 head2 t1 t2 -> (

let uu____7394 = (head_matches_delta env1 wl1 t1 t2)
in (match (uu____7394) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____7411), uu____7412) -> begin
(

let may_relate = (fun head3 -> (

let uu____7427 = (

let uu____7428 = (FStar_Syntax_Util.un_uinst head3)
in uu____7428.FStar_Syntax_Syntax.n)
in (match (uu____7427) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____7434 -> begin
false
end)))
in (

let uu____7435 = (((may_relate head1) || (may_relate head2)) && wl1.smt_ok)
in (match (uu____7435) with
| true -> begin
(

let guard = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_eq2 env1 t1 t2)
end
| uu____7437 -> begin
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

let uu____7452 = (

let uu____7453 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t11 uu____7453 t21))
in (FStar_Syntax_Util.mk_forall u_x x uu____7452))))
end))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB)) with
| true -> begin
(has_type_guard t1 t2)
end
| uu____7454 -> begin
(has_type_guard t2 t1)
end))
end)
in (

let uu____7455 = (solve_prob orig (Some (guard)) [] wl1)
in (solve env1 uu____7455)))
end
| uu____7456 -> begin
(giveup env1 "head mismatch" orig)
end)))
end
| (uu____7457, Some (t11, t21)) -> begin
(solve_t env1 (

let uu___159_7465 = problem
in {FStar_TypeChecker_Common.pid = uu___159_7465.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___159_7465.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___159_7465.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___159_7465.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___159_7465.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___159_7465.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___159_7465.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___159_7465.FStar_TypeChecker_Common.rank}) wl1)
end
| (uu____7466, None) -> begin
((

let uu____7473 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____7473) with
| true -> begin
(

let uu____7474 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____7475 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____7476 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____7477 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" uu____7474 uu____7475 uu____7476 uu____7477)))))
end
| uu____7478 -> begin
()
end));
(

let uu____7479 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____7479) with
| (head11, args1) -> begin
(

let uu____7505 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____7505) with
| (head21, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((nargs <> (FStar_List.length args2))) with
| true -> begin
(

let uu____7545 = (

let uu____7546 = (FStar_Syntax_Print.term_to_string head11)
in (

let uu____7547 = (args_to_string args1)
in (

let uu____7548 = (FStar_Syntax_Print.term_to_string head21)
in (

let uu____7549 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____7546 uu____7547 uu____7548 uu____7549)))))
in (giveup env1 uu____7545 orig))
end
| uu____7550 -> begin
(

let uu____7551 = ((nargs = (Prims.parse_int "0")) || (

let uu____7554 = (FStar_Syntax_Util.eq_args args1 args2)
in (uu____7554 = FStar_Syntax_Util.Equal)))
in (match (uu____7551) with
| true -> begin
(

let uu____7555 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____7555) with
| USolved (wl2) -> begin
(

let uu____7557 = (solve_prob orig None [] wl2)
in (solve env1 uu____7557))
end
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end))
end
| uu____7560 -> begin
(

let uu____7561 = (base_and_refinement env1 wl1 t1)
in (match (uu____7561) with
| (base1, refinement1) -> begin
(

let uu____7587 = (base_and_refinement env1 wl1 t2)
in (match (uu____7587) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (None, None) -> begin
(

let uu____7641 = (solve_maybe_uinsts env1 orig head11 head21 wl1)
in (match (uu____7641) with
| UFailed (msg) -> begin
(giveup env1 msg orig)
end
| UDeferred (wl2) -> begin
(solve env1 (defer "universe constraints" orig wl2))
end
| USolved (wl2) -> begin
(

let subprobs = (FStar_List.map2 (fun uu____7651 uu____7652 -> (match (((uu____7651), (uu____7652))) with
| ((a, uu____7662), (a', uu____7664)) -> begin
(

let uu____7669 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _0_48 -> FStar_TypeChecker_Common.TProb (_0_48)) uu____7669))
end)) args1 args2)
in (

let formula = (

let uu____7675 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____7675))
in (

let wl3 = (solve_prob orig (Some (formula)) [] wl2)
in (solve env1 (attempt subprobs wl3)))))
end))
end
| uu____7679 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env1 (

let uu___160_7712 = problem
in {FStar_TypeChecker_Common.pid = uu___160_7712.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___160_7712.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___160_7712.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___160_7712.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___160_7712.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___160_7712.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___160_7712.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___160_7712.FStar_TypeChecker_Common.rank}) wl1)))
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

let uu____7732 = p
in (match (uu____7732) with
| (((u, k), xs, c), ps, (h, uu____7743, qs)) -> begin
(

let xs1 = (sn_binders env1 xs)
in (

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____7792 = (imitation_sub_probs orig env1 xs1 ps qs)
in (match (uu____7792) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (

let uu____7806 = (h gs_xs)
in (

let uu____7807 = (

let uu____7814 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_49 -> FStar_Util.Inl (_0_49)))
in (FStar_All.pipe_right uu____7814 (fun _0_50 -> Some (_0_50))))
in (FStar_Syntax_Util.abs xs1 uu____7806 uu____7807)))
in ((

let uu____7845 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____7845) with
| true -> begin
(

let uu____7846 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____7847 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____7848 = (FStar_Syntax_Print.term_to_string im)
in (

let uu____7849 = (FStar_Syntax_Print.tag_of_term im)
in (

let uu____7850 = (

let uu____7851 = (FStar_List.map (prob_to_string env1) sub_probs)
in (FStar_All.pipe_right uu____7851 (FStar_String.concat ", ")))
in (

let uu____7854 = (FStar_TypeChecker_Normalize.term_to_string env1 formula)
in (FStar_Util.print6 "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" uu____7846 uu____7847 uu____7848 uu____7849 uu____7850 uu____7854)))))))
end
| uu____7855 -> begin
()
end));
(

let wl2 = (solve_prob orig (Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl1)
in (solve env1 (attempt sub_probs wl2)));
))
end))))
end)))
in (

let imitate' = (fun orig env1 wl1 uu___126_7872 -> (match (uu___126_7872) with
| None -> begin
(giveup env1 "unable to compute subterms" orig)
end
| Some (p) -> begin
(imitate orig env1 wl1 p)
end))
in (

let project = (fun orig env1 wl1 i p -> (

let uu____7901 = p
in (match (uu____7901) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____7959 = (FStar_List.nth ps i)
in (match (uu____7959) with
| (pi, uu____7962) -> begin
(

let uu____7967 = (FStar_List.nth xs i)
in (match (uu____7967) with
| (xi, uu____7974) -> begin
(

let rec gs = (fun k -> (

let uu____7983 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____7983) with
| (bs, k1) -> begin
(

let rec aux = (fun subst1 bs1 -> (match (bs1) with
| [] -> begin
(([]), ([]))
end
| ((a, uu____8035))::tl1 -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst1 a.FStar_Syntax_Syntax.sort)
in (

let uu____8043 = (new_uvar r xs k_a)
in (match (uu____8043) with
| (gi_xs, gi) -> begin
(

let gi_xs1 = (FStar_TypeChecker_Normalize.eta_expand env1 gi_xs)
in (

let gi_ps = ((FStar_Syntax_Syntax.mk_Tm_app gi ps) (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((a), (gi_xs1))))::subst1
in (

let uu____8062 = (aux subst2 tl1)
in (match (uu____8062) with
| (gi_xs', gi_ps') -> begin
(

let uu____8077 = (

let uu____8079 = (FStar_Syntax_Syntax.as_arg gi_xs1)
in (uu____8079)::gi_xs')
in (

let uu____8080 = (

let uu____8082 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (uu____8082)::gi_ps')
in ((uu____8077), (uu____8080))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in (

let uu____8085 = (

let uu____8086 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation uu____8086))
in (match (uu____8085) with
| true -> begin
None
end
| uu____8088 -> begin
(

let uu____8089 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (uu____8089) with
| (g_xs, uu____8096) -> begin
(

let xi1 = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (

let uu____8103 = ((FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs) None r)
in (

let uu____8108 = (

let uu____8115 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_51 -> FStar_Util.Inl (_0_51)))
in (FStar_All.pipe_right uu____8115 (fun _0_52 -> Some (_0_52))))
in (FStar_Syntax_Util.abs xs uu____8103 uu____8108)))
in (

let sub1 = (

let uu____8146 = (

let uu____8149 = ((FStar_Syntax_Syntax.mk_Tm_app proj ps) None r)
in (

let uu____8156 = (

let uu____8159 = (FStar_List.map (fun uu____8165 -> (match (uu____8165) with
| (uu____8170, uu____8171, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h uu____8159))
in (mk_problem (p_scope orig) orig uu____8149 (p_rel orig) uu____8156 None "projection")))
in (FStar_All.pipe_left (fun _0_53 -> FStar_TypeChecker_Common.TProb (_0_53)) uu____8146))
in ((

let uu____8181 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Rel")))
in (match (uu____8181) with
| true -> begin
(

let uu____8182 = (FStar_Syntax_Print.term_to_string proj)
in (

let uu____8183 = (prob_to_string env1 sub1)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" uu____8182 uu____8183)))
end
| uu____8184 -> begin
()
end));
(

let wl2 = (

let uu____8186 = (

let uu____8188 = (FStar_All.pipe_left Prims.fst (p_guard sub1))
in Some (uu____8188))
in (solve_prob orig uu____8186 ((TERM (((u), (proj))))::[]) wl1))
in (

let uu____8193 = (solve env1 (attempt ((sub1)::[]) wl2))
in (FStar_All.pipe_left (fun _0_54 -> Some (_0_54)) uu____8193)));
))))
end))
end)))
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl1 -> (

let uu____8217 = lhs
in (match (uu____8217) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let uu____8240 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (uu____8240) with
| (xs, c) -> begin
(match (((FStar_List.length xs) = (FStar_List.length ps))) with
| true -> begin
(

let uu____8262 = (

let uu____8288 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____8288)))
in Some (uu____8262))
end
| uu____8354 -> begin
(

let k_uv1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (

let uu____8371 = (

let uu____8375 = (

let uu____8376 = (FStar_Syntax_Subst.compress k)
in uu____8376.FStar_Syntax_Syntax.n)
in ((uu____8375), (args)))
in (match (uu____8371) with
| (uu____8383, []) -> begin
(

let uu____8385 = (

let uu____8391 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____8391)))
in Some (uu____8385))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(

let uu____8408 = (FStar_Syntax_Util.head_and_args k)
in (match (uu____8408) with
| (uv1, uv_args) -> begin
(

let uu____8437 = (

let uu____8438 = (FStar_Syntax_Subst.compress uv1)
in uu____8438.FStar_Syntax_Syntax.n)
in (match (uu____8437) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____8445) -> begin
(

let uu____8458 = (pat_vars env [] uv_args)
in (match (uu____8458) with
| None -> begin
None
end
| Some (scope) -> begin
(

let xs1 = (FStar_All.pipe_right args (FStar_List.map (fun uu____8472 -> (

let uu____8473 = (

let uu____8474 = (

let uu____8475 = (

let uu____8478 = (

let uu____8479 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8479 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____8478))
in (Prims.fst uu____8475))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) uu____8474))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____8473)))))
in (

let c1 = (

let uu____8485 = (

let uu____8486 = (

let uu____8489 = (

let uu____8490 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8490 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____8489))
in (Prims.fst uu____8486))
in (FStar_Syntax_Syntax.mk_Total uu____8485))
in (

let k' = (FStar_Syntax_Util.arrow xs1 c1)
in (

let uv_sol = (

let uu____8499 = (

let uu____8506 = (

let uu____8512 = (

let uu____8513 = (

let uu____8516 = (

let uu____8517 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8517 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total uu____8516))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8513))
in FStar_Util.Inl (uu____8512))
in Some (uu____8506))
in (FStar_Syntax_Util.abs scope k' uu____8499))
in ((FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)));
Some (((xs1), (c1)));
)))))
end))
end
| uu____8540 -> begin
None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs1, c1), uu____8545) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs1)
in (match ((n_xs = n_args)) with
| true -> begin
(

let uu____8571 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (FStar_All.pipe_right uu____8571 (fun _0_55 -> Some (_0_55))))
end
| uu____8581 -> begin
(match ((n_xs < n_args)) with
| true -> begin
(

let uu____8590 = (FStar_Util.first_N n_xs args)
in (match (uu____8590) with
| (args1, rest) -> begin
(

let uu____8606 = (FStar_Syntax_Subst.open_comp xs1 c1)
in (match (uu____8606) with
| (xs2, c2) -> begin
(

let uu____8614 = (elim (FStar_Syntax_Util.comp_result c2) rest)
in (FStar_Util.bind_opt uu____8614 (fun uu____8625 -> (match (uu____8625) with
| (xs', c3) -> begin
Some ((((FStar_List.append xs2 xs')), (c3)))
end))))
end))
end))
end
| uu____8646 -> begin
(

let uu____8647 = (FStar_Util.first_N n_args xs1)
in (match (uu____8647) with
| (xs2, rest) -> begin
(

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c1))))) None k.FStar_Syntax_Syntax.pos)
in (

let uu____8693 = (

let uu____8696 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs2 uu____8696))
in (FStar_All.pipe_right uu____8693 (fun _0_56 -> Some (_0_56)))))
end))
end)
end)))
end
| uu____8704 -> begin
(

let uu____8708 = (

let uu____8709 = (FStar_Syntax_Print.uvar_to_string uv)
in (

let uu____8713 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____8714 = (FStar_Syntax_Print.term_to_string k_uv1)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" uu____8709 uu____8713 uu____8714))))
in (failwith uu____8708))
end)))
in (

let uu____8718 = (elim k_uv1 ps)
in (FStar_Util.bind_opt uu____8718 (fun uu____8746 -> (match (uu____8746) with
| (xs1, c1) -> begin
(

let uu____8774 = (

let uu____8797 = (decompose env t2)
in ((((((uv), (k_uv1))), (xs1), (c1))), (ps), (uu____8797)))
in Some (uu____8774))
end))))))
end)
end)))
in (

let rec imitate_or_project = (fun n1 stopt i -> (match (((i >= n1) || (FStar_Option.isNone stopt))) with
| true -> begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end
| uu____8866 -> begin
(

let st = (FStar_Option.get stopt)
in (

let tx = (FStar_Unionfind.new_transaction ())
in (match ((i = (~- ((Prims.parse_int "1"))))) with
| true -> begin
(

let uu____8869 = (imitate orig env wl1 st)
in (match (uu____8869) with
| Failed (uu____8874) -> begin
((FStar_Unionfind.rollback tx);
(imitate_or_project n1 stopt (i + (Prims.parse_int "1")));
)
end
| sol -> begin
sol
end))
end
| uu____8879 -> begin
(

let uu____8880 = (project orig env wl1 i st)
in (match (uu____8880) with
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

let uu____8898 = (FStar_Syntax_Util.head_and_args t21)
in (match (uu____8898) with
| (hd1, uu____8909) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| uu____8927 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd1)
in (

let uu____8930 = (FStar_Util.set_is_subset_of fvs_hd fvs1)
in (match (uu____8930) with
| true -> begin
true
end
| uu____8931 -> begin
((

let uu____8933 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8933) with
| true -> begin
(

let uu____8934 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" uu____8934))
end
| uu____8935 -> begin
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

let uu____8942 = (

let uu____8945 = (FStar_Syntax_Util.head_and_args t21)
in (FStar_All.pipe_right uu____8945 Prims.fst))
in (FStar_All.pipe_right uu____8942 FStar_Syntax_Free.names))
in (

let uu____8976 = (FStar_Util.set_is_empty fvs_hd)
in (match (uu____8976) with
| true -> begin
(~- ((Prims.parse_int "1")))
end
| uu____8977 -> begin
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

let uu____8985 = (occurs_check env wl1 ((uv), (k_uv)) t21)
in (match (uu____8985) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____8993 = (

let uu____8994 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____8994))
in (giveup_or_defer1 orig uu____8993))
end
| uu____8995 -> begin
(

let uu____8996 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____8996) with
| true -> begin
(

let uu____8997 = (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t21)) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))
in (match (uu____8997) with
| true -> begin
(

let uu____8998 = (subterms args_lhs)
in (imitate' orig env wl1 uu____8998))
end
| uu____9000 -> begin
((

let uu____9002 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9002) with
| true -> begin
(

let uu____9003 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____9004 = (names_to_string fvs1)
in (

let uu____9005 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" uu____9003 uu____9004 uu____9005))))
end
| uu____9006 -> begin
()
end));
(

let sol = (match (vars) with
| [] -> begin
t21
end
| uu____9010 -> begin
(

let uu____9011 = (sn_binders env vars)
in (u_abs k_uv uu____9011 t21))
end)
in (

let wl2 = (solve_prob orig None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl1)
in (solve env wl2)));
)
end))
end
| uu____9018 -> begin
(match ((((not (patterns_only)) && wl1.defer_ok) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl1))
end
| uu____9019 -> begin
(

let uu____9020 = ((not (patterns_only)) && (check_head fvs1 t21))
in (match (uu____9020) with
| true -> begin
((

let uu____9022 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9022) with
| true -> begin
(

let uu____9023 = (FStar_Syntax_Print.term_to_string t11)
in (

let uu____9024 = (names_to_string fvs1)
in (

let uu____9025 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" uu____9023 uu____9024 uu____9025))))
end
| uu____9026 -> begin
()
end));
(

let uu____9027 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____9027 (~- ((Prims.parse_int "1")))));
)
end
| uu____9036 -> begin
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
| uu____9037 -> begin
(

let uu____9038 = (

let uu____9039 = (FStar_Syntax_Free.names t1)
in (check_head uu____9039 t2))
in (match (uu____9038) with
| true -> begin
(

let im_ok = (imitate_ok t2)
in ((

let uu____9043 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9043) with
| true -> begin
(

let uu____9044 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" uu____9044 (match ((im_ok < (Prims.parse_int "0"))) with
| true -> begin
"imitating"
end
| uu____9045 -> begin
"projecting"
end)))
end
| uu____9046 -> begin
()
end));
(

let uu____9047 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____9047 im_ok));
))
end
| uu____9056 -> begin
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
| uu____9067 -> begin
(

let force_quasi_pattern = (fun xs_opt uu____9089 -> (match (uu____9089) with
| (t, u, k, args) -> begin
(

let uu____9119 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____9119) with
| (all_formals, uu____9130) -> begin
(

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args1 -> (match (((formals), (args1))) with
| ([], []) -> begin
(

let pat_args1 = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun uu____9222 -> (match (uu____9222) with
| (x, imp) -> begin
(

let uu____9229 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____9229), (imp)))
end))))
in (

let pattern_vars1 = (FStar_List.rev pattern_vars)
in (

let kk = (

let uu____9237 = (FStar_Syntax_Util.type_u ())
in (match (uu____9237) with
| (t1, uu____9241) -> begin
(

let uu____9242 = (new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1 t1)
in (Prims.fst uu____9242))
end))
in (

let uu____9245 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk)
in (match (uu____9245) with
| (t', tm_u1) -> begin
(

let uu____9252 = (destruct_flex_t t')
in (match (uu____9252) with
| (uu____9272, u1, k1, uu____9275) -> begin
(

let sol = (

let uu____9303 = (

let uu____9308 = (u_abs k all_formals t')
in ((((u), (k))), (uu____9308)))
in TERM (uu____9303))
in (

let t_app = ((FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1) None t.FStar_Syntax_Syntax.pos)
in ((sol), (((t_app), (u1), (k1), (pat_args1))))))
end))
end)))))
end
| ((formal)::formals1, (hd1)::tl1) -> begin
(

let uu____9368 = (pat_var_opt env pat_args hd1)
in (match (uu____9368) with
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun uu____9397 -> (match (uu____9397) with
| (x, uu____9401) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in (match ((not (maybe_pat))) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals1 tl1)
end
| uu____9404 -> begin
(

let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____9407 = (

let uu____9408 = (FStar_Util.set_is_subset_of fvs pattern_var_set)
in (not (uu____9408)))
in (match (uu____9407) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals1 tl1)
end
| uu____9411 -> begin
(

let uu____9412 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) uu____9412 formals1 tl1))
end)))
end))
end))
end
| uu____9418 -> begin
(failwith "Impossible")
end))
in (

let uu____9429 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] uu____9429 all_formals args)))
end))
end))
in (

let solve_both_pats = (fun wl1 uu____9477 uu____9478 r -> (match (((uu____9477), (uu____9478))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
(

let uu____9632 = ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys))
in (match (uu____9632) with
| true -> begin
(

let uu____9636 = (solve_prob orig None [] wl1)
in (solve env uu____9636))
end
| uu____9637 -> begin
(

let xs1 = (sn_binders env xs)
in (

let ys1 = (sn_binders env ys)
in (

let zs = (intersect_vars xs1 ys1)
in ((

let uu____9651 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9651) with
| true -> begin
(

let uu____9652 = (FStar_Syntax_Print.binders_to_string ", " xs1)
in (

let uu____9653 = (FStar_Syntax_Print.binders_to_string ", " ys1)
in (

let uu____9654 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (

let uu____9655 = (FStar_Syntax_Print.term_to_string k1)
in (

let uu____9656 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" uu____9652 uu____9653 uu____9654 uu____9655 uu____9656))))))
end
| uu____9657 -> begin
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

let uu____9698 = (FStar_Syntax_Util.subst_of_list xs2 args)
in (FStar_Syntax_Subst.subst uu____9698 k))
end
| uu____9700 -> begin
(match ((args_len < xs_len)) with
| true -> begin
(

let uu____9706 = (FStar_Util.first_N args_len xs2)
in (match (uu____9706) with
| (xs3, xs_rest) -> begin
(

let k3 = (

let uu____9736 = (FStar_Syntax_Syntax.mk_GTotal k)
in (FStar_Syntax_Util.arrow xs_rest uu____9736))
in (

let uu____9739 = (FStar_Syntax_Util.subst_of_list xs3 args)
in (FStar_Syntax_Subst.subst uu____9739 k3)))
end))
end
| uu____9741 -> begin
(

let uu____9742 = (

let uu____9743 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____9744 = (FStar_Syntax_Print.binders_to_string ", " xs2)
in (

let uu____9745 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" uu____9743 uu____9744 uu____9745))))
in (failwith uu____9742))
end)
end))))
in (

let uu____9746 = (

let uu____9752 = (

let uu____9760 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals uu____9760))
in (match (uu____9752) with
| (bs, k1') -> begin
(

let uu____9778 = (

let uu____9786 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals uu____9786))
in (match (uu____9778) with
| (cs, k2') -> begin
(

let k1'_xs = (subst_k k1' bs args1)
in (

let k2'_ys = (subst_k k2' cs args2)
in (

let sub_prob = (

let uu____9807 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_57 -> FStar_TypeChecker_Common.TProb (_0_57)) uu____9807))
in (

let uu____9812 = (

let uu____9815 = (

let uu____9816 = (FStar_Syntax_Subst.compress k1')
in uu____9816.FStar_Syntax_Syntax.n)
in (

let uu____9819 = (

let uu____9820 = (FStar_Syntax_Subst.compress k2')
in uu____9820.FStar_Syntax_Syntax.n)
in ((uu____9815), (uu____9819))))
in (match (uu____9812) with
| (FStar_Syntax_Syntax.Tm_type (uu____9828), uu____9829) -> begin
((k1'), ((sub_prob)::[]))
end
| (uu____9833, FStar_Syntax_Syntax.Tm_type (uu____9834)) -> begin
((k2'), ((sub_prob)::[]))
end
| uu____9838 -> begin
(

let uu____9841 = (FStar_Syntax_Util.type_u ())
in (match (uu____9841) with
| (t, uu____9850) -> begin
(

let uu____9851 = (new_uvar r zs t)
in (match (uu____9851) with
| (k_zs, uu____9860) -> begin
(

let kprob = (

let uu____9862 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k_zs None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_58 -> FStar_TypeChecker_Common.TProb (_0_58)) uu____9862))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end)))))
end))
end))
in (match (uu____9746) with
| (k_u', sub_probs) -> begin
(

let uu____9876 = (

let uu____9884 = (

let uu____9885 = (new_uvar r zs k_u')
in (FStar_All.pipe_left Prims.fst uu____9885))
in (

let uu____9890 = (

let uu____9893 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs1 uu____9893))
in (

let uu____9896 = (

let uu____9899 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys1 uu____9899))
in ((uu____9884), (uu____9890), (uu____9896)))))
in (match (uu____9876) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs1 u_zs)
in (

let uu____9918 = (occurs_check env wl1 ((u1), (k1)) sub1)
in (match (uu____9918) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occcurs check")
end
| uu____9930 -> begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in (

let uu____9942 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____9942) with
| true -> begin
(

let wl2 = (solve_prob orig None ((sol1)::[]) wl1)
in (solve env wl2))
end
| uu____9947 -> begin
(

let sub2 = (u_abs knew2 ys1 u_zs)
in (

let uu____9949 = (occurs_check env wl1 ((u2), (k2)) sub2)
in (match (uu____9949) with
| (occurs_ok1, msg1) -> begin
(match ((not (occurs_ok1))) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: failed occurs check")
end
| uu____9961 -> begin
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

let solve_one_pat = (fun uu____10001 uu____10002 -> (match (((uu____10001), (uu____10002))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
((

let uu____10106 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10106) with
| true -> begin
(

let uu____10107 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10108 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" uu____10107 uu____10108)))
end
| uu____10109 -> begin
()
end));
(

let uu____10110 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____10110) with
| true -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____10120 uu____10121 -> (match (((uu____10120), (uu____10121))) with
| ((a, uu____10131), (t21, uu____10133)) -> begin
(

let uu____10138 = (

let uu____10141 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig uu____10141 FStar_TypeChecker_Common.EQ t21 None "flex-flex index"))
in (FStar_All.pipe_right uu____10138 (fun _0_59 -> FStar_TypeChecker_Common.TProb (_0_59))))
end)) xs args2)
in (

let guard = (

let uu____10145 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____10145))
in (

let wl1 = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))))
end
| uu____10151 -> begin
(

let t21 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t21)
in (

let uu____10155 = (occurs_check env wl ((u1), (k1)) t21)
in (match (uu____10155) with
| (occurs_ok, uu____10164) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in (

let uu____10169 = (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars))
in (match (uu____10169) with
| true -> begin
(

let sol = (

let uu____10171 = (

let uu____10176 = (u_abs k1 xs t21)
in ((((u1), (k1))), (uu____10176)))
in TERM (uu____10171))
in (

let wl1 = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl1)))
end
| uu____10188 -> begin
(

let uu____10189 = (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok))
in (match (uu____10189) with
| true -> begin
(

let uu____10190 = (force_quasi_pattern (Some (xs)) ((t21), (u2), (k2), (args2)))
in (match (uu____10190) with
| (sol, (uu____10204, u21, k21, ys)) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____10214 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____10214) with
| true -> begin
(

let uu____10215 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" uu____10215))
end
| uu____10216 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____10220 -> begin
(giveup env "impossible" orig)
end);
))
end))
end
| uu____10221 -> begin
(giveup_or_defer1 orig "flex-flex constraint")
end))
end)))
end))))
end));
)
end))
in (

let uu____10222 = lhs
in (match (uu____10222) with
| (t1, u1, k1, args1) -> begin
(

let uu____10227 = rhs
in (match (uu____10227) with
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
| uu____10253 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer1 orig "flex-flex: neither side is a pattern")
end
| uu____10258 -> begin
(

let uu____10259 = (force_quasi_pattern None ((t1), (u1), (k1), (args1)))
in (match (uu____10259) with
| (sol, uu____10266) -> begin
(

let wl1 = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____10269 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____10269) with
| true -> begin
(

let uu____10270 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" uu____10270))
end
| uu____10271 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl1)
end
| uu____10275 -> begin
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

let uu____10277 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____10277) with
| true -> begin
(

let uu____10278 = (solve_prob orig None [] wl)
in (solve env uu____10278))
end
| uu____10279 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in (

let uu____10282 = (FStar_Util.physical_equality t1 t2)
in (match (uu____10282) with
| true -> begin
(

let uu____10283 = (solve_prob orig None [] wl)
in (solve env uu____10283))
end
| uu____10284 -> begin
((

let uu____10286 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____10286) with
| true -> begin
(

let uu____10287 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" uu____10287))
end
| uu____10288 -> begin
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

let mk_c = (fun c uu___127_10333 -> (match (uu___127_10333) with
| [] -> begin
c
end
| bs -> begin
(

let uu____10347 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c))))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____10347))
end))
in (

let uu____10361 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____10361) with
| ((bs11, c11), (bs21, c21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let c12 = (FStar_Syntax_Subst.subst_comp subst1 c11)
in (

let c22 = (FStar_Syntax_Subst.subst_comp subst1 c21)
in (

let rel = (

let uu____10447 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____10447) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____10448 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (

let uu____10449 = (mk_problem scope orig c12 rel c22 None "function co-domain")
in (FStar_All.pipe_left (fun _0_60 -> FStar_TypeChecker_Common.CProb (_0_60)) uu____10449)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___128_10526 -> (match (uu___128_10526) with
| [] -> begin
t
end
| bs -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l))))) None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____10565 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____10565) with
| ((bs11, tbody11), (bs21, tbody21)) -> begin
(solve_binders env bs11 bs21 orig wl (fun scope env1 subst1 -> (

let uu____10648 = (

let uu____10651 = (FStar_Syntax_Subst.subst subst1 tbody11)
in (

let uu____10652 = (FStar_Syntax_Subst.subst subst1 tbody21)
in (mk_problem scope orig uu____10651 problem.FStar_TypeChecker_Common.relation uu____10652 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _0_61 -> FStar_TypeChecker_Common.TProb (_0_61)) uu____10648))))
end)))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____10667) -> begin
true
end
| uu____10682 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____10701 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t3)) with
| true -> begin
FStar_Util.Inl (t3)
end
| uu____10707 -> begin
FStar_Util.Inr (t3)
end))
end))
in (

let uu____10710 = (

let uu____10721 = (maybe_eta t1)
in (

let uu____10726 = (maybe_eta t2)
in ((uu____10721), (uu____10726))))
in (match (uu____10710) with
| (FStar_Util.Inl (t11), FStar_Util.Inl (t21)) -> begin
(solve_t env (

let uu___161_10757 = problem
in {FStar_TypeChecker_Common.pid = uu___161_10757.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___161_10757.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___161_10757.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___161_10757.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___161_10757.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___161_10757.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___161_10757.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___161_10757.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs))) | ((FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs))) -> begin
(

let uu____10790 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____10790) with
| true -> begin
(

let uu____10791 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____10791 t_abs wl))
end
| uu____10795 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| uu____10796 -> begin
(failwith "Impossible: at least one side is an abstraction")
end))))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____10807), FStar_Syntax_Syntax.Tm_refine (uu____10808)) -> begin
(

let uu____10817 = (as_refinement env wl t1)
in (match (uu____10817) with
| (x1, phi1) -> begin
(

let uu____10822 = (as_refinement env wl t2)
in (match (uu____10822) with
| (x2, phi2) -> begin
(

let base_prob = (

let uu____10828 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _0_62 -> FStar_TypeChecker_Common.TProb (_0_62)) uu____10828))
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

let uu____10861 = (imp phi12 phi22)
in (FStar_All.pipe_right uu____10861 (guard_on_element wl problem x11))))
in (

let fallback = (fun uu____10865 -> (

let impl = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp1 FStar_Syntax_Util.mk_iff phi11 phi21)
end
| uu____10867 -> begin
(mk_imp1 FStar_Syntax_Util.mk_imp phi11 phi21)
end)
in (

let guard = (

let uu____10871 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____10871 impl))
in (

let wl1 = (solve_prob orig (Some (guard)) [] wl)
in (solve env1 (attempt ((base_prob)::[]) wl1))))))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let ref_prob = (

let uu____10878 = (

let uu____10881 = (

let uu____10882 = (FStar_Syntax_Syntax.mk_binder x11)
in (uu____10882)::(p_scope orig))
in (mk_problem uu____10881 orig phi11 FStar_TypeChecker_Common.EQ phi21 None "refinement formula"))
in (FStar_All.pipe_left (fun _0_63 -> FStar_TypeChecker_Common.TProb (_0_63)) uu____10878))
in (

let uu____10885 = (solve env1 (

let uu___162_10886 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___162_10886.ctr; defer_ok = false; smt_ok = uu___162_10886.smt_ok; tcenv = uu___162_10886.tcenv}))
in (match (uu____10885) with
| Failed (uu____10890) -> begin
(fallback ())
end
| Success (uu____10893) -> begin
(

let guard = (

let uu____10897 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (

let uu____10900 = (

let uu____10901 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right uu____10901 (guard_on_element wl problem x11)))
in (FStar_Syntax_Util.mk_conj uu____10897 uu____10900)))
in (

let wl1 = (solve_prob orig (Some (guard)) [] wl)
in (

let wl2 = (

let uu___163_10908 = wl1
in {attempting = uu___163_10908.attempting; wl_deferred = uu___163_10908.wl_deferred; ctr = (wl1.ctr + (Prims.parse_int "1")); defer_ok = uu___163_10908.defer_ok; smt_ok = uu___163_10908.smt_ok; tcenv = uu___163_10908.tcenv})
in (solve env1 (attempt ((base_prob)::[]) wl2)))))
end)))
end
| uu____10909 -> begin
(fallback ())
end)))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(

let uu____10962 = (destruct_flex_t t1)
in (

let uu____10963 = (destruct_flex_t t2)
in (flex_flex1 orig uu____10962 uu____10963)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(

let uu____10979 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____10979 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_arrow (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
(solve_t' env (

let uu___164_11028 = problem
in {FStar_TypeChecker_Common.pid = uu___164_11028.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___164_11028.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___164_11028.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___164_11028.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_11028.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_11028.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_11028.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_11028.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_11028.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____11044 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____11046 = (

let uu____11047 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____11047))
in (match (uu____11046) with
| true -> begin
(

let uu____11048 = (FStar_All.pipe_left (fun _0_64 -> FStar_TypeChecker_Common.TProb (_0_64)) (

let uu___165_11051 = problem
in {FStar_TypeChecker_Common.pid = uu___165_11051.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___165_11051.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___165_11051.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___165_11051.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___165_11051.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___165_11051.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___165_11051.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___165_11051.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___165_11051.FStar_TypeChecker_Common.rank}))
in (

let uu____11052 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____11048 uu____11052 t2 wl)))
end
| uu____11056 -> begin
(

let uu____11057 = (base_and_refinement env wl t2)
in (match (uu____11057) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(

let uu____11087 = (FStar_All.pipe_left (fun _0_65 -> FStar_TypeChecker_Common.TProb (_0_65)) (

let uu___166_11090 = problem
in {FStar_TypeChecker_Common.pid = uu___166_11090.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___166_11090.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___166_11090.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___166_11090.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_11090.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___166_11090.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___166_11090.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_11090.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_11090.FStar_TypeChecker_Common.rank}))
in (

let uu____11091 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____11087 uu____11091 t_base wl)))
end
| Some (y, phi) -> begin
(

let y' = (

let uu___167_11106 = y
in {FStar_Syntax_Syntax.ppname = uu___167_11106.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___167_11106.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element wl problem y' phi)
in (

let base_prob = (

let uu____11109 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_66 -> FStar_TypeChecker_Common.TProb (_0_66)) uu____11109))
in (

let guard = (

let uu____11117 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____11117 impl))
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
| uu____11138 -> begin
(

let uu____11139 = (base_and_refinement env wl t1)
in (match (uu____11139) with
| (t_base, uu____11150) -> begin
(solve_t env (

let uu___168_11165 = problem
in {FStar_TypeChecker_Common.pid = uu___168_11165.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___168_11165.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___168_11165.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___168_11165.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___168_11165.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___168_11165.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___168_11165.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___168_11165.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (FStar_Syntax_Syntax.Tm_refine (uu____11168), uu____11169) -> begin
(

let t21 = (

let uu____11177 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement uu____11177))
in (solve_t env (

let uu___169_11190 = problem
in {FStar_TypeChecker_Common.pid = uu___169_11190.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___169_11190.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___169_11190.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___169_11190.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___169_11190.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___169_11190.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___169_11190.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___169_11190.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___169_11190.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____11191, FStar_Syntax_Syntax.Tm_refine (uu____11192)) -> begin
(

let t11 = (

let uu____11200 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement uu____11200))
in (solve_t env (

let uu___170_11213 = problem
in {FStar_TypeChecker_Common.pid = uu___170_11213.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___170_11213.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___170_11213.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___170_11213.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___170_11213.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___170_11213.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___170_11213.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___170_11213.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___170_11213.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(

let head1 = (

let uu____11243 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____11243 Prims.fst))
in (

let head2 = (

let uu____11274 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____11274 Prims.fst))
in (

let uu____11302 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____11302) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____11311 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____11311) with
| true -> begin
(

let guard = (

let uu____11318 = (

let uu____11319 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____11319 = FStar_Syntax_Util.Equal))
in (match (uu____11318) with
| true -> begin
None
end
| uu____11321 -> begin
(

let uu____11322 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_67 -> Some (_0_67)) uu____11322))
end))
in (

let uu____11324 = (solve_prob orig guard [] wl)
in (solve env uu____11324)))
end
| uu____11325 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____11326 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t11, uu____11328, uu____11329), uu____11330) -> begin
(solve_t' env (

let uu___171_11359 = problem
in {FStar_TypeChecker_Common.pid = uu___171_11359.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t11; FStar_TypeChecker_Common.relation = uu___171_11359.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___171_11359.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___171_11359.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___171_11359.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___171_11359.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___171_11359.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___171_11359.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___171_11359.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____11362, FStar_Syntax_Syntax.Tm_ascribed (t21, uu____11364, uu____11365)) -> begin
(solve_t' env (

let uu___172_11394 = problem
in {FStar_TypeChecker_Common.pid = uu___172_11394.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___172_11394.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___172_11394.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t21; FStar_TypeChecker_Common.element = uu___172_11394.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___172_11394.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___172_11394.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___172_11394.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___172_11394.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___172_11394.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(

let uu____11407 = (

let uu____11408 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____11409 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____11408 uu____11409)))
in (failwith uu____11407))
end
| uu____11410 -> begin
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

let uu____11442 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____11442) with
| true -> begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end
| uu____11443 -> begin
()
end));
(

let sub_probs = (FStar_List.map2 (fun uu____11450 uu____11451 -> (match (((uu____11450), (uu____11451))) with
| ((a1, uu____11461), (a2, uu____11463)) -> begin
(

let uu____11468 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _0_68 -> FStar_TypeChecker_Common.TProb (_0_68)) uu____11468))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (

let uu____11474 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____11474))
in (

let wl1 = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl1)))));
))
in (

let solve_sub = (fun c11 edge c21 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let lift_c1 = (fun uu____11494 -> (

let wp = (match (c11.FStar_Syntax_Syntax.effect_args) with
| ((wp1, uu____11501))::[] -> begin
wp1
end
| uu____11514 -> begin
(

let uu____11520 = (

let uu____11521 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c11.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" uu____11521))
in (failwith uu____11520))
end)
in (

let uu____11524 = (

let uu____11530 = (

let uu____11531 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c11.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____11531))
in (uu____11530)::[])
in {FStar_Syntax_Syntax.comp_univs = c11.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c21.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c11.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____11524; FStar_Syntax_Syntax.flags = c11.FStar_Syntax_Syntax.flags})))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____11532 = (lift_c1 ())
in (solve_eq uu____11532 c21))
end
| uu____11533 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___129_11536 -> (match (uu___129_11536) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| uu____11537 -> begin
false
end))))
in (

let uu____11538 = (match (((c11.FStar_Syntax_Syntax.effect_args), (c21.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____11562))::uu____11563, ((wp2, uu____11565))::uu____11566) -> begin
((wp1), (wp2))
end
| uu____11607 -> begin
(

let uu____11620 = (

let uu____11621 = (

let uu____11624 = (

let uu____11625 = (FStar_Syntax_Print.lid_to_string c11.FStar_Syntax_Syntax.effect_name)
in (

let uu____11626 = (FStar_Syntax_Print.lid_to_string c21.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____11625 uu____11626)))
in ((uu____11624), (env.FStar_TypeChecker_Env.range)))
in FStar_Errors.Error (uu____11621))
in (Prims.raise uu____11620))
end)
in (match (uu____11538) with
| (wpc1, wpc2) -> begin
(

let uu____11643 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____11643) with
| true -> begin
(

let uu____11646 = (problem_using_guard orig c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env uu____11646 wl))
end
| uu____11649 -> begin
(

let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c21.FStar_Syntax_Syntax.effect_name)
in (

let uu____11651 = (FStar_All.pipe_right c2_decl.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____11651) with
| true -> begin
(

let c1_repr = (

let uu____11654 = (

let uu____11655 = (

let uu____11656 = (lift_c1 ())
in (FStar_Syntax_Syntax.mk_Comp uu____11656))
in (

let uu____11657 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____11655 uu____11657)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____11654))
in (

let c2_repr = (

let uu____11659 = (

let uu____11660 = (FStar_Syntax_Syntax.mk_Comp c21)
in (

let uu____11661 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____11660 uu____11661)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____11659))
in (

let prob = (

let uu____11663 = (

let uu____11666 = (

let uu____11667 = (FStar_Syntax_Print.term_to_string c1_repr)
in (

let uu____11668 = (FStar_Syntax_Print.term_to_string c2_repr)
in (FStar_Util.format2 "sub effect repr: %s <: %s" uu____11667 uu____11668)))
in (sub_prob c1_repr problem.FStar_TypeChecker_Common.relation c2_repr uu____11666))
in FStar_TypeChecker_Common.TProb (uu____11663))
in (

let wl1 = (

let uu____11670 = (

let uu____11672 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in Some (uu____11672))
in (solve_prob orig uu____11670 [] wl))
in (solve env (attempt ((prob)::[]) wl1))))))
end
| uu____11675 -> begin
(

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____11677 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____11679 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11679) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____11680 -> begin
()
end));
(

let uu____11681 = (

let uu____11684 = (

let uu____11685 = (

let uu____11695 = (

let uu____11696 = (

let uu____11697 = (env.FStar_TypeChecker_Env.universe_of env c11.FStar_Syntax_Syntax.result_typ)
in (uu____11697)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____11696 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (

let uu____11698 = (

let uu____11700 = (FStar_Syntax_Syntax.as_arg c11.FStar_Syntax_Syntax.result_typ)
in (

let uu____11701 = (

let uu____11703 = (

let uu____11704 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11704))
in (uu____11703)::[])
in (uu____11700)::uu____11701))
in ((uu____11695), (uu____11698))))
in FStar_Syntax_Syntax.Tm_app (uu____11685))
in (FStar_Syntax_Syntax.mk uu____11684))
in (uu____11681 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r));
)
end
| uu____11714 -> begin
(

let uu____11715 = (

let uu____11718 = (

let uu____11719 = (

let uu____11729 = (

let uu____11730 = (

let uu____11731 = (env.FStar_TypeChecker_Env.universe_of env c21.FStar_Syntax_Syntax.result_typ)
in (uu____11731)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____11730 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (

let uu____11732 = (

let uu____11734 = (FStar_Syntax_Syntax.as_arg c21.FStar_Syntax_Syntax.result_typ)
in (

let uu____11735 = (

let uu____11737 = (FStar_Syntax_Syntax.as_arg wpc2)
in (

let uu____11738 = (

let uu____11740 = (

let uu____11741 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c11.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11741))
in (uu____11740)::[])
in (uu____11737)::uu____11738))
in (uu____11734)::uu____11735))
in ((uu____11729), (uu____11732))))
in FStar_Syntax_Syntax.Tm_app (uu____11719))
in (FStar_Syntax_Syntax.mk uu____11718))
in (uu____11715 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r))
end)
end)
in (

let base_prob = (

let uu____11752 = (sub_prob c11.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c21.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _0_69 -> FStar_TypeChecker_Common.TProb (_0_69)) uu____11752))
in (

let wl1 = (

let uu____11758 = (

let uu____11760 = (

let uu____11763 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____11763 g))
in (FStar_All.pipe_left (fun _0_70 -> Some (_0_70)) uu____11760))
in (solve_prob orig uu____11758 [] wl))
in (solve env (attempt ((base_prob)::[]) wl1)))))
end)))
end))
end)))
end))))
in (

let uu____11773 = (FStar_Util.physical_equality c1 c2)
in (match (uu____11773) with
| true -> begin
(

let uu____11774 = (solve_prob orig None [] wl)
in (solve env uu____11774))
end
| uu____11775 -> begin
((

let uu____11777 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11777) with
| true -> begin
(

let uu____11778 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____11779 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____11778 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____11779)))
end
| uu____11780 -> begin
()
end));
(

let uu____11781 = (

let uu____11784 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____11785 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____11784), (uu____11785))))
in (match (uu____11781) with
| (c11, c21) -> begin
(match (((c11.FStar_Syntax_Syntax.n), (c21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____11789), FStar_Syntax_Syntax.Total (t2, uu____11791)) when (FStar_Syntax_Util.non_informative t2) -> begin
(

let uu____11804 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env uu____11804 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____11807), FStar_Syntax_Syntax.Total (uu____11808)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.Total (t2, _))) | ((FStar_Syntax_Syntax.GTotal (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) | ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) -> begin
(

let uu____11857 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env uu____11857 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(

let uu____11864 = (

let uu___173_11867 = problem
in (

let uu____11870 = (

let uu____11871 = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____11871))
in {FStar_TypeChecker_Common.pid = uu___173_11867.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____11870; FStar_TypeChecker_Common.relation = uu___173_11867.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___173_11867.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___173_11867.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___173_11867.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___173_11867.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___173_11867.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___173_11867.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___173_11867.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____11864 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(

let uu____11876 = (

let uu___174_11879 = problem
in (

let uu____11882 = (

let uu____11883 = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____11883))
in {FStar_TypeChecker_Common.pid = uu___174_11879.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___174_11879.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___174_11879.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____11882; FStar_TypeChecker_Common.element = uu___174_11879.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___174_11879.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___174_11879.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___174_11879.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___174_11879.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___174_11879.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____11876 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____11884), FStar_Syntax_Syntax.Comp (uu____11885)) -> begin
(

let uu____11886 = (((FStar_Syntax_Util.is_ml_comp c11) && (FStar_Syntax_Util.is_ml_comp c21)) || ((FStar_Syntax_Util.is_total_comp c11) && ((FStar_Syntax_Util.is_total_comp c21) || (FStar_Syntax_Util.is_ml_comp c21))))
in (match (uu____11886) with
| true -> begin
(

let uu____11887 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c11) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c21) None "result type")
in (solve_t env uu____11887 wl))
end
| uu____11890 -> begin
(

let c1_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c11)
in (

let c2_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c21)
in (match (((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name))) with
| true -> begin
(solve_eq c1_comp c2_comp)
end
| uu____11893 -> begin
(

let c12 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c11)
in (

let c22 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c21)
in ((

let uu____11897 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11897) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c12.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c22.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____11898 -> begin
()
end));
(

let uu____11899 = (FStar_TypeChecker_Env.monad_leq env c12.FStar_Syntax_Syntax.effect_name c22.FStar_Syntax_Syntax.effect_name)
in (match (uu____11899) with
| None -> begin
(

let uu____11901 = (((FStar_Syntax_Util.is_ghost_effect c12.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c22.FStar_Syntax_Syntax.effect_name)) && (

let uu____11902 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c22.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative uu____11902)))
in (match (uu____11901) with
| true -> begin
(

let edge = {FStar_TypeChecker_Env.msource = c12.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c22.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = FStar_TypeChecker_Env.identity_mlift}
in (solve_sub c12 edge c22))
end
| uu____11904 -> begin
(

let uu____11905 = (

let uu____11906 = (FStar_Syntax_Print.lid_to_string c12.FStar_Syntax_Syntax.effect_name)
in (

let uu____11907 = (FStar_Syntax_Print.lid_to_string c22.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____11906 uu____11907)))
in (giveup env uu____11905 orig))
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

let uu____11912 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____11932 -> (match (uu____11932) with
| (uu____11943, uu____11944, u, uu____11946, uu____11947, uu____11948) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____11912 (FStar_String.concat ", "))))


let ineqs_to_string : (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.string = (fun ineqs -> (

let vars = (

let uu____11977 = (FStar_All.pipe_right (Prims.fst ineqs) (FStar_List.map FStar_Syntax_Print.univ_to_string))
in (FStar_All.pipe_right uu____11977 (FStar_String.concat ", ")))
in (

let ineqs1 = (

let uu____11987 = (FStar_All.pipe_right (Prims.snd ineqs) (FStar_List.map (fun uu____11999 -> (match (uu____11999) with
| (u1, u2) -> begin
(

let uu____12004 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____12005 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "%s < %s" uu____12004 uu____12005)))
end))))
in (FStar_All.pipe_right uu____11987 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred), (g.FStar_TypeChecker_Env.univ_ineqs))) with
| (FStar_TypeChecker_Common.Trivial, [], (uu____12017, [])) -> begin
"{}"
end
| uu____12030 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____12040 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____12040) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____12041 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____12043 = (FStar_List.map (fun uu____12047 -> (match (uu____12047) with
| (uu____12050, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right uu____12043 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (

let uu____12054 = (ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs)
in (FStar_Util.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n" form carry uu____12054 imps)))))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = (

let uu____12092 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____12092) with
| true -> begin
(

let uu____12093 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____12094 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____12093 (rel_to_string rel) uu____12094)))
end
| uu____12095 -> begin
"TOP"
end))
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (

let uu____12114 = (

let uu____12116 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_71 -> Some (_0_71)) uu____12116))
in (FStar_Syntax_Syntax.new_bv uu____12114 t1))
in (

let env1 = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (

let uu____12122 = (

let uu____12124 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _0_72 -> Some (_0_72)) uu____12124))
in (

let uu____12126 = (FStar_TypeChecker_Env.get_range env1)
in (new_t_problem env1 t1 rel t2 uu____12122 uu____12126)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (

let probs1 = (

let uu____12149 = (FStar_Options.eager_inference ())
in (match (uu____12149) with
| true -> begin
(

let uu___175_12150 = probs
in {attempting = uu___175_12150.attempting; wl_deferred = uu___175_12150.wl_deferred; ctr = uu___175_12150.ctr; defer_ok = false; smt_ok = uu___175_12150.smt_ok; tcenv = uu___175_12150.tcenv})
end
| uu____12151 -> begin
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

let uu____12161 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____12161) with
| true -> begin
(

let uu____12162 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____12162))
end
| uu____12163 -> begin
()
end));
(err ((d), (s)));
)
end)))))


let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
((

let uu____12172 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____12172) with
| true -> begin
(

let uu____12173 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____12173))
end
| uu____12174 -> begin
()
end));
(

let f1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in ((

let uu____12177 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____12177) with
| true -> begin
(

let uu____12178 = (FStar_Syntax_Print.term_to_string f1)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____12178))
end
| uu____12179 -> begin
()
end));
(

let f2 = (

let uu____12181 = (

let uu____12182 = (FStar_Syntax_Util.unmeta f1)
in uu____12182.FStar_Syntax_Syntax.n)
in (match (uu____12181) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____12186 -> begin
FStar_TypeChecker_Common.NonTrivial (f1)
end))
in (

let uu___176_12187 = g
in {FStar_TypeChecker_Env.guard_f = f2; FStar_TypeChecker_Env.deferred = uu___176_12187.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___176_12187.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___176_12187.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(

let uu____12202 = (

let uu____12203 = (

let uu____12204 = (

let uu____12205 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right uu____12205 (fun _0_73 -> FStar_TypeChecker_Common.NonTrivial (_0_73))))
in {FStar_TypeChecker_Env.guard_f = uu____12204; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env uu____12203))
in (FStar_All.pipe_left (fun _0_74 -> Some (_0_74)) uu____12202))
end))


let try_teq : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun smt_ok env t1 t2 -> ((

let uu____12232 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12232) with
| true -> begin
(

let uu____12233 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12234 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" uu____12233 uu____12234)))
end
| uu____12235 -> begin
()
end));
(

let prob = (

let uu____12237 = (

let uu____12240 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None uu____12240))
in (FStar_All.pipe_left (fun _0_75 -> FStar_TypeChecker_Common.TProb (_0_75)) uu____12237))
in (

let g = (

let uu____12245 = (

let uu____12247 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____12247 (fun uu____12248 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12245))
in g));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____12262 = (try_teq true env t1 t2)
in (match (uu____12262) with
| None -> begin
(

let uu____12264 = (

let uu____12265 = (

let uu____12268 = (FStar_TypeChecker_Err.basic_type_error env None t2 t1)
in (

let uu____12269 = (FStar_TypeChecker_Env.get_range env)
in ((uu____12268), (uu____12269))))
in FStar_Errors.Error (uu____12265))
in (Prims.raise uu____12264))
end
| Some (g) -> begin
((

let uu____12272 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12272) with
| true -> begin
(

let uu____12273 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12274 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____12275 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____12273 uu____12274 uu____12275))))
end
| uu____12276 -> begin
()
end));
g;
)
end)))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 smt_ok -> ((

let uu____12291 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12291) with
| true -> begin
(

let uu____12292 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____12293 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" uu____12292 uu____12293)))
end
| uu____12294 -> begin
()
end));
(

let uu____12295 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____12295) with
| (prob, x) -> begin
(

let g = (

let uu____12303 = (

let uu____12305 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____12305 (fun uu____12306 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12303))
in ((

let uu____12312 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____12312) with
| true -> begin
(

let uu____12313 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____12314 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____12315 = (

let uu____12316 = (FStar_Util.must g)
in (guard_to_string env uu____12316))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" uu____12313 uu____12314 uu____12315))))
end
| uu____12317 -> begin
()
end));
(abstract_guard x g);
))
end));
))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env e t1 t2 -> (

let uu____12340 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12341 = (FStar_TypeChecker_Err.basic_type_error env (Some (e)) t2 t1)
in (FStar_Errors.report uu____12340 uu____12341))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> ((

let uu____12353 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12353) with
| true -> begin
(

let uu____12354 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____12355 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" uu____12354 uu____12355)))
end
| uu____12356 -> begin
()
end));
(

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____12358 -> begin
FStar_TypeChecker_Common.SUB
end)
in (

let prob = (

let uu____12360 = (

let uu____12363 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None uu____12363 "sub_comp"))
in (FStar_All.pipe_left (fun _0_76 -> FStar_TypeChecker_Common.CProb (_0_76)) uu____12360))
in (

let uu____12366 = (

let uu____12368 = (singleton env prob)
in (solve_and_commit env uu____12368 (fun uu____12369 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12366))));
))


let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun tx env uu____12388 -> (match (uu____12388) with
| (variables, ineqs) -> begin
(

let fail = (fun u1 u2 -> ((FStar_Unionfind.rollback tx);
(

let uu____12413 = (

let uu____12414 = (

let uu____12417 = (

let uu____12418 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____12419 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Universe %s and %s are incompatible" uu____12418 uu____12419)))
in (

let uu____12420 = (FStar_TypeChecker_Env.get_range env)
in ((uu____12417), (uu____12420))))
in FStar_Errors.Error (uu____12414))
in (Prims.raise uu____12413));
))
in (

let equiv = (fun v1 v' -> (

let uu____12428 = (

let uu____12431 = (FStar_Syntax_Subst.compress_univ v1)
in (

let uu____12432 = (FStar_Syntax_Subst.compress_univ v')
in ((uu____12431), (uu____12432))))
in (match (uu____12428) with
| (FStar_Syntax_Syntax.U_unif (v0), FStar_Syntax_Syntax.U_unif (v0')) -> begin
(FStar_Unionfind.equivalent v0 v0')
end
| uu____12440 -> begin
false
end)))
in (

let sols = (FStar_All.pipe_right variables (FStar_List.collect (fun v1 -> (

let uu____12454 = (FStar_Syntax_Subst.compress_univ v1)
in (match (uu____12454) with
| FStar_Syntax_Syntax.U_unif (uu____12458) -> begin
(

let lower_bounds_of_v = (FStar_All.pipe_right ineqs (FStar_List.collect (fun uu____12469 -> (match (uu____12469) with
| (u, v') -> begin
(

let uu____12475 = (equiv v1 v')
in (match (uu____12475) with
| true -> begin
(

let uu____12477 = (FStar_All.pipe_right variables (FStar_Util.for_some (equiv u)))
in (match (uu____12477) with
| true -> begin
[]
end
| uu____12480 -> begin
(u)::[]
end))
end
| uu____12481 -> begin
[]
end))
end))))
in (

let lb = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max (lower_bounds_of_v)))
in (((lb), (v1)))::[]))
end
| uu____12487 -> begin
[]
end)))))
in (

let uu____12490 = (

let wl = (

let uu___177_12493 = (empty_worklist env)
in {attempting = uu___177_12493.attempting; wl_deferred = uu___177_12493.wl_deferred; ctr = uu___177_12493.ctr; defer_ok = false; smt_ok = uu___177_12493.smt_ok; tcenv = uu___177_12493.tcenv})
in (FStar_All.pipe_right sols (FStar_List.map (fun uu____12500 -> (match (uu____12500) with
| (lb, v1) -> begin
(

let uu____12505 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl lb v1)
in (match (uu____12505) with
| USolved (wl1) -> begin
()
end
| uu____12507 -> begin
(fail lb v1)
end))
end)))))
in (

let rec check_ineq = (fun uu____12513 -> (match (uu____12513) with
| (u, v1) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u)
in (

let v2 = (FStar_TypeChecker_Normalize.normalize_universe env v1)
in (match (((u1), (v2))) with
| (FStar_Syntax_Syntax.U_zero, uu____12520) -> begin
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
| (FStar_Syntax_Syntax.U_max (us), uu____12536) -> begin
(FStar_All.pipe_right us (FStar_Util.for_all (fun u2 -> (check_ineq ((u2), (v2))))))
end
| (uu____12540, FStar_Syntax_Syntax.U_max (vs)) -> begin
(FStar_All.pipe_right vs (FStar_Util.for_some (fun v3 -> (check_ineq ((u1), (v3))))))
end
| uu____12545 -> begin
false
end)))
end))
in (

let uu____12548 = (FStar_All.pipe_right ineqs (FStar_Util.for_all (fun uu____12554 -> (match (uu____12554) with
| (u, v1) -> begin
(

let uu____12559 = (check_ineq ((u), (v1)))
in (match (uu____12559) with
| true -> begin
true
end
| uu____12560 -> begin
((

let uu____12562 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____12562) with
| true -> begin
(

let uu____12563 = (FStar_Syntax_Print.univ_to_string u)
in (

let uu____12564 = (FStar_Syntax_Print.univ_to_string v1)
in (FStar_Util.print2 "%s </= %s" uu____12563 uu____12564)))
end
| uu____12565 -> begin
()
end));
false;
)
end))
end))))
in (match (uu____12548) with
| true -> begin
()
end
| uu____12566 -> begin
((

let uu____12568 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____12568) with
| true -> begin
((

let uu____12570 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Partially solved inequality constraints are: %s\n" uu____12570));
(FStar_Unionfind.rollback tx);
(

let uu____12576 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Original solved inequality constraints are: %s\n" uu____12576));
)
end
| uu____12581 -> begin
()
end));
(

let uu____12582 = (

let uu____12583 = (

let uu____12586 = (FStar_TypeChecker_Env.get_range env)
in (("Failed to solve universe inequalities for inductives"), (uu____12586)))
in FStar_Errors.Error (uu____12583))
in (Prims.raise uu____12582));
)
end)))))))
end))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun env ineqs -> (

let tx = (FStar_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Unionfind.commit tx);
)))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail = (fun uu____12619 -> (match (uu____12619) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Errors.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in ((

let uu____12629 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____12629) with
| true -> begin
(

let uu____12630 = (wl_to_string wl)
in (

let uu____12631 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" uu____12630 uu____12631)))
end
| uu____12641 -> begin
()
end));
(

let g1 = (

let uu____12643 = (solve_and_commit env wl fail)
in (match (uu____12643) with
| Some ([]) -> begin
(

let uu___178_12650 = g
in {FStar_TypeChecker_Env.guard_f = uu___178_12650.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu___178_12650.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___178_12650.FStar_TypeChecker_Env.implicits})
end
| uu____12653 -> begin
(failwith "impossible: Unexpected deferred constraints remain")
end))
in ((solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___179_12656 = g1
in {FStar_TypeChecker_Env.guard_f = uu___179_12656.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___179_12656.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = uu___179_12656.FStar_TypeChecker_Env.implicits});
));
))))


let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun use_env_range_msg env g use_smt -> (

let g1 = (solve_deferred_constraints env g)
in (

let ret_g = (

let uu___180_12682 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___180_12682.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___180_12682.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___180_12682.FStar_TypeChecker_Env.implicits})
in (

let uu____12683 = (

let uu____12684 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12684)))
in (match (uu____12683) with
| true -> begin
Some (ret_g)
end
| uu____12686 -> begin
(match (g1.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((

let uu____12690 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Norm")))
in (match (uu____12690) with
| true -> begin
(

let uu____12691 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12692 = (

let uu____12693 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____12693))
in (FStar_Errors.diag uu____12691 uu____12692)))
end
| uu____12694 -> begin
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
| uu____12699 -> begin
((

let uu____12702 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12702) with
| true -> begin
(

let uu____12703 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12704 = (

let uu____12705 = (FStar_Syntax_Print.term_to_string vc2)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____12705))
in (FStar_Errors.diag uu____12703 uu____12704)))
end
| uu____12706 -> begin
()
end));
(

let vcs = (

let uu____12711 = (FStar_Options.use_tactics ())
in (match (uu____12711) with
| true -> begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.preprocess env vc2)
end
| uu____12715 -> begin
(((env), (vc2)))::[]
end))
in (FStar_All.pipe_right vcs (FStar_List.iter (fun uu____12725 -> (match (uu____12725) with
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

let uu____12736 = (discharge_guard' None env g true)
in (match (uu____12736) with
| Some (g1) -> begin
g1
end
| None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end)))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (

let uu____12756 = (FStar_Unionfind.find u)
in (match (uu____12756) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| uu____12765 -> begin
false
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____12780 = acc
in (match (uu____12780) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____12791 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd1)::tl1 -> begin
(

let uu____12826 = hd1
in (match (uu____12826) with
| (uu____12833, env, u, tm, k, r) -> begin
(

let uu____12839 = (unresolved u)
in (match (uu____12839) with
| true -> begin
(until_fixpoint (((hd1)::out), (changed)) tl1)
end
| uu____12853 -> begin
(

let env1 = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 tm)
in ((

let uu____12857 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("RelCheck")))
in (match (uu____12857) with
| true -> begin
(

let uu____12858 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____12862 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____12863 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" uu____12858 uu____12862 uu____12863))))
end
| uu____12864 -> begin
()
end));
(

let uu____12865 = (env1.FStar_TypeChecker_Env.type_of (

let uu___181_12869 = env1
in {FStar_TypeChecker_Env.solver = uu___181_12869.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___181_12869.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___181_12869.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___181_12869.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___181_12869.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___181_12869.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___181_12869.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___181_12869.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___181_12869.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___181_12869.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___181_12869.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___181_12869.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___181_12869.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___181_12869.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___181_12869.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___181_12869.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___181_12869.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___181_12869.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___181_12869.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___181_12869.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___181_12869.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___181_12869.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___181_12869.FStar_TypeChecker_Env.qname_and_index}) tm1)
in (match (uu____12865) with
| (uu____12870, uu____12871, g1) -> begin
(

let g2 = (match (env1.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___182_12874 = g1
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___182_12874.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___182_12874.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___182_12874.FStar_TypeChecker_Env.implicits})
end
| uu____12875 -> begin
g1
end)
in (

let g' = (

let uu____12877 = (discharge_guard' (Some ((fun uu____12881 -> (FStar_Syntax_Print.term_to_string tm1)))) env1 g2 true)
in (match (uu____12877) with
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

let uu___183_12896 = g
in (

let uu____12897 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___183_12896.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___183_12896.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___183_12896.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____12897})))))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g1 = (

let uu____12925 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____12925 resolve_implicits))
in (match (g1.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(

let uu____12932 = (discharge_guard env g1)
in (FStar_All.pipe_left Prims.ignore uu____12932))
end
| ((reason, uu____12934, uu____12935, e, t, r))::uu____12939 -> begin
(

let uu____12953 = (

let uu____12954 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____12955 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" uu____12954 uu____12955 reason)))
in (FStar_Errors.report r uu____12953))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___184_12962 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___184_12962.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___184_12962.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ((((u1), (u2)))::[])); FStar_TypeChecker_Env.implicits = uu___184_12962.FStar_TypeChecker_Env.implicits}))


let teq_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____12980 = (try_teq false env t1 t2)
in (match (uu____12980) with
| None -> begin
false
end
| Some (g) -> begin
(

let uu____12983 = (discharge_guard' None env g false)
in (match (uu____12983) with
| Some (uu____12987) -> begin
true
end
| None -> begin
false
end))
end)))





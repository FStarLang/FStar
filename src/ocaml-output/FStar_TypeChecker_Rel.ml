
open Prims

let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (

let uv = (FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(

let uv = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k))))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((uv), (uv)))
end
| uu____45 -> begin
(

let args = (FStar_All.pipe_right binders (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder))
in (

let k' = (

let uu____60 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders uu____60))
in (

let uv = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k'))))) None r)
in (

let uu____80 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((uv), (args))))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((uu____80), (uv))))))
end)))

type uvi =
| TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)


let uu___is_TERM : uvi  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TERM (_0) -> begin
true
end
| uu____120 -> begin
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
| uu____146 -> begin
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
| uu____226 -> begin
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
| uu____240 -> begin
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
| uu____257 -> begin
false
end))


let uu___is_CONTRAVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CONTRAVARIANT -> begin
true
end
| uu____261 -> begin
false
end))


let uu___is_INVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| INVARIANT -> begin
true
end
| uu____265 -> begin
false
end))


type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem


type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem


type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun uu___99_276 -> (match (uu___99_276) with
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

let uu____289 = (

let uu____290 = (FStar_Syntax_Subst.compress t)
in uu____290.FStar_Syntax_Syntax.n)
in (match (uu____289) with
| FStar_Syntax_Syntax.Tm_uvar (u, t) -> begin
(

let uu____307 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____311 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "(%s:%s)" uu____307 uu____311)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty); FStar_Syntax_Syntax.tk = uu____314; FStar_Syntax_Syntax.pos = uu____315; FStar_Syntax_Syntax.vars = uu____316}, args) -> begin
(

let uu____344 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____348 = (FStar_Syntax_Print.term_to_string ty)
in (

let uu____349 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "(%s:%s) %s" uu____344 uu____348 uu____349))))
end
| uu____350 -> begin
(FStar_Syntax_Print.term_to_string t)
end)))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env uu___100_356 -> (match (uu___100_356) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____360 = (

let uu____362 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____363 = (

let uu____365 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____366 = (

let uu____368 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (

let uu____369 = (

let uu____371 = (

let uu____373 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (

let uu____374 = (

let uu____376 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (

let uu____377 = (

let uu____379 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (

let uu____380 = (

let uu____382 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (uu____382)::[])
in (uu____379)::uu____380))
in (uu____376)::uu____377))
in (uu____373)::uu____374))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::uu____371)
in (uu____368)::uu____369))
in (uu____365)::uu____366))
in (uu____362)::uu____363))
in (FStar_Util.format "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" uu____360))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____387 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____388 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____387 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____388)))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env uu___101_394 -> (match (uu___101_394) with
| UNIV (u, t) -> begin
(

let x = (

let uu____398 = (FStar_Options.hide_uvar_nums ())
in (match (uu____398) with
| true -> begin
"?"
end
| uu____399 -> begin
(

let uu____400 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____400 FStar_Util.string_of_int))
end))
in (

let uu____402 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x uu____402)))
end
| TERM ((u, uu____404), t) -> begin
(

let x = (

let uu____409 = (FStar_Options.hide_uvar_nums ())
in (match (uu____409) with
| true -> begin
"?"
end
| uu____410 -> begin
(

let uu____411 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____411 FStar_Util.string_of_int))
end))
in (

let uu____415 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x uu____415)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (

let uu____424 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right uu____424 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (

let uu____432 = (

let uu____434 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right uu____434 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right uu____432 (FStar_String.concat ", "))))


let args_to_string = (fun args -> (

let uu____452 = (FStar_All.pipe_right args (FStar_List.map (fun uu____460 -> (match (uu____460) with
| (x, uu____464) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____452 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> (

let uu____469 = (

let uu____470 = (FStar_Options.eager_inference ())
in (not (uu____470)))
in {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = uu____469; smt_ok = true; tcenv = env}))


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let uu___128_483 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = uu___128_483.wl_deferred; ctr = uu___128_483.ctr; defer_ok = uu___128_483.defer_ok; smt_ok = smt_ok; tcenv = uu___128_483.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard = (fun env g -> (

let uu___129_508 = (empty_worklist env)
in (

let uu____509 = (FStar_List.map Prims.snd g)
in {attempting = uu____509; wl_deferred = uu___129_508.wl_deferred; ctr = uu___129_508.ctr; defer_ok = false; smt_ok = uu___129_508.smt_ok; tcenv = uu___129_508.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu___130_521 = wl
in {attempting = uu___130_521.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = uu___130_521.ctr; defer_ok = uu___130_521.defer_ok; smt_ok = uu___130_521.smt_ok; tcenv = uu___130_521.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let uu___131_533 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = uu___131_533.wl_deferred; ctr = uu___131_533.ctr; defer_ok = uu___131_533.defer_ok; smt_ok = uu___131_533.smt_ok; tcenv = uu___131_533.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> ((

let uu____544 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____544) with
| true -> begin
(

let uu____545 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason uu____545))
end
| uu____546 -> begin
()
end));
Failed (((prob), (reason)));
))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun uu___102_549 -> (match (uu___102_549) with
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

let uu___132_565 = p
in {FStar_TypeChecker_Common.pid = uu___132_565.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = uu___132_565.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___132_565.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___132_565.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___132_565.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___132_565.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___132_565.FStar_TypeChecker_Common.rank}))


let maybe_invert = (fun p -> (match ((p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV)) with
| true -> begin
(invert p)
end
| uu____583 -> begin
p
end))


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___103_586 -> (match (uu___103_586) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_28 -> FStar_TypeChecker_Common.TProb (_0_28)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_29 -> FStar_TypeChecker_Common.CProb (_0_29)))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel uu___104_602 -> (match (uu___104_602) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun uu___105_605 -> (match (uu___105_605) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun uu___106_614 -> (match (uu___106_614) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun uu___107_624 -> (match (uu___107_624) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun uu___108_634 -> (match (uu___108_634) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun uu___109_645 -> (match (uu___109_645) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun uu___110_656 -> (match (uu___110_656) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___111_665 -> (match (uu___111_665) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _0_30 -> FStar_TypeChecker_Common.TProb (_0_30)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _0_31 -> FStar_TypeChecker_Common.CProb (_0_31)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> (

let uu____679 = (FStar_All.pipe_right (p_reason p) FStar_List.length)
in (uu____679 = (Prims.parse_int "1"))))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____690 -> ((FStar_Util.incr ctr);
(FStar_ST.read ctr);
)))


let mk_problem = (fun scope orig lhs rel rhs elt reason -> (

let uu____740 = (next_pid ())
in (

let uu____741 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____740; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____741; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))


let new_problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (

let uu____788 = (next_pid ())
in (

let uu____789 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____788; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____789; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (

let uu____830 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____830; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))


let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (

let uu____878 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____878) with
| true -> begin
(

let uu____879 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (

let uu____880 = (prob_to_string env d)
in (

let uu____881 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" uu____879 uu____880 uu____881 s))))
end
| uu____883 -> begin
(

let d = (maybe_invert_p d)
in (

let rel = (match ((p_rel d)) with
| FStar_TypeChecker_Common.EQ -> begin
"equal to"
end
| FStar_TypeChecker_Common.SUB -> begin
"a subtype of"
end
| uu____886 -> begin
(failwith "impossible")
end)
in (

let uu____887 = (match (d) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____895 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (

let uu____896 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((uu____895), (uu____896))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____900 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (

let uu____901 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((uu____900), (uu____901))))
end)
in (match (uu____887) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___112_910 -> (match (uu___112_910) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| uu____917 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, uu____920), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun uu___113_943 -> (match (uu___113_943) with
| UNIV (uu____945) -> begin
None
end
| TERM ((u, uu____949), t) -> begin
(

let uu____953 = (FStar_Unionfind.equivalent uv u)
in (match (uu____953) with
| true -> begin
Some (t)
end
| uu____958 -> begin
None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun uu___114_972 -> (match (uu___114_972) with
| UNIV (u', t) -> begin
(

let uu____976 = (FStar_Unionfind.equivalent u u')
in (match (uu____976) with
| true -> begin
Some (t)
end
| uu____979 -> begin
None
end))
end
| uu____980 -> begin
None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____987 = (

let uu____988 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____988))
in (FStar_Syntax_Subst.compress uu____987)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____995 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress uu____995)))


let norm_arg = (fun env t -> (

let uu____1014 = (sn env (Prims.fst t))
in ((uu____1014), ((Prims.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____1031 -> (match (uu____1031) with
| (x, imp) -> begin
(

let uu____1038 = (

let uu___133_1039 = x
in (

let uu____1040 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___133_1039.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___133_1039.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1040}))
in ((uu____1038), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(

let uu____1055 = (aux u)
in FStar_Syntax_Syntax.U_succ (uu____1055))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1058 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____1058))
end
| uu____1060 -> begin
u
end)))
in (

let uu____1061 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1061))))


let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement = (fun env wl t1 -> (

let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(match (norm) with
| true -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| uu____1167 -> begin
(

let uu____1168 = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (match (uu____1168) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = uu____1180; FStar_Syntax_Syntax.pos = uu____1181; FStar_Syntax_Syntax.vars = uu____1182} -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| tt -> begin
(

let uu____1203 = (

let uu____1204 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____1205 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1204 uu____1205)))
in (failwith uu____1203))
end))
end)
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(match (norm) with
| true -> begin
((t1), (None))
end
| uu____1238 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (

let uu____1240 = (

let uu____1241 = (FStar_Syntax_Subst.compress t1')
in uu____1241.FStar_Syntax_Syntax.n)
in (match (uu____1240) with
| FStar_Syntax_Syntax.Tm_refine (uu____1253) -> begin
(aux true t1')
end
| uu____1258 -> begin
((t1), (None))
end)))
end)
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
((t1), (None))
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(

let uu____1293 = (

let uu____1294 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1295 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1294 uu____1295)))
in (failwith uu____1293))
end))
in (

let uu____1305 = (whnf env t1)
in (aux false uu____1305))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____1314 = (

let uu____1324 = (empty_worklist env)
in (base_and_refinement env uu____1324 t))
in (FStar_All.pipe_right uu____1314 Prims.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (

let uu____1348 = (FStar_Syntax_Syntax.null_bv t)
in ((uu____1348), (FStar_Syntax_Util.t_true))))


let as_refinement = (fun env wl t -> (

let uu____1368 = (base_and_refinement env wl t)
in (match (uu____1368) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement = (fun uu____1427 -> (match (uu____1427) with
| (t_base, refopt) -> begin
(

let uu____1441 = (match (refopt) with
| Some (y, phi) -> begin
((y), (phi))
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (uu____1441) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl uu___115_1465 -> (match (uu___115_1465) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____1469 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1470 = (

let uu____1471 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string uu____1471))
in (

let uu____1472 = (

let uu____1473 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string uu____1473))
in (FStar_Util.format4 "%s: %s  (%s)  %s" uu____1469 uu____1470 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1472))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____1477 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1478 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____1479 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" uu____1477 uu____1478 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1479))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (

let uu____1483 = (

let uu____1485 = (

let uu____1487 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____1497 -> (match (uu____1497) with
| (uu____1501, uu____1502, x) -> begin
x
end))))
in (FStar_List.append wl.attempting uu____1487))
in (FStar_List.map (wl_prob_to_string wl) uu____1485))
in (FStar_All.pipe_right uu____1483 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____1520 = (

let uu____1530 = (

let uu____1531 = (FStar_Syntax_Subst.compress k)
in uu____1531.FStar_Syntax_Syntax.n)
in (match (uu____1530) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (((FStar_List.length bs) = (FStar_List.length ys))) with
| true -> begin
(

let uu____1572 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (uu____1572)))
end
| uu____1585 -> begin
(

let uu____1586 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____1586) with
| (ys', t, uu____1607) -> begin
(

let uu____1620 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t))), (uu____1620)))
end))
end)
end
| uu____1641 -> begin
(

let uu____1642 = (

let uu____1648 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____1648)))
in ((((ys), (t))), (uu____1642)))
end))
in (match (uu____1520) with
| ((ys, t), (xs, c)) -> begin
(match (((FStar_List.length xs) <> (FStar_List.length ys))) with
| true -> begin
(FStar_Syntax_Util.abs ys t (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ([]))))))
end
| uu____1701 -> begin
(

let c = (

let uu____1703 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp uu____1703 c))
in (

let uu____1705 = (

let uu____1712 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_32 -> FStar_Util.Inl (_0_32)))
in (FStar_All.pipe_right uu____1712 (fun _0_33 -> Some (_0_33))))
in (FStar_Syntax_Util.abs ys t uu____1705)))
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

let uu____1763 = (p_guard prob)
in (match (uu____1763) with
| (uu____1766, uv) -> begin
((

let uu____1769 = (

let uu____1770 = (FStar_Syntax_Subst.compress uv)
in uu____1770.FStar_Syntax_Syntax.n)
in (match (uu____1769) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi = (u_abs k bs phi)
in ((

let uu____1790 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____1790) with
| true -> begin
(

let uu____1791 = (FStar_Util.string_of_int (p_pid prob))
in (

let uu____1792 = (FStar_Syntax_Print.term_to_string uv)
in (

let uu____1793 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" uu____1791 uu____1792 uu____1793))))
end
| uu____1794 -> begin
()
end));
(FStar_Syntax_Util.set_uvar uvar phi);
)))
end
| uu____1797 -> begin
(match ((not (resolve_ok))) with
| true -> begin
(failwith "Impossible: this instance has already been assigned a solution")
end
| uu____1798 -> begin
()
end)
end));
(commit uvis);
(

let uu___134_1800 = wl
in {attempting = uu___134_1800.attempting; wl_deferred = uu___134_1800.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___134_1800.defer_ok; smt_ok = uu___134_1800.smt_ok; tcenv = uu___134_1800.tcenv});
)
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____1813 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____1813) with
| true -> begin
(

let uu____1814 = (FStar_Util.string_of_int pid)
in (

let uu____1815 = (

let uu____1816 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right uu____1816 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____1814 uu____1815)))
end
| uu____1819 -> begin
()
end));
(commit sol);
(

let uu___135_1821 = wl
in {attempting = uu___135_1821.attempting; wl_deferred = uu___135_1821.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___135_1821.defer_ok; smt_ok = uu___135_1821.smt_ok; tcenv = uu___135_1821.tcenv});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard = (fun t g -> (match (((t), (g))) with
| (uu____1850, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(

let uu____1858 = (FStar_Syntax_Util.mk_conj t f)
in Some (uu____1858))
end))
in ((

let uu____1864 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____1864) with
| true -> begin
(

let uu____1865 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (

let uu____1866 = (

let uu____1867 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right uu____1867 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____1865 uu____1866)))
end
| uu____1870 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
)))


let rec occurs = (fun wl uk t -> (

let uu____1892 = (

let uu____1896 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right uu____1896 FStar_Util.set_elements))
in (FStar_All.pipe_right uu____1892 (FStar_Util.for_some (fun uu____1917 -> (match (uu____1917) with
| (uv, uu____1925) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (

let uu____1969 = (occurs wl uk t)
in (not (uu____1969)))
in (

let msg = (match (occurs_ok) with
| true -> begin
None
end
| uu____1973 -> begin
(

let uu____1974 = (

let uu____1975 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (

let uu____1979 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" uu____1975 uu____1979)))
in Some (uu____1974))
end)
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let uu____2027 = (occurs_check env wl uk t)
in (match (uu____2027) with
| (occurs_ok, msg) -> begin
(

let uu____2044 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (uu____2044), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set v1)
in (

let uu____2108 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____2132 uu____2133 -> (match (((uu____2132), (uu____2133))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____2176 = (

let uu____2177 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation uu____2177))
in (match (uu____2176) with
| true -> begin
((isect), (isect_set))
end
| uu____2188 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____2191 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____2191) with
| true -> begin
(

let uu____2198 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (uu____2198)))
end
| uu____2206 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (uu____2108) with
| (isect, uu____2220) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____2269 uu____2270 -> (match (((uu____2269), (uu____2270))) with
| ((a, uu____2280), (b, uu____2282)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(

let uu____2326 = (FStar_All.pipe_right seen (FStar_Util.for_some (fun uu____2332 -> (match (uu____2332) with
| (b, uu____2336) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end))))
in (match (uu____2326) with
| true -> begin
None
end
| uu____2342 -> begin
Some (((a), ((Prims.snd hd))))
end))
end
| uu____2345 -> begin
None
end)))


let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| (hd)::rest -> begin
(

let uu____2388 = (pat_var_opt env seen hd)
in (match (uu____2388) with
| None -> begin
((

let uu____2396 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____2396) with
| true -> begin
(

let uu____2397 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" uu____2397))
end
| uu____2398 -> begin
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

let uu____2409 = (

let uu____2410 = (FStar_Syntax_Subst.compress t)
in uu____2410.FStar_Syntax_Syntax.n)
in (match (uu____2409) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
true
end
| uu____2426 -> begin
false
end)))


let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = uu____2488; FStar_Syntax_Syntax.pos = uu____2489; FStar_Syntax_Syntax.vars = uu____2490}, args) -> begin
((t), (uv), (k), (args))
end
| uu____2531 -> begin
(failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let uu____2585 = (destruct_flex_t t)
in (match (uu____2585) with
| (t, uv, k, args) -> begin
(

let uu____2653 = (pat_vars env [] args)
in (match (uu____2653) with
| Some (vars) -> begin
((((t), (uv), (k), (args))), (Some (vars)))
end
| uu____2709 -> begin
((((t), (uv), (k), (args))), (None))
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
| uu____2757 -> begin
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
| uu____2780 -> begin
false
end))


let uu___is_FullMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullMatch -> begin
true
end
| uu____2784 -> begin
false
end))


let head_match : match_result  ->  match_result = (fun uu___116_2787 -> (match (uu___116_2787) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____2796 -> begin
HeadMatch
end))


let fv_delta_depth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.delta_depth = (fun env fv -> (match (fv.FStar_Syntax_Syntax.fv_delta) with
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(match ((env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)) with
| true -> begin
d
end
| uu____2808 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
end
| d -> begin
d
end))


let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth Prims.option = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
None
end
| (FStar_Syntax_Syntax.Tm_uinst (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) | (FStar_Syntax_Syntax.Tm_app (t, _)) | (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}, _)) -> begin
(delta_depth_of_term env t)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
Some ((fv_delta_depth env fv))
end)))


let rec head_matches : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  match_result = (fun env t1 t2 -> (

let t1 = (FStar_Syntax_Util.unmeta t1)
in (

let t2 = (FStar_Syntax_Util.unmeta t2)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_name (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(match ((FStar_Syntax_Syntax.bv_eq x y)) with
| true -> begin
FullMatch
end
| uu____2881 -> begin
MisMatch (((None), (None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____2886 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____2886) with
| true -> begin
FullMatch
end
| uu____2887 -> begin
MisMatch (((Some ((fv_delta_depth env f))), (Some ((fv_delta_depth env g)))))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____2891), FStar_Syntax_Syntax.Tm_uinst (g, uu____2893)) -> begin
(

let uu____2902 = (head_matches env f g)
in (FStar_All.pipe_right uu____2902 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(match ((c = d)) with
| true -> begin
FullMatch
end
| uu____2905 -> begin
MisMatch (((None), (None)))
end)
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, uu____2909), FStar_Syntax_Syntax.Tm_uvar (uv', uu____2911)) -> begin
(

let uu____2936 = (FStar_Unionfind.equivalent uv uv')
in (match (uu____2936) with
| true -> begin
FullMatch
end
| uu____2940 -> begin
MisMatch (((None), (None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____2944), FStar_Syntax_Syntax.Tm_refine (y, uu____2946)) -> begin
(

let uu____2955 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____2955 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____2957), uu____2958) -> begin
(

let uu____2963 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right uu____2963 head_match))
end
| (uu____2964, FStar_Syntax_Syntax.Tm_refine (x, uu____2966)) -> begin
(

let uu____2971 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____2971 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, uu____2977), FStar_Syntax_Syntax.Tm_app (head', uu____2979)) -> begin
(

let uu____3008 = (head_matches env head head')
in (FStar_All.pipe_right uu____3008 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head, uu____3010), uu____3011) -> begin
(

let uu____3026 = (head_matches env head t2)
in (FStar_All.pipe_right uu____3026 head_match))
end
| (uu____3027, FStar_Syntax_Syntax.Tm_app (head, uu____3029)) -> begin
(

let uu____3044 = (head_matches env t1 head)
in (FStar_All.pipe_right uu____3044 head_match))
end
| uu____3045 -> begin
(

let uu____3048 = (

let uu____3053 = (delta_depth_of_term env t1)
in (

let uu____3055 = (delta_depth_of_term env t2)
in ((uu____3053), (uu____3055))))
in MisMatch (uu____3048))
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let uu____3091 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____3091) with
| (head, uu____3103) -> begin
(

let uu____3118 = (

let uu____3119 = (FStar_Syntax_Util.un_uinst head)
in uu____3119.FStar_Syntax_Syntax.n)
in (match (uu____3118) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3124 = (

let uu____3125 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3125 FStar_Option.isSome))
in (match (uu____3124) with
| true -> begin
(

let uu____3139 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right uu____3139 (fun _0_34 -> Some (_0_34))))
end
| uu____3141 -> begin
None
end))
end
| uu____3142 -> begin
None
end))
end)))
in (

let success = (fun d r t1 t2 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
Some (((t1), (t2)))
end
| uu____3169 -> begin
None
end))))
in (

let fail = (fun r -> ((r), (None)))
in (

let rec aux = (fun retry n_delta t1 t2 -> (

let r = (head_matches env t1 t2)
in (match (r) with
| (MisMatch (Some (FStar_Syntax_Syntax.Delta_equational), _)) | (MisMatch (_, Some (FStar_Syntax_Syntax.Delta_equational))) -> begin
(match ((not (retry))) with
| true -> begin
(fail r)
end
| uu____3221 -> begin
(

let uu____3222 = (

let uu____3227 = (maybe_inline t1)
in (

let uu____3229 = (maybe_inline t2)
in ((uu____3227), (uu____3229))))
in (match (uu____3222) with
| (None, None) -> begin
(fail r)
end
| (Some (t1), None) -> begin
(aux false (n_delta + (Prims.parse_int "1")) t1 t2)
end
| (None, Some (t2)) -> begin
(aux false (n_delta + (Prims.parse_int "1")) t1 t2)
end
| (Some (t1), Some (t2)) -> begin
(aux false (n_delta + (Prims.parse_int "1")) t1 t2)
end))
end)
end
| MisMatch (Some (d1), Some (d2)) when (d1 = d2) -> begin
(

let uu____3254 = (FStar_TypeChecker_Common.decr_delta_depth d1)
in (match (uu____3254) with
| None -> begin
(fail r)
end
| Some (d) -> begin
(

let t1 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (

let t2 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (aux retry (n_delta + (Prims.parse_int "1")) t1 t2)))
end))
end
| MisMatch (Some (d1), Some (d2)) -> begin
(

let d1_greater_than_d2 = (FStar_TypeChecker_Common.delta_depth_greater_than d1 d2)
in (

let uu____3269 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in ((t1'), (t2)))
end
| uu____3275 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (

let uu____3277 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in ((t1), (uu____3277))))
end)
in (match (uu____3269) with
| (t1, t2) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t1 t2)
end)))
end
| MisMatch (uu____3285) -> begin
(fail r)
end
| uu____3290 -> begin
(success n_delta r t1 t2)
end)))
in (aux true (Prims.parse_int "0") t1 t2))))))

type tc =
| T of (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term))
| C of FStar_Syntax_Syntax.comp


let uu___is_T : tc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| T (_0) -> begin
true
end
| uu____3315 -> begin
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
| uu____3345 -> begin
false
end))


let __proj__C__item___0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_0) -> begin
_0
end))


type tcs =
tc Prims.list


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____3360 = (FStar_Syntax_Util.type_u ())
in (match (uu____3360) with
| (t, uu____3364) -> begin
(

let uu____3365 = (new_uvar r binders t)
in (Prims.fst uu____3365))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____3374 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____3374 Prims.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (

let uu____3416 = (head_matches env t t')
in (match (uu____3416) with
| MisMatch (uu____3417) -> begin
false
end
| uu____3422 -> begin
true
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(

let rebuild = (fun args' -> (

let args = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((uu____3482, imp), T (t, uu____3485)) -> begin
((t), (imp))
end
| uu____3502 -> begin
(failwith "Bad reconstruction")
end)) args args')
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), (args))))) None t.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun uu____3546 -> (match (uu____3546) with
| (t, uu____3554) -> begin
((None), (INVARIANT), (T (((t), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let fail = (fun uu____3587 -> (failwith "Bad reconstruction"))
in (

let uu____3588 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3588) with
| (bs, c) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs tcs -> (match (((bs), (tcs))) with
| (((x, imp))::bs, (T (t, uu____3641))::tcs) -> begin
(aux (((((

let uu___136_3663 = x
in {FStar_Syntax_Syntax.ppname = uu___136_3663.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___136_3663.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp)))::out) bs tcs)
end
| ([], (C (c))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| uu____3673 -> begin
(failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (

let rec decompose = (fun out uu___117_3704 -> (match (uu___117_3704) with
| [] -> begin
(FStar_List.rev ((((None), (COVARIANT), (C (c))))::out))
end
| (hd)::rest -> begin
(decompose ((((Some (hd)), (CONTRAVARIANT), (T ((((Prims.fst hd).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (

let uu____3767 = (decompose [] bs)
in ((rebuild), (matches), (uu____3767)))))
end)))
end
| uu____3795 -> begin
(

let rebuild = (fun uu___118_3800 -> (match (uu___118_3800) with
| [] -> begin
t
end
| uu____3802 -> begin
(failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t -> true)), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun uu___119_3821 -> (match (uu___119_3821) with
| T (t, uu____3823) -> begin
t
end
| uu____3832 -> begin
(failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun uu___120_3835 -> (match (uu___120_3835) with
| T (t, uu____3837) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| uu____3846 -> begin
(failwith "Impossible")
end))


let imitation_sub_probs = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope args q -> (match (q) with
| (uu____3927, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope r)
in (

let uu____3946 = (new_uvar r scope k)
in (match (uu____3946) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| uu____3958 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) None r)
end)
in (

let uu____3973 = (

let uu____3974 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _0_35 -> FStar_TypeChecker_Common.TProb (_0_35)) uu____3974))
in ((T (((gi_xs), (mk_kind)))), (uu____3973))))
end)))
end
| (uu____3983, uu____3984, C (uu____3985)) -> begin
(failwith "impos")
end))
in (

let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs -> begin
(

let uu____4072 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.tk = uu____4083; FStar_Syntax_Syntax.pos = uu____4084; FStar_Syntax_Syntax.vars = uu____4085})) -> begin
(

let uu____4100 = (sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____4100) with
| (T (gi_xs, uu____4116), prob) -> begin
(

let uu____4126 = (

let uu____4127 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_36 -> C (_0_36)) uu____4127))
in ((uu____4126), ((prob)::[])))
end
| uu____4129 -> begin
(failwith "impossible")
end))
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.tk = uu____4139; FStar_Syntax_Syntax.pos = uu____4140; FStar_Syntax_Syntax.vars = uu____4141})) -> begin
(

let uu____4156 = (sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____4156) with
| (T (gi_xs, uu____4172), prob) -> begin
(

let uu____4182 = (

let uu____4183 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_37 -> C (_0_37)) uu____4183))
in ((uu____4182), ((prob)::[])))
end
| uu____4185 -> begin
(failwith "impossible")
end))
end
| (uu____4191, uu____4192, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = uu____4194; FStar_Syntax_Syntax.pos = uu____4195; FStar_Syntax_Syntax.vars = uu____4196})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((None), (INVARIANT), (T ((((Prims.fst t)), (generic_kind))))))))
in (

let components = (((None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let uu____4270 = (

let uu____4275 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right uu____4275 FStar_List.unzip))
in (match (uu____4270) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (

let uu____4304 = (

let uu____4305 = (

let uu____4308 = (FStar_List.hd tcs)
in (FStar_All.pipe_right uu____4308 un_T))
in (

let uu____4309 = (

let uu____4315 = (FStar_List.tl tcs)
in (FStar_All.pipe_right uu____4315 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____4305; FStar_Syntax_Syntax.effect_args = uu____4309; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____4304))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| uu____4320 -> begin
(

let uu____4327 = (sub_prob scope args q)
in (match (uu____4327) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (uu____4072) with
| (tc, probs) -> begin
(

let uu____4345 = (match (q) with
| (Some (b), uu____4371, uu____4372) -> begin
(

let uu____4380 = (

let uu____4384 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (uu____4384)::args)
in ((Some (b)), ((b)::scope), (uu____4380)))
end
| uu____4402 -> begin
((None), (scope), (args))
end)
in (match (uu____4345) with
| (bopt, scope, args) -> begin
(

let uu____4445 = (aux scope args qs)
in (match (uu____4445) with
| (sub_probs, tcs, f) -> begin
(

let f = (match (bopt) with
| None -> begin
(

let uu____4466 = (

let uu____4468 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::uu____4468)
in (FStar_Syntax_Util.mk_conj_l uu____4466))
end
| Some (b) -> begin
(

let uu____4480 = (

let uu____4482 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (

let uu____4485 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (uu____4482)::uu____4485))
in (FStar_Syntax_Util.mk_conj_l uu____4480))
end)
in (((FStar_List.append probs sub_probs)), ((tc)::tcs), (f)))
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

let uu___137_4542 = p
in (

let uu____4545 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____4546 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___137_4542.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____4545; FStar_TypeChecker_Common.relation = uu___137_4542.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____4546; FStar_TypeChecker_Common.element = uu___137_4542.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___137_4542.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___137_4542.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___137_4542.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___137_4542.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___137_4542.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____4556 = (compress_tprob wl p)
in (FStar_All.pipe_right uu____4556 (fun _0_38 -> FStar_TypeChecker_Common.TProb (_0_38))))
end
| FStar_TypeChecker_Common.CProb (uu____4561) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (

let uu____4575 = (compress_prob wl pr)
in (FStar_All.pipe_right uu____4575 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____4581 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____4581) with
| (lh, uu____4594) -> begin
(

let uu____4609 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____4609) with
| (rh, uu____4622) -> begin
(

let uu____4637 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____4646), FStar_Syntax_Syntax.Tm_uvar (uu____4647)) -> begin
((flex_flex), (tp))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when ((tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____4672), uu____4673) -> begin
(

let uu____4682 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (uu____4682) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((flex_rigid), (tp))
end
| uu____4722 -> begin
(

let rank = (

let uu____4729 = (is_top_level_prob prob)
in (match (uu____4729) with
| true -> begin
flex_refine
end
| uu____4730 -> begin
flex_refine_inner
end))
in (

let uu____4731 = (

let uu___138_4734 = tp
in (

let uu____4737 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___138_4734.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___138_4734.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___138_4734.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____4737; FStar_TypeChecker_Common.element = uu___138_4734.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___138_4734.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___138_4734.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___138_4734.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___138_4734.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___138_4734.FStar_TypeChecker_Common.rank}))
in ((rank), (uu____4731))))
end)
end))
end
| (uu____4747, FStar_Syntax_Syntax.Tm_uvar (uu____4748)) -> begin
(

let uu____4757 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (uu____4757) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((rigid_flex), (tp))
end
| uu____4797 -> begin
(

let uu____4803 = (

let uu___139_4808 = tp
in (

let uu____4811 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___139_4808.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____4811; FStar_TypeChecker_Common.relation = uu___139_4808.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___139_4808.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___139_4808.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___139_4808.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___139_4808.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___139_4808.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___139_4808.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___139_4808.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (uu____4803)))
end)
end))
end
| (uu____4827, uu____4828) -> begin
((rigid_rigid), (tp))
end)
in (match (uu____4637) with
| (rank, tp) -> begin
(

let uu____4839 = (FStar_All.pipe_right (

let uu___140_4842 = tp
in {FStar_TypeChecker_Common.pid = uu___140_4842.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___140_4842.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___140_4842.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___140_4842.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___140_4842.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___140_4842.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___140_4842.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___140_4842.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___140_4842.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _0_39 -> FStar_TypeChecker_Common.TProb (_0_39)))
in ((rank), (uu____4839)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____4848 = (FStar_All.pipe_right (

let uu___141_4851 = cp
in {FStar_TypeChecker_Common.pid = uu___141_4851.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___141_4851.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___141_4851.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___141_4851.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___141_4851.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___141_4851.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___141_4851.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___141_4851.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___141_4851.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _0_40 -> FStar_TypeChecker_Common.CProb (_0_40)))
in ((rigid_rigid), (uu____4848)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun uu____4883 probs -> (match (uu____4883) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
((min), (out), (min_rank))
end
| (hd)::tl -> begin
(

let uu____4913 = (rank wl hd)
in (match (uu____4913) with
| (rank, hd) -> begin
(match ((rank <= flex_rigid_eq)) with
| true -> begin
(match (min) with
| None -> begin
((Some (hd)), ((FStar_List.append out tl)), (rank))
end
| Some (m) -> begin
((Some (hd)), ((FStar_List.append out ((m)::tl))), (rank))
end)
end
| uu____4938 -> begin
(match ((rank < min_rank)) with
| true -> begin
(match (min) with
| None -> begin
(aux ((rank), (Some (hd)), (out)) tl)
end
| Some (m) -> begin
(aux ((rank), (Some (hd)), ((m)::out)) tl)
end)
end
| uu____4954 -> begin
(aux ((min_rank), (min), ((hd)::out)) tl)
end)
end)
end))
end)
end))
in (aux (((flex_flex + (Prims.parse_int "1"))), (None), ([])) wl.attempting)))


let is_flex_rigid : Prims.int  ->  Prims.bool = (fun rank -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))


let is_rigid_flex : Prims.int  ->  Prims.bool = (fun rank -> ((rigid_flex <= rank) && (rank <= refine_flex)))

type univ_eq_sol =
| UDeferred of worklist
| USolved of worklist
| UFailed of Prims.string


let uu___is_UDeferred : univ_eq_sol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UDeferred (_0) -> begin
true
end
| uu____4978 -> begin
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
| uu____4990 -> begin
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
| uu____5002 -> begin
false
end))


let __proj__UFailed__item___0 : univ_eq_sol  ->  Prims.string = (fun projectee -> (match (projectee) with
| UFailed (_0) -> begin
_0
end))


let rec really_solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (

let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (

let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (

let uu____5039 = (FStar_Syntax_Util.univ_kernel u)
in (match (uu____5039) with
| (k, uu____5043) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| uu____5048 -> begin
false
end)
end)))))
end
| uu____5049 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (

let try_umax_components = (fun u1 u2 msg -> (match (((u1), (u2))) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(match (((FStar_List.length us1) = (FStar_List.length us2))) with
| true -> begin
(

let rec aux = (fun wl us1 us2 -> (match (((us1), (us2))) with
| ((u1)::us1, (u2)::us2) -> begin
(

let uu____5092 = (really_solve_universe_eq orig wl u1 u2)
in (match (uu____5092) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed -> begin
failed
end))
end
| uu____5095 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end
| uu____5100 -> begin
(

let uu____5101 = (

let uu____5102 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____5103 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" uu____5102 uu____5103)))
in UFailed (uu____5101))
end)
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(

let rec aux = (fun wl us -> (match (us) with
| [] -> begin
USolved (wl)
end
| (u)::us -> begin
(

let uu____5120 = (really_solve_universe_eq orig wl u u')
in (match (uu____5120) with
| USolved (wl) -> begin
(aux wl us)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____5123 -> begin
(

let uu____5126 = (

let uu____5127 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____5128 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" uu____5127 uu____5128 msg)))
in UFailed (uu____5126))
end))
in (match (((u1), (u2))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(

let uu____5135 = (

let uu____5136 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____5137 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____5136 uu____5137)))
in (failwith uu____5135))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((x.FStar_Ident.idText = y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____5140 -> begin
UFailed ("Incompatible universes")
end)
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
USolved (wl)
end
| (FStar_Syntax_Syntax.U_succ (u1), FStar_Syntax_Syntax.U_succ (u2)) -> begin
(really_solve_universe_eq orig wl u1 u2)
end
| (FStar_Syntax_Syntax.U_unif (v1), FStar_Syntax_Syntax.U_unif (v2)) -> begin
(

let uu____5149 = (FStar_Unionfind.equivalent v1 v2)
in (match (uu____5149) with
| true -> begin
USolved (wl)
end
| uu____5151 -> begin
(

let wl = (extend_solution orig ((UNIV (((v1), (u2))))::[]) wl)
in USolved (wl))
end))
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(

let u = (norm_univ wl u)
in (

let uu____5162 = (occurs_univ v1 u)
in (match (uu____5162) with
| true -> begin
(

let uu____5163 = (

let uu____5164 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____5165 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____5164 uu____5165)))
in (try_umax_components u1 u2 uu____5163))
end
| uu____5166 -> begin
(

let uu____5167 = (extend_solution orig ((UNIV (((v1), (u))))::[]) wl)
in USolved (uu____5167))
end)))
end
| ((FStar_Syntax_Syntax.U_max (_), _)) | ((_, FStar_Syntax_Syntax.U_max (_))) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____5174 -> begin
(

let u1 = (norm_univ wl u1)
in (

let u2 = (norm_univ wl u2)
in (

let uu____5177 = (FStar_Syntax_Util.eq_univs u1 u2)
in (match (uu____5177) with
| true -> begin
USolved (wl)
end
| uu____5178 -> begin
(try_umax_components u1 u2 "")
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
| uu____5199 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders = (fun bc1 bc2 -> (

let uu____5248 = bc1
in (match (uu____5248) with
| (bs1, mk_cod1) -> begin
(

let uu____5273 = bc2
in (match (uu____5273) with
| (bs2, mk_cod2) -> begin
(

let curry = (fun n bs mk_cod -> (

let uu____5320 = (FStar_Util.first_N n bs)
in (match (uu____5320) with
| (bs, rest) -> begin
(

let uu____5334 = (mk_cod rest)
in ((bs), (uu____5334)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(

let uu____5352 = (

let uu____5356 = (mk_cod1 [])
in ((bs1), (uu____5356)))
in (

let uu____5358 = (

let uu____5362 = (mk_cod2 [])
in ((bs2), (uu____5362)))
in ((uu____5352), (uu____5358))))
end
| uu____5370 -> begin
(match ((l1 > l2)) with
| true -> begin
(

let uu____5384 = (curry l2 bs1 mk_cod1)
in (

let uu____5391 = (

let uu____5395 = (mk_cod2 [])
in ((bs2), (uu____5395)))
in ((uu____5384), (uu____5391))))
end
| uu____5403 -> begin
(

let uu____5404 = (

let uu____5408 = (mk_cod1 [])
in ((bs1), (uu____5408)))
in (

let uu____5410 = (curry l1 bs2 mk_cod2)
in ((uu____5404), (uu____5410))))
end)
end))))
end))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____5514 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5514) with
| true -> begin
(

let uu____5515 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" uu____5515))
end
| uu____5516 -> begin
()
end));
(

let uu____5517 = (next_prob probs)
in (match (uu____5517) with
| (Some (hd), tl, rank) -> begin
(

let probs = (

let uu___142_5530 = probs
in {attempting = tl; wl_deferred = uu___142_5530.wl_deferred; ctr = uu___142_5530.ctr; defer_ok = uu___142_5530.defer_ok; smt_ok = uu___142_5530.smt_ok; tcenv = uu___142_5530.tcenv})
in (match (hd) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match ((((not (probs.defer_ok)) && (flex_refine_inner <= rank)) && (rank <= flex_rigid))) with
| true -> begin
(

let uu____5537 = (solve_flex_rigid_join env tp probs)
in (match (uu____5537) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end))
end
| uu____5540 -> begin
(match ((((not (probs.defer_ok)) && (rigid_flex <= rank)) && (rank <= refine_flex))) with
| true -> begin
(

let uu____5541 = (solve_rigid_flex_meet env tp probs)
in (match (uu____5541) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end))
end
| uu____5544 -> begin
(solve_t' env (maybe_invert tp) probs)
end)
end)
end))
end
| (None, uu____5545, uu____5546) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| uu____5555 -> begin
(

let uu____5560 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____5588 -> (match (uu____5588) with
| (c, uu____5593, uu____5594) -> begin
(c < probs.ctr)
end))))
in (match (uu____5560) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(

let uu____5616 = (FStar_List.map (fun uu____5622 -> (match (uu____5622) with
| (uu____5628, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (uu____5616))
end
| uu____5631 -> begin
(

let uu____5636 = (

let uu___143_5637 = probs
in (

let uu____5638 = (FStar_All.pipe_right attempt (FStar_List.map (fun uu____5647 -> (match (uu____5647) with
| (uu____5651, uu____5652, y) -> begin
y
end))))
in {attempting = uu____5638; wl_deferred = rest; ctr = uu___143_5637.ctr; defer_ok = uu___143_5637.defer_ok; smt_ok = uu___143_5637.smt_ok; tcenv = uu___143_5637.tcenv}))
in (solve env uu____5636))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____5659 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____5659) with
| USolved (wl) -> begin
(

let uu____5661 = (solve_prob orig None [] wl)
in (solve env uu____5661))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end)))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (

let rec aux = (fun wl us1 us2 -> (match (((us1), (us2))) with
| ([], []) -> begin
USolved (wl)
end
| ((u1)::us1, (u2)::us2) -> begin
(

let uu____5695 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____5695) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____5698 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t1 = (whnf env t1)
in (

let t2 = (whnf env t2)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = uu____5706; FStar_Syntax_Syntax.pos = uu____5707; FStar_Syntax_Syntax.vars = uu____5708}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = uu____5711; FStar_Syntax_Syntax.pos = uu____5712; FStar_Syntax_Syntax.vars = uu____5713}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____5729 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____5737 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____5737) with
| true -> begin
(

let uu____5738 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" uu____5738 msg))
end
| uu____5739 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____5740 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> ((

let uu____5746 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5746) with
| true -> begin
(

let uu____5747 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" uu____5747))
end
| uu____5748 -> begin
()
end));
(

let uu____5749 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____5749) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let uu____5791 = (head_matches_delta env () t1 t2)
in (match (uu____5791) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (uu____5813) -> begin
None
end
| FullMatch -> begin
(match (ts) with
| None -> begin
Some (((t1), ([])))
end
| Some (t1, t2) -> begin
Some (((t1), ([])))
end)
end
| HeadMatch -> begin
(

let uu____5839 = (match (ts) with
| Some (t1, t2) -> begin
(

let uu____5848 = (FStar_Syntax_Subst.compress t1)
in (

let uu____5849 = (FStar_Syntax_Subst.compress t2)
in ((uu____5848), (uu____5849))))
end
| None -> begin
(

let uu____5852 = (FStar_Syntax_Subst.compress t1)
in (

let uu____5853 = (FStar_Syntax_Subst.compress t2)
in ((uu____5852), (uu____5853))))
end)
in (match (uu____5839) with
| (t1, t2) -> begin
(

let eq_prob = (fun t1 t2 -> (

let uu____5875 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _0_41 -> FStar_TypeChecker_Common.TProb (_0_41)) uu____5875)))
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(

let uu____5898 = (

let uu____5904 = (

let uu____5907 = (

let uu____5910 = (

let uu____5911 = (

let uu____5916 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (uu____5916)))
in FStar_Syntax_Syntax.Tm_refine (uu____5911))
in (FStar_Syntax_Syntax.mk uu____5910))
in (uu____5907 None t1.FStar_Syntax_Syntax.pos))
in (

let uu____5929 = (

let uu____5931 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (uu____5931)::[])
in ((uu____5904), (uu____5929))))
in Some (uu____5898))
end
| (uu____5940, FStar_Syntax_Syntax.Tm_refine (x, uu____5942)) -> begin
(

let uu____5947 = (

let uu____5951 = (

let uu____5953 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (uu____5953)::[])
in ((t1), (uu____5951)))
in Some (uu____5947))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____5959), uu____5960) -> begin
(

let uu____5965 = (

let uu____5969 = (

let uu____5971 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (uu____5971)::[])
in ((t2), (uu____5969)))
in Some (uu____5965))
end
| uu____5976 -> begin
(

let uu____5979 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____5979) with
| (head1, uu____5994) -> begin
(

let uu____6009 = (

let uu____6010 = (FStar_Syntax_Util.un_uinst head1)
in uu____6010.FStar_Syntax_Syntax.n)
in (match (uu____6009) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____6017; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (i); FStar_Syntax_Syntax.fv_qual = uu____6019}) -> begin
(

let prev = (match ((i > (Prims.parse_int "1"))) with
| true -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i - (Prims.parse_int "1")))
end
| uu____6025 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t1)
in (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t2)
in (disjoin t1 t2))))
end
| uu____6028 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____6037) -> begin
(

let uu____6050 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___121_6059 -> (match (uu___121_6059) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(

let uu____6064 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____6064) with
| (u', uu____6075) -> begin
(

let uu____6090 = (

let uu____6091 = (whnf env u')
in uu____6091.FStar_Syntax_Syntax.n)
in (match (uu____6090) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____6095) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____6111 -> begin
false
end))
end))
end
| uu____6112 -> begin
false
end)
end
| uu____6114 -> begin
false
end))))
in (match (uu____6050) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun uu____6135 tps -> (match (uu____6135) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(

let uu____6162 = (

let uu____6167 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound uu____6167))
in (match (uu____6162) with
| Some (bound, sub) -> begin
(make_lower_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end))
end
| uu____6186 -> begin
None
end)
end))
in (

let uu____6191 = (

let uu____6196 = (

let uu____6200 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((uu____6200), ([])))
in (make_lower_bound uu____6196 lower_bounds))
in (match (uu____6191) with
| None -> begin
((

let uu____6207 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6207) with
| true -> begin
(FStar_Util.print_string "No lower bounds\n")
end
| uu____6208 -> begin
()
end));
None;
)
end
| Some (lhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in ((

let uu____6220 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6220) with
| true -> begin
(

let wl' = (

let uu___144_6222 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___144_6222.wl_deferred; ctr = uu___144_6222.ctr; defer_ok = uu___144_6222.defer_ok; smt_ok = uu___144_6222.smt_ok; tcenv = uu___144_6222.tcenv})
in (

let uu____6223 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" uu____6223)))
end
| uu____6224 -> begin
()
end));
(

let uu____6225 = (solve_t env eq_prob (

let uu___145_6226 = wl
in {attempting = sub_probs; wl_deferred = uu___145_6226.wl_deferred; ctr = uu___145_6226.ctr; defer_ok = uu___145_6226.defer_ok; smt_ok = uu___145_6226.smt_ok; tcenv = uu___145_6226.tcenv}))
in (match (uu____6225) with
| Success (uu____6228) -> begin
(

let wl = (

let uu___146_6230 = wl
in {attempting = rest; wl_deferred = uu___146_6230.wl_deferred; ctr = uu___146_6230.ctr; defer_ok = uu___146_6230.defer_ok; smt_ok = uu___146_6230.smt_ok; tcenv = uu___146_6230.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let uu____6232 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| uu____6235 -> begin
None
end));
))
end)))
end))
end
| uu____6236 -> begin
(failwith "Impossible: Not a rigid-flex")
end)))
end));
))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> ((

let uu____6243 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6243) with
| true -> begin
(

let uu____6244 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" uu____6244))
end
| uu____6245 -> begin
()
end));
(

let uu____6246 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____6246) with
| (u, args) -> begin
(

let uu____6273 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (uu____6273) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(

let max = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____6292 -> begin
i
end))
in (

let base_types_match = (fun t1 t2 -> (

let uu____6304 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____6304) with
| (h1, args1) -> begin
(

let uu____6332 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____6332) with
| (h2, uu____6345) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
(

let uu____6364 = (FStar_Syntax_Syntax.fv_eq tc1 tc2)
in (match (uu____6364) with
| true -> begin
(match (((FStar_List.length args1) = (Prims.parse_int "0"))) with
| true -> begin
Some ([])
end
| uu____6376 -> begin
(

let uu____6377 = (

let uu____6379 = (

let uu____6380 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_42 -> FStar_TypeChecker_Common.TProb (_0_42)) uu____6380))
in (uu____6379)::[])
in Some (uu____6377))
end)
end
| uu____6386 -> begin
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
| uu____6401 -> begin
(

let uu____6402 = (

let uu____6404 = (

let uu____6405 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_43 -> FStar_TypeChecker_Common.TProb (_0_43)) uu____6405))
in (uu____6404)::[])
in Some (uu____6402))
end)
end
| uu____6411 -> begin
None
end)
end
| uu____6413 -> begin
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
| Some (m) -> begin
(

let x = (FStar_Syntax_Syntax.freshen_bv x)
in (

let subst = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]
in (

let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (

let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (

let uu____6479 = (

let uu____6485 = (

let uu____6488 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x uu____6488))
in ((uu____6485), (m)))
in Some (uu____6479))))))
end))
end
| (uu____6497, FStar_Syntax_Syntax.Tm_refine (y, uu____6499)) -> begin
(

let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some (((t2), (m)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____6531), uu____6532) -> begin
(

let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some (((t1), (m)))
end))
end
| uu____6563 -> begin
(

let m = (base_types_match t1 t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some (((t1), (m)))
end))
end))
in (

let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____6597) -> begin
(

let uu____6610 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___122_6619 -> (match (uu___122_6619) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(

let uu____6624 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____6624) with
| (u', uu____6635) -> begin
(

let uu____6650 = (

let uu____6651 = (whnf env u')
in uu____6651.FStar_Syntax_Syntax.n)
in (match (uu____6650) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____6655) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____6671 -> begin
false
end))
end))
end
| uu____6672 -> begin
false
end)
end
| uu____6674 -> begin
false
end))))
in (match (uu____6610) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun uu____6699 tps -> (match (uu____6699) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(

let uu____6740 = (

let uu____6747 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound uu____6747))
in (match (uu____6740) with
| Some (bound, sub) -> begin
(make_upper_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end))
end
| uu____6782 -> begin
None
end)
end))
in (

let uu____6789 = (

let uu____6796 = (

let uu____6802 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((uu____6802), ([])))
in (make_upper_bound uu____6796 upper_bounds))
in (match (uu____6789) with
| None -> begin
((

let uu____6811 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6811) with
| true -> begin
(FStar_Util.print_string "No upper bounds\n")
end
| uu____6812 -> begin
()
end));
None;
)
end
| Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in ((

let uu____6830 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6830) with
| true -> begin
(

let wl' = (

let uu___147_6832 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___147_6832.wl_deferred; ctr = uu___147_6832.ctr; defer_ok = uu___147_6832.defer_ok; smt_ok = uu___147_6832.smt_ok; tcenv = uu___147_6832.tcenv})
in (

let uu____6833 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" uu____6833)))
end
| uu____6834 -> begin
()
end));
(

let uu____6835 = (solve_t env eq_prob (

let uu___148_6836 = wl
in {attempting = sub_probs; wl_deferred = uu___148_6836.wl_deferred; ctr = uu___148_6836.ctr; defer_ok = uu___148_6836.defer_ok; smt_ok = uu___148_6836.smt_ok; tcenv = uu___148_6836.tcenv}))
in (match (uu____6835) with
| Success (uu____6838) -> begin
(

let wl = (

let uu___149_6840 = wl
in {attempting = rest; wl_deferred = uu___149_6840.wl_deferred; ctr = uu___149_6840.ctr; defer_ok = uu___149_6840.defer_ok; smt_ok = uu___149_6840.smt_ok; tcenv = uu___149_6840.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let uu____6842 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| uu____6845 -> begin
None
end));
))
end)))
end))
end
| uu____6846 -> begin
(failwith "Impossible: Not a flex-rigid")
end)))))
end))
end));
))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (

let rec aux = (fun scope env subst xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
(

let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in ((

let uu____6911 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6911) with
| true -> begin
(

let uu____6912 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" uu____6912))
end
| uu____6913 -> begin
()
end));
(

let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl ((((rhs_prob)::[]), (formula))));
))
end
| (((hd1, imp))::xs, ((hd2, imp'))::ys) when (imp = imp') -> begin
(

let hd1 = (

let uu___150_6944 = hd1
in (

let uu____6945 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___150_6944.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___150_6944.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6945}))
in (

let hd2 = (

let uu___151_6949 = hd2
in (

let uu____6950 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___151_6949.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___151_6949.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6950}))
in (

let prob = (

let uu____6954 = (

let uu____6957 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort uu____6957 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _0_44 -> FStar_TypeChecker_Common.TProb (_0_44)) uu____6954))
in (

let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (

let subst = (

let uu____6965 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd1))))::uu____6965)
in (

let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (

let uu____6968 = (aux ((((hd1), (imp)))::scope) env subst xs ys)
in (match (uu____6968) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi = (

let uu____6986 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (

let uu____6989 = (FStar_Syntax_Util.close_forall ((((hd1), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj uu____6986 uu____6989)))
in ((

let uu____6995 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6995) with
| true -> begin
(

let uu____6996 = (FStar_Syntax_Print.term_to_string phi)
in (

let uu____6997 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" uu____6996 uu____6997)))
end
| uu____6998 -> begin
()
end));
FStar_Util.Inl ((((prob)::sub_probs), (phi)));
))
end
| fail -> begin
fail
end))))))))
end
| uu____7012 -> begin
FStar_Util.Inr ("arity or argument-qualifier mismatch")
end))
in (

let scope = (p_scope orig)
in (

let uu____7018 = (aux scope env [] bs1 bs2)
in (match (uu____7018) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end)))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let uu____7034 = (compress_tprob wl problem)
in (solve_t' env uu____7034 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (

let uu____7067 = (head_matches_delta env wl t1 t2)
in (match (uu____7067) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____7084), uu____7085) -> begin
(

let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____7107 -> begin
false
end))
in (match ((((may_relate head1) || (may_relate head2)) && wl.smt_ok)) with
| true -> begin
(

let guard = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end
| uu____7113 -> begin
(

let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(

let x = (FStar_Syntax_Syntax.new_bv None t1)
in (

let uu____7127 = (

let uu____7128 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 uu____7128 t2))
in (FStar_Syntax_Util.mk_forall x uu____7127)))
end))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB)) with
| true -> begin
(has_type_guard t1 t2)
end
| uu____7131 -> begin
(has_type_guard t2 t1)
end))
end)
in (

let uu____7132 = (solve_prob orig (Some (guard)) [] wl)
in (solve env uu____7132)))
end
| uu____7135 -> begin
(giveup env "head mismatch" orig)
end))
end
| (uu____7136, Some (t1, t2)) -> begin
(solve_t env (

let uu___152_7144 = problem
in {FStar_TypeChecker_Common.pid = uu___152_7144.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___152_7144.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___152_7144.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___152_7144.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___152_7144.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___152_7144.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___152_7144.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___152_7144.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____7145, None) -> begin
((

let uu____7152 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7152) with
| true -> begin
(

let uu____7153 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____7154 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____7155 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____7156 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" uu____7153 uu____7154 uu____7155 uu____7156)))))
end
| uu____7157 -> begin
()
end));
(

let uu____7158 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____7158) with
| (head1, args1) -> begin
(

let uu____7184 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____7184) with
| (head2, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((nargs <> (FStar_List.length args2))) with
| true -> begin
(

let uu____7224 = (

let uu____7225 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____7226 = (args_to_string args1)
in (

let uu____7227 = (FStar_Syntax_Print.term_to_string head2)
in (

let uu____7228 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____7225 uu____7226 uu____7227 uu____7228)))))
in (giveup env uu____7224 orig))
end
| uu____7229 -> begin
(

let uu____7230 = ((nargs = (Prims.parse_int "0")) || (

let uu____7233 = (FStar_Syntax_Util.eq_args args1 args2)
in (uu____7233 = FStar_Syntax_Util.Equal)))
in (match (uu____7230) with
| true -> begin
(

let uu____7234 = (solve_maybe_uinsts env orig head1 head2 wl)
in (match (uu____7234) with
| USolved (wl) -> begin
(

let uu____7236 = (solve_prob orig None [] wl)
in (solve env uu____7236))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end))
end
| uu____7239 -> begin
(

let uu____7240 = (base_and_refinement env wl t1)
in (match (uu____7240) with
| (base1, refinement1) -> begin
(

let uu____7266 = (base_and_refinement env wl t2)
in (match (uu____7266) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (None, None) -> begin
(

let uu____7320 = (solve_maybe_uinsts env orig head1 head2 wl)
in (match (uu____7320) with
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end
| USolved (wl) -> begin
(

let subprobs = (FStar_List.map2 (fun uu____7330 uu____7331 -> (match (((uu____7330), (uu____7331))) with
| ((a, uu____7341), (a', uu____7343)) -> begin
(

let uu____7348 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _0_45 -> FStar_TypeChecker_Common.TProb (_0_45)) uu____7348))
end)) args1 args2)
in (

let formula = (

let uu____7354 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____7354))
in (

let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end))
end
| uu____7358 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env (

let uu___153_7391 = problem
in {FStar_TypeChecker_Common.pid = uu___153_7391.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___153_7391.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___153_7391.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___153_7391.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___153_7391.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___153_7391.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___153_7391.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___153_7391.FStar_TypeChecker_Common.rank}) wl)))
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

let imitate = (fun orig env wl p -> (

let uu____7411 = p
in (match (uu____7411) with
| (((u, k), xs, c), ps, (h, uu____7422, qs)) -> begin
(

let xs = (sn_binders env xs)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____7471 = (imitation_sub_probs orig env xs ps qs)
in (match (uu____7471) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (

let uu____7485 = (h gs_xs)
in (

let uu____7486 = (

let uu____7493 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_46 -> FStar_Util.Inl (_0_46)))
in (FStar_All.pipe_right uu____7493 (fun _0_47 -> Some (_0_47))))
in (FStar_Syntax_Util.abs xs uu____7485 uu____7486)))
in ((

let uu____7524 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7524) with
| true -> begin
(

let uu____7525 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (

let uu____7526 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____7527 = (FStar_Syntax_Print.term_to_string im)
in (

let uu____7528 = (FStar_Syntax_Print.tag_of_term im)
in (

let uu____7529 = (

let uu____7530 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right uu____7530 (FStar_String.concat ", ")))
in (

let uu____7533 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" uu____7525 uu____7526 uu____7527 uu____7528 uu____7529 uu____7533)))))))
end
| uu____7534 -> begin
()
end));
(

let wl = (solve_prob orig (Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl)
in (solve env (attempt sub_probs wl)));
))
end))))
end)))
in (

let imitate' = (fun orig env wl uu___123_7551 -> (match (uu___123_7551) with
| None -> begin
(giveup env "unable to compute subterms" orig)
end
| Some (p) -> begin
(imitate orig env wl p)
end))
in (

let project = (fun orig env wl i p -> (

let uu____7580 = p
in (match (uu____7580) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____7638 = (FStar_List.nth ps i)
in (match (uu____7638) with
| (pi, uu____7641) -> begin
(

let uu____7646 = (FStar_List.nth xs i)
in (match (uu____7646) with
| (xi, uu____7653) -> begin
(

let rec gs = (fun k -> (

let uu____7662 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____7662) with
| (bs, k) -> begin
(

let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
(([]), ([]))
end
| ((a, uu____7714))::tl -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (

let uu____7722 = (new_uvar r xs k_a)
in (match (uu____7722) with
| (gi_xs, gi) -> begin
(

let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (

let gi_ps = ((FStar_Syntax_Syntax.mk_Tm_app gi ps) (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst = (FStar_Syntax_Syntax.NT (((a), (gi_xs))))::subst
in (

let uu____7741 = (aux subst tl)
in (match (uu____7741) with
| (gi_xs', gi_ps') -> begin
(

let uu____7756 = (

let uu____7758 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (uu____7758)::gi_xs')
in (

let uu____7759 = (

let uu____7761 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (uu____7761)::gi_ps')
in ((uu____7756), (uu____7759))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in (

let uu____7764 = (

let uu____7765 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation uu____7765))
in (match (uu____7764) with
| true -> begin
None
end
| uu____7767 -> begin
(

let uu____7768 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (uu____7768) with
| (g_xs, uu____7775) -> begin
(

let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (

let uu____7782 = ((FStar_Syntax_Syntax.mk_Tm_app xi g_xs) None r)
in (

let uu____7787 = (

let uu____7794 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_48 -> FStar_Util.Inl (_0_48)))
in (FStar_All.pipe_right uu____7794 (fun _0_49 -> Some (_0_49))))
in (FStar_Syntax_Util.abs xs uu____7782 uu____7787)))
in (

let sub = (

let uu____7825 = (

let uu____7828 = ((FStar_Syntax_Syntax.mk_Tm_app proj ps) None r)
in (

let uu____7835 = (

let uu____7838 = (FStar_List.map (fun uu____7844 -> (match (uu____7844) with
| (uu____7849, uu____7850, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h uu____7838))
in (mk_problem (p_scope orig) orig uu____7828 (p_rel orig) uu____7835 None "projection")))
in (FStar_All.pipe_left (fun _0_50 -> FStar_TypeChecker_Common.TProb (_0_50)) uu____7825))
in ((

let uu____7860 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7860) with
| true -> begin
(

let uu____7861 = (FStar_Syntax_Print.term_to_string proj)
in (

let uu____7862 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" uu____7861 uu____7862)))
end
| uu____7863 -> begin
()
end));
(

let wl = (

let uu____7865 = (

let uu____7867 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (uu____7867))
in (solve_prob orig uu____7865 ((TERM (((u), (proj))))::[]) wl))
in (

let uu____7872 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _0_51 -> Some (_0_51)) uu____7872)));
))))
end))
end)))
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl -> (

let uu____7896 = lhs
in (match (uu____7896) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let uu____7919 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (uu____7919) with
| (xs, c) -> begin
(match (((FStar_List.length xs) = (FStar_List.length ps))) with
| true -> begin
(

let uu____7941 = (

let uu____7967 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____7967)))
in Some (uu____7941))
end
| uu____8033 -> begin
(

let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (

let uu____8050 = (

let uu____8054 = (

let uu____8055 = (FStar_Syntax_Subst.compress k)
in uu____8055.FStar_Syntax_Syntax.n)
in ((uu____8054), (args)))
in (match (uu____8050) with
| (uu____8062, []) -> begin
(

let uu____8064 = (

let uu____8070 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____8070)))
in Some (uu____8064))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(

let uu____8087 = (FStar_Syntax_Util.head_and_args k)
in (match (uu____8087) with
| (uv, uv_args) -> begin
(

let uu____8116 = (

let uu____8117 = (FStar_Syntax_Subst.compress uv)
in uu____8117.FStar_Syntax_Syntax.n)
in (match (uu____8116) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____8124) -> begin
(

let uu____8137 = (pat_vars env [] uv_args)
in (match (uu____8137) with
| None -> begin
None
end
| Some (scope) -> begin
(

let xs = (FStar_All.pipe_right args (FStar_List.map (fun uu____8151 -> (

let uu____8152 = (

let uu____8153 = (

let uu____8154 = (

let uu____8157 = (

let uu____8158 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8158 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____8157))
in (Prims.fst uu____8154))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) uu____8153))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____8152)))))
in (

let c = (

let uu____8164 = (

let uu____8165 = (

let uu____8168 = (

let uu____8169 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8169 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____8168))
in (Prims.fst uu____8165))
in (FStar_Syntax_Syntax.mk_Total uu____8164))
in (

let k' = (FStar_Syntax_Util.arrow xs c)
in (

let uv_sol = (

let uu____8178 = (

let uu____8185 = (

let uu____8191 = (

let uu____8192 = (

let uu____8195 = (

let uu____8196 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8196 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total uu____8195))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8192))
in FStar_Util.Inl (uu____8191))
in Some (uu____8185))
in (FStar_Syntax_Util.abs scope k' uu____8178))
in ((FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)));
Some (((xs), (c)));
)))))
end))
end
| uu____8219 -> begin
None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), uu____8224) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs)
in (match ((n_xs = n_args)) with
| true -> begin
(

let uu____8250 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right uu____8250 (fun _0_52 -> Some (_0_52))))
end
| uu____8260 -> begin
(match ((n_xs < n_args)) with
| true -> begin
(

let uu____8269 = (FStar_Util.first_N n_xs args)
in (match (uu____8269) with
| (args, rest) -> begin
(

let uu____8285 = (FStar_Syntax_Subst.open_comp xs c)
in (match (uu____8285) with
| (xs, c) -> begin
(

let uu____8293 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt uu____8293 (fun uu____8304 -> (match (uu____8304) with
| (xs', c) -> begin
Some ((((FStar_List.append xs xs')), (c)))
end))))
end))
end))
end
| uu____8325 -> begin
(

let uu____8326 = (FStar_Util.first_N n_args xs)
in (match (uu____8326) with
| (xs, rest) -> begin
(

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c))))) None k.FStar_Syntax_Syntax.pos)
in (

let uu____8372 = (

let uu____8375 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs uu____8375))
in (FStar_All.pipe_right uu____8372 (fun _0_53 -> Some (_0_53)))))
end))
end)
end)))
end
| uu____8383 -> begin
(

let uu____8387 = (

let uu____8388 = (FStar_Syntax_Print.uvar_to_string uv)
in (

let uu____8392 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____8393 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" uu____8388 uu____8392 uu____8393))))
in (failwith uu____8387))
end)))
in (

let uu____8397 = (elim k_uv ps)
in (FStar_Util.bind_opt uu____8397 (fun uu____8425 -> (match (uu____8425) with
| (xs, c) -> begin
(

let uu____8453 = (

let uu____8476 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____8476)))
in Some (uu____8453))
end))))))
end)
end)))
in (

let rec imitate_or_project = (fun n stopt i -> (match (((i >= n) || (FStar_Option.isNone stopt))) with
| true -> begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end
| uu____8545 -> begin
(

let st = (FStar_Option.get stopt)
in (

let tx = (FStar_Unionfind.new_transaction ())
in (match ((i = (~- ((Prims.parse_int "1"))))) with
| true -> begin
(

let uu____8548 = (imitate orig env wl st)
in (match (uu____8548) with
| Failed (uu____8553) -> begin
((FStar_Unionfind.rollback tx);
(imitate_or_project n stopt (i + (Prims.parse_int "1")));
)
end
| sol -> begin
sol
end))
end
| uu____8558 -> begin
(

let uu____8559 = (project orig env wl i st)
in (match (uu____8559) with
| (None) | (Some (Failed (_))) -> begin
((FStar_Unionfind.rollback tx);
(imitate_or_project n stopt (i + (Prims.parse_int "1")));
)
end
| Some (sol) -> begin
sol
end))
end)))
end))
in (

let check_head = (fun fvs1 t2 -> (

let uu____8577 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____8577) with
| (hd, uu____8588) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| uu____8606 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd)
in (

let uu____8609 = (FStar_Util.set_is_subset_of fvs_hd fvs1)
in (match (uu____8609) with
| true -> begin
true
end
| uu____8610 -> begin
((

let uu____8612 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8612) with
| true -> begin
(

let uu____8613 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" uu____8613))
end
| uu____8614 -> begin
()
end));
false;
)
end)))
end)
end)))
in (

let imitate_ok = (fun t2 -> (

let fvs_hd = (

let uu____8621 = (

let uu____8624 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____8624 Prims.fst))
in (FStar_All.pipe_right uu____8621 FStar_Syntax_Free.names))
in (

let uu____8655 = (FStar_Util.set_is_empty fvs_hd)
in (match (uu____8655) with
| true -> begin
(~- ((Prims.parse_int "1")))
end
| uu____8656 -> begin
(Prims.parse_int "0")
end))))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(

let t1 = (sn env t1)
in (

let t2 = (sn env t2)
in (

let fvs1 = (FStar_Syntax_Free.names t1)
in (

let fvs2 = (FStar_Syntax_Free.names t2)
in (

let uu____8664 = (occurs_check env wl ((uv), (k_uv)) t2)
in (match (uu____8664) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____8672 = (

let uu____8673 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____8673))
in (giveup_or_defer orig uu____8672))
end
| uu____8674 -> begin
(

let uu____8675 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____8675) with
| true -> begin
(

let uu____8676 = (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t2)) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))
in (match (uu____8676) with
| true -> begin
(

let uu____8677 = (subterms args_lhs)
in (imitate' orig env wl uu____8677))
end
| uu____8679 -> begin
((

let uu____8681 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8681) with
| true -> begin
(

let uu____8682 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____8683 = (names_to_string fvs1)
in (

let uu____8684 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" uu____8682 uu____8683 uu____8684))))
end
| uu____8685 -> begin
()
end));
(

let sol = (match (vars) with
| [] -> begin
t2
end
| uu____8689 -> begin
(

let uu____8690 = (sn_binders env vars)
in (u_abs k_uv uu____8690 t2))
end)
in (

let wl = (solve_prob orig None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl)
in (solve env wl)));
)
end))
end
| uu____8697 -> begin
(match ((((not (patterns_only)) && wl.defer_ok) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end
| uu____8698 -> begin
(

let uu____8699 = ((not (patterns_only)) && (check_head fvs1 t2))
in (match (uu____8699) with
| true -> begin
((

let uu____8701 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8701) with
| true -> begin
(

let uu____8702 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____8703 = (names_to_string fvs1)
in (

let uu____8704 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" uu____8702 uu____8703 uu____8704))))
end
| uu____8705 -> begin
()
end));
(

let uu____8706 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____8706 (~- ((Prims.parse_int "1")))));
)
end
| uu____8715 -> begin
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
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "not a pattern" orig wl))
end
| uu____8716 -> begin
(

let uu____8717 = (

let uu____8718 = (FStar_Syntax_Free.names t1)
in (check_head uu____8718 t2))
in (match (uu____8717) with
| true -> begin
(

let im_ok = (imitate_ok t2)
in ((

let uu____8722 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8722) with
| true -> begin
(

let uu____8723 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" uu____8723 (match ((im_ok < (Prims.parse_int "0"))) with
| true -> begin
"imitating"
end
| uu____8724 -> begin
"projecting"
end)))
end
| uu____8725 -> begin
()
end));
(

let uu____8726 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____8726 im_ok));
))
end
| uu____8735 -> begin
(giveup env "head-symbol is free" orig)
end))
end)
end)))))
end)))
in (

let flex_flex = (fun orig lhs rhs -> (match ((wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex-flex deferred" orig wl))
end
| uu____8746 -> begin
(

let force_quasi_pattern = (fun xs_opt uu____8768 -> (match (uu____8768) with
| (t, u, k, args) -> begin
(

let uu____8798 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____8798) with
| (all_formals, uu____8809) -> begin
(

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match (((formals), (args))) with
| ([], []) -> begin
(

let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun uu____8901 -> (match (uu____8901) with
| (x, imp) -> begin
(

let uu____8908 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____8908), (imp)))
end))))
in (

let pattern_vars = (FStar_List.rev pattern_vars)
in (

let kk = (

let uu____8916 = (FStar_Syntax_Util.type_u ())
in (match (uu____8916) with
| (t, uu____8920) -> begin
(

let uu____8921 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst uu____8921))
end))
in (

let uu____8924 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (uu____8924) with
| (t', tm_u1) -> begin
(

let uu____8931 = (destruct_flex_t t')
in (match (uu____8931) with
| (uu____8951, u1, k1, uu____8954) -> begin
(

let sol = (

let uu____8982 = (

let uu____8987 = (u_abs k all_formals t')
in ((((u), (k))), (uu____8987)))
in TERM (uu____8982))
in (

let t_app = ((FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args) None t.FStar_Syntax_Syntax.pos)
in ((sol), (((t_app), (u1), (k1), (pat_args))))))
end))
end)))))
end
| ((formal)::formals, (hd)::tl) -> begin
(

let uu____9047 = (pat_var_opt env pat_args hd)
in (match (uu____9047) with
| None -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| Some (y) -> begin
(

let maybe_pat = (match (xs_opt) with
| None -> begin
true
end
| Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun uu____9076 -> (match (uu____9076) with
| (x, uu____9080) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in (match ((not (maybe_pat))) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| uu____9083 -> begin
(

let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____9086 = (

let uu____9087 = (FStar_Util.set_is_subset_of fvs pattern_var_set)
in (not (uu____9087)))
in (match (uu____9086) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| uu____9090 -> begin
(

let uu____9091 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) uu____9091 formals tl))
end)))
end))
end))
end
| uu____9097 -> begin
(failwith "Impossible")
end))
in (

let uu____9108 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] uu____9108 all_formals args)))
end))
end))
in (

let solve_both_pats = (fun wl uu____9156 uu____9157 r -> (match (((uu____9156), (uu____9157))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
(

let uu____9311 = ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys))
in (match (uu____9311) with
| true -> begin
(

let uu____9315 = (solve_prob orig None [] wl)
in (solve env uu____9315))
end
| uu____9316 -> begin
(

let xs = (sn_binders env xs)
in (

let ys = (sn_binders env ys)
in (

let zs = (intersect_vars xs ys)
in ((

let uu____9330 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9330) with
| true -> begin
(

let uu____9331 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (

let uu____9332 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (

let uu____9333 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (

let uu____9334 = (FStar_Syntax_Print.term_to_string k1)
in (

let uu____9335 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" uu____9331 uu____9332 uu____9333 uu____9334 uu____9335))))))
end
| uu____9336 -> begin
()
end));
(

let subst_k = (fun k xs args -> (

let xs_len = (FStar_List.length xs)
in (

let args_len = (FStar_List.length args)
in (match ((xs_len = args_len)) with
| true -> begin
(

let uu____9377 = (FStar_Syntax_Util.subst_of_list xs args)
in (FStar_Syntax_Subst.subst uu____9377 k))
end
| uu____9379 -> begin
(match ((args_len < xs_len)) with
| true -> begin
(

let uu____9385 = (FStar_Util.first_N args_len xs)
in (match (uu____9385) with
| (xs, xs_rest) -> begin
(

let k = (

let uu____9415 = (FStar_Syntax_Syntax.mk_GTotal k)
in (FStar_Syntax_Util.arrow xs_rest uu____9415))
in (

let uu____9418 = (FStar_Syntax_Util.subst_of_list xs args)
in (FStar_Syntax_Subst.subst uu____9418 k)))
end))
end
| uu____9420 -> begin
(

let uu____9421 = (

let uu____9422 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____9423 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (

let uu____9424 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" uu____9422 uu____9423 uu____9424))))
in (failwith uu____9421))
end)
end))))
in (

let uu____9425 = (

let uu____9431 = (

let uu____9439 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals uu____9439))
in (match (uu____9431) with
| (bs, k1') -> begin
(

let uu____9457 = (

let uu____9465 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals uu____9465))
in (match (uu____9457) with
| (cs, k2') -> begin
(

let k1'_xs = (subst_k k1' bs args1)
in (

let k2'_ys = (subst_k k2' cs args2)
in (

let sub_prob = (

let uu____9486 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_54 -> FStar_TypeChecker_Common.TProb (_0_54)) uu____9486))
in (

let uu____9491 = (

let uu____9494 = (

let uu____9495 = (FStar_Syntax_Subst.compress k1')
in uu____9495.FStar_Syntax_Syntax.n)
in (

let uu____9498 = (

let uu____9499 = (FStar_Syntax_Subst.compress k2')
in uu____9499.FStar_Syntax_Syntax.n)
in ((uu____9494), (uu____9498))))
in (match (uu____9491) with
| (FStar_Syntax_Syntax.Tm_type (uu____9507), uu____9508) -> begin
((k1'), ((sub_prob)::[]))
end
| (uu____9512, FStar_Syntax_Syntax.Tm_type (uu____9513)) -> begin
((k2'), ((sub_prob)::[]))
end
| uu____9517 -> begin
(

let uu____9520 = (FStar_Syntax_Util.type_u ())
in (match (uu____9520) with
| (t, uu____9529) -> begin
(

let uu____9530 = (new_uvar r zs t)
in (match (uu____9530) with
| (k_zs, uu____9539) -> begin
(

let kprob = (

let uu____9541 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k_zs None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_55 -> FStar_TypeChecker_Common.TProb (_0_55)) uu____9541))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end)))))
end))
end))
in (match (uu____9425) with
| (k_u', sub_probs) -> begin
(

let uu____9555 = (

let uu____9563 = (

let uu____9564 = (new_uvar r zs k_u')
in (FStar_All.pipe_left Prims.fst uu____9564))
in (

let uu____9569 = (

let uu____9572 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs uu____9572))
in (

let uu____9575 = (

let uu____9578 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys uu____9578))
in ((uu____9563), (uu____9569), (uu____9575)))))
in (match (uu____9555) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs u_zs)
in (

let uu____9597 = (occurs_check env wl ((u1), (k1)) sub1)
in (match (uu____9597) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end
| uu____9609 -> begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in (

let uu____9621 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____9621) with
| true -> begin
(

let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end
| uu____9626 -> begin
(

let sub2 = (u_abs knew2 ys u_zs)
in (

let uu____9628 = (occurs_check env wl ((u2), (k2)) sub2)
in (match (uu____9628) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end
| uu____9640 -> begin
(

let sol2 = TERM (((((u2), (k2))), (sub2)))
in (

let wl = (solve_prob orig None ((sol1)::(sol2)::[]) wl)
in (solve env (attempt sub_probs wl))))
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

let solve_one_pat = (fun uu____9680 uu____9681 -> (match (((uu____9680), (uu____9681))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
((

let uu____9785 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9785) with
| true -> begin
(

let uu____9786 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____9787 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" uu____9786 uu____9787)))
end
| uu____9788 -> begin
()
end));
(

let uu____9789 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____9789) with
| true -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____9799 uu____9800 -> (match (((uu____9799), (uu____9800))) with
| ((a, uu____9810), (t2, uu____9812)) -> begin
(

let uu____9817 = (

let uu____9820 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig uu____9820 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right uu____9817 (fun _0_56 -> FStar_TypeChecker_Common.TProb (_0_56))))
end)) xs args2)
in (

let guard = (

let uu____9824 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____9824))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end
| uu____9830 -> begin
(

let t2 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t2)
in (

let uu____9834 = (occurs_check env wl ((u1), (k1)) t2)
in (match (uu____9834) with
| (occurs_ok, uu____9843) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in (

let uu____9848 = (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars))
in (match (uu____9848) with
| true -> begin
(

let sol = (

let uu____9850 = (

let uu____9855 = (u_abs k1 xs t2)
in ((((u1), (k1))), (uu____9855)))
in TERM (uu____9850))
in (

let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end
| uu____9867 -> begin
(

let uu____9868 = (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok))
in (match (uu____9868) with
| true -> begin
(

let uu____9869 = (force_quasi_pattern (Some (xs)) ((t2), (u2), (k2), (args2)))
in (match (uu____9869) with
| (sol, (uu____9883, u2, k2, ys)) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____9893 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____9893) with
| true -> begin
(

let uu____9894 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" uu____9894))
end
| uu____9895 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| uu____9899 -> begin
(giveup env "impossible" orig)
end);
))
end))
end
| uu____9900 -> begin
(giveup_or_defer orig "flex-flex constraint")
end))
end)))
end))))
end));
)
end))
in (

let uu____9901 = lhs
in (match (uu____9901) with
| (t1, u1, k1, args1) -> begin
(

let uu____9906 = rhs
in (match (uu____9906) with
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
| uu____9932 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end
| uu____9937 -> begin
(

let uu____9938 = (force_quasi_pattern None ((t1), (u1), (k1), (args1)))
in (match (uu____9938) with
| (sol, uu____9945) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____9948 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____9948) with
| true -> begin
(

let uu____9949 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" uu____9949))
end
| uu____9950 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| uu____9954 -> begin
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

let uu____9956 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____9956) with
| true -> begin
(

let uu____9957 = (solve_prob orig None [] wl)
in (solve env uu____9957))
end
| uu____9958 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in (

let uu____9961 = (FStar_Util.physical_equality t1 t2)
in (match (uu____9961) with
| true -> begin
(

let uu____9962 = (solve_prob orig None [] wl)
in (solve env uu____9962))
end
| uu____9963 -> begin
((

let uu____9965 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____9965) with
| true -> begin
(

let uu____9966 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" uu____9966))
end
| uu____9967 -> begin
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

let mk_c = (fun c uu___124_10012 -> (match (uu___124_10012) with
| [] -> begin
c
end
| bs -> begin
(

let uu____10026 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c))))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____10026))
end))
in (

let uu____10040 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____10040) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (

let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (

let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (

let rel = (

let uu____10126 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____10126) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____10127 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (

let uu____10128 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _0_57 -> FStar_TypeChecker_Common.CProb (_0_57)) uu____10128)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___125_10205 -> (match (uu___125_10205) with
| [] -> begin
t
end
| bs -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l))))) None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____10244 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____10244) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (

let uu____10327 = (

let uu____10330 = (FStar_Syntax_Subst.subst subst tbody1)
in (

let uu____10331 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig uu____10330 problem.FStar_TypeChecker_Common.relation uu____10331 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _0_58 -> FStar_TypeChecker_Common.TProb (_0_58)) uu____10327))))
end)))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____10346) -> begin
true
end
| uu____10361 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____10380 -> begin
(

let t = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____10386 -> begin
FStar_Util.Inr (t)
end))
end))
in (

let uu____10389 = (

let uu____10400 = (maybe_eta t1)
in (

let uu____10405 = (maybe_eta t2)
in ((uu____10400), (uu____10405))))
in (match (uu____10389) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(solve_t env (

let uu___154_10436 = problem
in {FStar_TypeChecker_Common.pid = uu___154_10436.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___154_10436.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___154_10436.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___154_10436.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___154_10436.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___154_10436.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___154_10436.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___154_10436.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs))) | ((FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs))) -> begin
(

let uu____10469 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____10469) with
| true -> begin
(

let uu____10470 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____10470 t_abs wl))
end
| uu____10474 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| uu____10475 -> begin
(failwith "Impossible: at least one side is an abstraction")
end))))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____10486), FStar_Syntax_Syntax.Tm_refine (uu____10487)) -> begin
(

let uu____10496 = (as_refinement env wl t1)
in (match (uu____10496) with
| (x1, phi1) -> begin
(

let uu____10501 = (as_refinement env wl t2)
in (match (uu____10501) with
| (x2, phi2) -> begin
(

let base_prob = (

let uu____10507 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _0_59 -> FStar_TypeChecker_Common.TProb (_0_59)) uu____10507))
in (

let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (

let subst = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x1))))::[]
in (

let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (

let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (

let env = (FStar_TypeChecker_Env.push_bv env x1)
in (

let mk_imp = (fun imp phi1 phi2 -> (

let uu____10542 = (imp phi1 phi2)
in (FStar_All.pipe_right uu____10542 (guard_on_element problem x1))))
in (

let fallback = (fun uu____10548 -> (

let impl = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end
| uu____10554 -> begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end)
in (

let guard = (

let uu____10558 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____10558 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl))))))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let ref_prob = (

let uu____10565 = (

let uu____10568 = (

let uu____10569 = (FStar_Syntax_Syntax.mk_binder x1)
in (uu____10569)::(p_scope orig))
in (mk_problem uu____10568 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _0_60 -> FStar_TypeChecker_Common.TProb (_0_60)) uu____10565))
in (

let uu____10572 = (solve env (

let uu___155_10573 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___155_10573.ctr; defer_ok = false; smt_ok = uu___155_10573.smt_ok; tcenv = uu___155_10573.tcenv}))
in (match (uu____10572) with
| Failed (uu____10577) -> begin
(fallback ())
end
| Success (uu____10580) -> begin
(

let guard = (

let uu____10584 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (

let uu____10587 = (

let uu____10588 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right uu____10588 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj uu____10584 uu____10587)))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (

let wl = (

let uu___156_10597 = wl
in {attempting = uu___156_10597.attempting; wl_deferred = uu___156_10597.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___156_10597.defer_ok; smt_ok = uu___156_10597.smt_ok; tcenv = uu___156_10597.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end)))
end
| uu____10598 -> begin
(fallback ())
end)))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(

let uu____10651 = (destruct_flex_t t1)
in (

let uu____10652 = (destruct_flex_t t2)
in (flex_flex orig uu____10651 uu____10652)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(

let uu____10668 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____10668 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_arrow (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
(solve_t' env (

let uu___157_10717 = problem
in {FStar_TypeChecker_Common.pid = uu___157_10717.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___157_10717.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___157_10717.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___157_10717.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___157_10717.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___157_10717.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___157_10717.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___157_10717.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___157_10717.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____10733 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____10735 = (

let uu____10736 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____10736))
in (match (uu____10735) with
| true -> begin
(

let uu____10737 = (FStar_All.pipe_left (fun _0_61 -> FStar_TypeChecker_Common.TProb (_0_61)) (

let uu___158_10740 = problem
in {FStar_TypeChecker_Common.pid = uu___158_10740.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___158_10740.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___158_10740.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___158_10740.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___158_10740.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___158_10740.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___158_10740.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___158_10740.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___158_10740.FStar_TypeChecker_Common.rank}))
in (

let uu____10741 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____10737 uu____10741 t2 wl)))
end
| uu____10745 -> begin
(

let uu____10746 = (base_and_refinement env wl t2)
in (match (uu____10746) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(

let uu____10776 = (FStar_All.pipe_left (fun _0_62 -> FStar_TypeChecker_Common.TProb (_0_62)) (

let uu___159_10779 = problem
in {FStar_TypeChecker_Common.pid = uu___159_10779.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___159_10779.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___159_10779.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___159_10779.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___159_10779.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___159_10779.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___159_10779.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___159_10779.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___159_10779.FStar_TypeChecker_Common.rank}))
in (

let uu____10780 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____10776 uu____10780 t_base wl)))
end
| Some (y, phi) -> begin
(

let y' = (

let uu___160_10795 = y
in {FStar_Syntax_Syntax.ppname = uu___160_10795.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___160_10795.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element problem y' phi)
in (

let base_prob = (

let uu____10800 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_63 -> FStar_TypeChecker_Common.TProb (_0_63)) uu____10800))
in (

let guard = (

let uu____10808 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____10808 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))))
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
| uu____10829 -> begin
(

let uu____10830 = (base_and_refinement env wl t1)
in (match (uu____10830) with
| (t_base, uu____10841) -> begin
(solve_t env (

let uu___161_10856 = problem
in {FStar_TypeChecker_Common.pid = uu___161_10856.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___161_10856.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___161_10856.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___161_10856.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___161_10856.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___161_10856.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___161_10856.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___161_10856.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (FStar_Syntax_Syntax.Tm_refine (uu____10859), uu____10860) -> begin
(

let t2 = (

let uu____10868 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement uu____10868))
in (solve_t env (

let uu___162_10881 = problem
in {FStar_TypeChecker_Common.pid = uu___162_10881.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___162_10881.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___162_10881.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___162_10881.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_10881.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_10881.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_10881.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_10881.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_10881.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____10882, FStar_Syntax_Syntax.Tm_refine (uu____10883)) -> begin
(

let t1 = (

let uu____10891 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement uu____10891))
in (solve_t env (

let uu___163_10904 = problem
in {FStar_TypeChecker_Common.pid = uu___163_10904.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___163_10904.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___163_10904.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___163_10904.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___163_10904.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___163_10904.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___163_10904.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___163_10904.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___163_10904.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(

let head1 = (

let uu____10934 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____10934 Prims.fst))
in (

let head2 = (

let uu____10965 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____10965 Prims.fst))
in (

let uu____10993 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____10993) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____11002 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____11002) with
| true -> begin
(

let guard = (

let uu____11011 = (

let uu____11012 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____11012 = FStar_Syntax_Util.Equal))
in (match (uu____11011) with
| true -> begin
None
end
| uu____11018 -> begin
(

let uu____11019 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _0_64 -> Some (_0_64)) uu____11019))
end))
in (

let uu____11029 = (solve_prob orig guard [] wl)
in (solve env uu____11029)))
end
| uu____11030 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____11031 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, uu____11033, uu____11034), uu____11035) -> begin
(solve_t' env (

let uu___164_11054 = problem
in {FStar_TypeChecker_Common.pid = uu___164_11054.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___164_11054.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___164_11054.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___164_11054.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_11054.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_11054.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_11054.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_11054.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_11054.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____11057, FStar_Syntax_Syntax.Tm_ascribed (t2, uu____11059, uu____11060)) -> begin
(solve_t' env (

let uu___165_11079 = problem
in {FStar_TypeChecker_Common.pid = uu___165_11079.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___165_11079.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___165_11079.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___165_11079.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___165_11079.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___165_11079.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___165_11079.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___165_11079.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___165_11079.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(

let uu____11092 = (

let uu____11093 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____11094 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____11093 uu____11094)))
in (failwith uu____11092))
end
| uu____11095 -> begin
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

let uu____11127 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____11127) with
| true -> begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end
| uu____11128 -> begin
()
end));
(

let sub_probs = (FStar_List.map2 (fun uu____11135 uu____11136 -> (match (((uu____11135), (uu____11136))) with
| ((a1, uu____11146), (a2, uu____11148)) -> begin
(

let uu____11153 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _0_65 -> FStar_TypeChecker_Common.TProb (_0_65)) uu____11153))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (

let uu____11159 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____11159))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))));
))
in (

let solve_sub = (fun c1 edge c2 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let wp = (match (c1.FStar_Syntax_Syntax.effect_args) with
| ((wp1, uu____11182))::[] -> begin
wp1
end
| uu____11195 -> begin
(

let uu____11201 = (

let uu____11202 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" uu____11202))
in (failwith uu____11201))
end)
in (

let c1 = (

let uu____11206 = (

let uu____11212 = (

let uu____11213 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____11213))
in (uu____11212)::[])
in {FStar_Syntax_Syntax.comp_univs = c1.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____11206; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2)))
end
| uu____11214 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___126_11217 -> (match (uu___126_11217) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| uu____11218 -> begin
false
end))))
in (

let uu____11219 = (match (((c1.FStar_Syntax_Syntax.effect_args), (c2.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____11243))::uu____11244, ((wp2, uu____11246))::uu____11247) -> begin
((wp1), (wp2))
end
| uu____11288 -> begin
(

let uu____11301 = (

let uu____11302 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____11303 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____11302 uu____11303)))
in (failwith uu____11301))
end)
in (match (uu____11219) with
| (wpc1, wpc2) -> begin
(

let uu____11320 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____11320) with
| true -> begin
(

let uu____11323 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env uu____11323 wl))
end
| uu____11326 -> begin
(

let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____11329 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____11331 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11331) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____11332 -> begin
()
end));
(

let uu____11333 = (

let uu____11336 = (

let uu____11337 = (

let uu____11347 = (

let uu____11348 = (

let uu____11349 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (uu____11349)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____11348 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (

let uu____11350 = (

let uu____11352 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____11353 = (

let uu____11355 = (

let uu____11356 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11356))
in (uu____11355)::[])
in (uu____11352)::uu____11353))
in ((uu____11347), (uu____11350))))
in FStar_Syntax_Syntax.Tm_app (uu____11337))
in (FStar_Syntax_Syntax.mk uu____11336))
in (uu____11333 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r));
)
end
| uu____11366 -> begin
(

let uu____11367 = (

let uu____11370 = (

let uu____11371 = (

let uu____11381 = (

let uu____11382 = (

let uu____11383 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (uu____11383)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____11382 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (

let uu____11384 = (

let uu____11386 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (

let uu____11387 = (

let uu____11389 = (FStar_Syntax_Syntax.as_arg wpc2)
in (

let uu____11390 = (

let uu____11392 = (

let uu____11393 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11393))
in (uu____11392)::[])
in (uu____11389)::uu____11390))
in (uu____11386)::uu____11387))
in ((uu____11381), (uu____11384))))
in FStar_Syntax_Syntax.Tm_app (uu____11371))
in (FStar_Syntax_Syntax.mk uu____11370))
in (uu____11367 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r))
end)
end)
in (

let base_prob = (

let uu____11404 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _0_66 -> FStar_TypeChecker_Common.TProb (_0_66)) uu____11404))
in (

let wl = (

let uu____11410 = (

let uu____11412 = (

let uu____11415 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____11415 g))
in (FStar_All.pipe_left (fun _0_67 -> Some (_0_67)) uu____11412))
in (solve_prob orig uu____11410 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end))
end)))
end)))
in (

let uu____11425 = (FStar_Util.physical_equality c1 c2)
in (match (uu____11425) with
| true -> begin
(

let uu____11426 = (solve_prob orig None [] wl)
in (solve env uu____11426))
end
| uu____11427 -> begin
((

let uu____11429 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11429) with
| true -> begin
(

let uu____11430 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____11431 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____11430 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____11431)))
end
| uu____11432 -> begin
()
end));
(

let uu____11433 = (

let uu____11436 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____11437 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____11436), (uu____11437))))
in (match (uu____11433) with
| (c1, c2) -> begin
(match (((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____11441), FStar_Syntax_Syntax.Total (t2, uu____11443)) when (FStar_Syntax_Util.non_informative t2) -> begin
(

let uu____11456 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env uu____11456 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____11459), FStar_Syntax_Syntax.Total (uu____11460)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.Total (t2, _))) | ((FStar_Syntax_Syntax.GTotal (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) | ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) -> begin
(

let uu____11509 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env uu____11509 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(

let uu____11516 = (

let uu___166_11519 = problem
in (

let uu____11522 = (

let uu____11523 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____11523))
in {FStar_TypeChecker_Common.pid = uu___166_11519.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____11522; FStar_TypeChecker_Common.relation = uu___166_11519.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___166_11519.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___166_11519.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_11519.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___166_11519.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___166_11519.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_11519.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_11519.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____11516 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(

let uu____11528 = (

let uu___167_11531 = problem
in (

let uu____11534 = (

let uu____11535 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c2)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____11535))
in {FStar_TypeChecker_Common.pid = uu___167_11531.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___167_11531.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___167_11531.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____11534; FStar_TypeChecker_Common.element = uu___167_11531.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___167_11531.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___167_11531.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___167_11531.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___167_11531.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___167_11531.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____11528 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____11536), FStar_Syntax_Syntax.Comp (uu____11537)) -> begin
(

let uu____11538 = (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2))))
in (match (uu____11538) with
| true -> begin
(

let uu____11539 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env uu____11539 wl))
end
| uu____11542 -> begin
(

let c1_comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c1)
in (

let c2_comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c2)
in (match (((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name))) with
| true -> begin
(solve_eq c1_comp c2_comp)
end
| uu____11545 -> begin
(

let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (

let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in ((

let uu____11549 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11549) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____11550 -> begin
()
end));
(

let uu____11551 = (FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (uu____11551) with
| None -> begin
(

let uu____11553 = (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (

let uu____11554 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative uu____11554)))
in (match (uu____11553) with
| true -> begin
(

let edge = {FStar_TypeChecker_Env.msource = c1.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c2.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = (fun r t -> t)}
in (solve_sub c1 edge c2))
end
| uu____11558 -> begin
(

let uu____11559 = (

let uu____11560 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____11561 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____11560 uu____11561)))
in (giveup env uu____11559 orig))
end))
end
| Some (edge) -> begin
(solve_sub c1 edge c2)
end));
)))
end)))
end))
end)
end));
)
end)))))))))


let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (

let uu____11566 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____11586 -> (match (uu____11586) with
| (uu____11597, uu____11598, u, uu____11600, uu____11601, uu____11602) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____11566 (FStar_String.concat ", "))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred))) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| uu____11626 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____11631 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____11631) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____11632 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____11634 = (FStar_List.map (fun uu____11638 -> (match (uu____11638) with
| (uu____11641, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right uu____11634 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu____11662; FStar_TypeChecker_Env.implicits = uu____11663} -> begin
true
end
| uu____11674 -> begin
false
end))


let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []}


let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _; FStar_TypeChecker_Env.univ_ineqs = _; FStar_TypeChecker_Env.implicits = _})) -> begin
g
end
| Some (g) -> begin
(

let f = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| uu____11699 -> begin
(failwith "impossible")
end)
in (

let uu____11700 = (

let uu___168_11701 = g
in (

let uu____11702 = (

let uu____11703 = (

let uu____11704 = (

let uu____11708 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____11708)::[])
in (

let uu____11709 = (

let uu____11716 = (

let uu____11722 = (

let uu____11723 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____11723 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____11722 (fun _0_68 -> FStar_Util.Inl (_0_68))))
in Some (uu____11716))
in (FStar_Syntax_Util.abs uu____11704 f uu____11709)))
in (FStar_All.pipe_left (fun _0_69 -> FStar_TypeChecker_Common.NonTrivial (_0_69)) uu____11703))
in {FStar_TypeChecker_Env.guard_f = uu____11702; FStar_TypeChecker_Env.deferred = uu___168_11701.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___168_11701.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___168_11701.FStar_TypeChecker_Env.implicits}))
in Some (uu____11700)))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___169_11744 = g
in (

let uu____11745 = (

let uu____11746 = (

let uu____11747 = (

let uu____11750 = (

let uu____11751 = (

let uu____11761 = (

let uu____11763 = (FStar_Syntax_Syntax.as_arg e)
in (uu____11763)::[])
in ((f), (uu____11761)))
in FStar_Syntax_Syntax.Tm_app (uu____11751))
in (FStar_Syntax_Syntax.mk uu____11750))
in (uu____11747 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _0_70 -> FStar_TypeChecker_Common.NonTrivial (_0_70)) uu____11746))
in {FStar_TypeChecker_Env.guard_f = uu____11745; FStar_TypeChecker_Env.deferred = uu___169_11744.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___169_11744.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___169_11744.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____11776) -> begin
(failwith "impossible")
end))


let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let uu____11786 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (uu____11786))
end))


let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____11795 -> begin
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

let uu____11826 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = uu____11826; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___170_11854 = g
in (

let uu____11855 = (

let uu____11856 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right uu____11856 (fun _0_71 -> FStar_TypeChecker_Common.NonTrivial (_0_71))))
in {FStar_TypeChecker_Env.guard_f = uu____11855; FStar_TypeChecker_Env.deferred = uu___170_11854.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___170_11854.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___170_11854.FStar_TypeChecker_Env.implicits}))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = (

let uu____11894 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____11894) with
| true -> begin
(

let uu____11895 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____11896 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____11895 (rel_to_string rel) uu____11896)))
end
| uu____11897 -> begin
"TOP"
end))
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (

let uu____11916 = (

let uu____11918 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_72 -> Some (_0_72)) uu____11918))
in (FStar_Syntax_Syntax.new_bv uu____11916 t1))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (

let uu____11924 = (

let uu____11926 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _0_73 -> Some (_0_73)) uu____11926))
in (

let uu____11928 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 uu____11924 uu____11928)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (

let probs = (

let uu____11951 = (FStar_Options.eager_inference ())
in (match (uu____11951) with
| true -> begin
(

let uu___171_11952 = probs
in {attempting = uu___171_11952.attempting; wl_deferred = uu___171_11952.wl_deferred; ctr = uu___171_11952.ctr; defer_ok = false; smt_ok = uu___171_11952.smt_ok; tcenv = uu___171_11952.tcenv})
end
| uu____11953 -> begin
probs
end))
in (

let tx = (FStar_Unionfind.new_transaction ())
in (

let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
((FStar_Unionfind.commit tx);
Some (deferred);
)
end
| Failed (d, s) -> begin
((FStar_Unionfind.rollback tx);
(

let uu____11963 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____11963) with
| true -> begin
(

let uu____11964 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____11964))
end
| uu____11965 -> begin
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

let uu____11974 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____11974) with
| true -> begin
(

let uu____11975 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____11975))
end
| uu____11976 -> begin
()
end));
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in ((

let uu____11979 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____11979) with
| true -> begin
(

let uu____11980 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____11980))
end
| uu____11981 -> begin
()
end));
(

let f = (

let uu____11983 = (

let uu____11984 = (FStar_Syntax_Util.unmeta f)
in uu____11984.FStar_Syntax_Syntax.n)
in (match (uu____11983) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____11988 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end))
in (

let uu___172_11989 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = uu___172_11989.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___172_11989.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___172_11989.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(

let uu____12004 = (

let uu____12005 = (

let uu____12006 = (

let uu____12007 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right uu____12007 (fun _0_74 -> FStar_TypeChecker_Common.NonTrivial (_0_74))))
in {FStar_TypeChecker_Env.guard_f = uu____12006; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env uu____12005))
in (FStar_All.pipe_left (fun _0_75 -> Some (_0_75)) uu____12004))
end))


let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> ((

let uu____12029 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12029) with
| true -> begin
(

let uu____12030 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12031 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" uu____12030 uu____12031)))
end
| uu____12032 -> begin
()
end));
(

let prob = (

let uu____12034 = (

let uu____12037 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None uu____12037))
in (FStar_All.pipe_left (fun _0_76 -> FStar_TypeChecker_Common.TProb (_0_76)) uu____12034))
in (

let g = (

let uu____12042 = (

let uu____12044 = (singleton env prob)
in (solve_and_commit env uu____12044 (fun uu____12045 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12042))
in g));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____12059 = (try_teq env t1 t2)
in (match (uu____12059) with
| None -> begin
(

let uu____12061 = (

let uu____12062 = (

let uu____12065 = (FStar_TypeChecker_Err.basic_type_error env None t2 t1)
in (

let uu____12066 = (FStar_TypeChecker_Env.get_range env)
in ((uu____12065), (uu____12066))))
in FStar_Errors.Error (uu____12062))
in (Prims.raise uu____12061))
end
| Some (g) -> begin
((

let uu____12069 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12069) with
| true -> begin
(

let uu____12070 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12071 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____12072 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____12070 uu____12071 uu____12072))))
end
| uu____12073 -> begin
()
end));
g;
)
end)))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 smt_ok -> ((

let uu____12088 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12088) with
| true -> begin
(

let uu____12089 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____12090 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" uu____12089 uu____12090)))
end
| uu____12091 -> begin
()
end));
(

let uu____12092 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____12092) with
| (prob, x) -> begin
(

let g = (

let uu____12100 = (

let uu____12102 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____12102 (fun uu____12103 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12100))
in ((

let uu____12109 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____12109) with
| true -> begin
(

let uu____12110 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____12111 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____12112 = (

let uu____12113 = (FStar_Util.must g)
in (guard_to_string env uu____12113))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" uu____12110 uu____12111 uu____12112))))
end
| uu____12114 -> begin
()
end));
(abstract_guard x g);
))
end));
))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env e t1 t2 -> (

let uu____12137 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12138 = (FStar_TypeChecker_Err.basic_type_error env (Some (e)) t2 t1)
in (FStar_Errors.report uu____12137 uu____12138))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> ((

let uu____12150 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12150) with
| true -> begin
(

let uu____12151 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____12152 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" uu____12151 uu____12152)))
end
| uu____12153 -> begin
()
end));
(

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____12155 -> begin
FStar_TypeChecker_Common.SUB
end)
in (

let prob = (

let uu____12157 = (

let uu____12160 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None uu____12160 "sub_comp"))
in (FStar_All.pipe_left (fun _0_77 -> FStar_TypeChecker_Common.CProb (_0_77)) uu____12157))
in (

let uu____12163 = (

let uu____12165 = (singleton env prob)
in (solve_and_commit env uu____12165 (fun uu____12166 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12163))));
))


let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (

let fail = (fun msg u1 u2 -> ((FStar_Unionfind.rollback tx);
(

let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (

let uu____12201 = (

let uu____12202 = (

let uu____12205 = (

let uu____12206 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____12207 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" uu____12206 uu____12207 msg)))
in (

let uu____12208 = (FStar_TypeChecker_Env.get_range env)
in ((uu____12205), (uu____12208))))
in FStar_Errors.Error (uu____12202))
in (Prims.raise uu____12201)));
))
in (

let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
(((uv), ((u1)::[])))::[]
end
| (hd)::tl -> begin
(

let uu____12283 = hd
in (match (uu____12283) with
| (uv', lower_bounds) -> begin
(

let uu____12303 = (FStar_Unionfind.equivalent uv uv')
in (match (uu____12303) with
| true -> begin
(((uv'), ((u1)::lower_bounds)))::tl
end
| uu____12319 -> begin
(

let uu____12320 = (insert uv u1 tl)
in (hd)::uu____12320)
end))
end))
end))
in (

let rec group_by = (fun out ineqs -> (match (ineqs) with
| [] -> begin
Some (out)
end
| ((u1, u2))::rest -> begin
(

let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u2) with
| FStar_Syntax_Syntax.U_unif (uv) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (

let uu____12399 = (FStar_Syntax_Util.eq_univs u1 u2)
in (match (uu____12399) with
| true -> begin
(group_by out rest)
end
| uu____12407 -> begin
(

let uu____12408 = (insert uv u1 out)
in (group_by uu____12408 rest))
end)))
end
| uu____12415 -> begin
None
end))
end))
in (

let ad_hoc_fallback = (fun uu____12425 -> (match (ineqs) with
| [] -> begin
()
end
| uu____12428 -> begin
(

let wl = (

let uu___173_12433 = (empty_worklist env)
in {attempting = uu___173_12433.attempting; wl_deferred = uu___173_12433.wl_deferred; ctr = uu___173_12433.ctr; defer_ok = true; smt_ok = uu___173_12433.smt_ok; tcenv = uu___173_12433.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun uu____12439 -> (match (uu____12439) with
| (u1, u2) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| uu____12446 -> begin
(

let uu____12447 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl u1 u2)
in (match (uu____12447) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(

let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| uu____12455 -> begin
(u1)::[]
end)
in (

let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| uu____12461 -> begin
(u2)::[]
end)
in (

let uu____12462 = (FStar_All.pipe_right us1 (FStar_Util.for_all (fun uu___127_12464 -> (match (uu___127_12464) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(

let uu____12466 = (FStar_Syntax_Util.univ_kernel u)
in (match (uu____12466) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (

let uu____12473 = (FStar_Syntax_Util.univ_kernel u')
in (match (uu____12473) with
| (k_u', n') -> begin
((FStar_Syntax_Util.eq_univs k_u k_u') && (n <= n'))
end)))))
end))
end))))
in (match (uu____12462) with
| true -> begin
()
end
| uu____12478 -> begin
(fail None u1 u2)
end))))
end
| USolved (uu____12479) -> begin
()
end))
end)))
end)))))
end))
in (

let uu____12480 = (group_by [] ineqs)
in (match (uu____12480) with
| Some (groups) -> begin
(

let wl = (

let uu___174_12507 = (empty_worklist env)
in {attempting = uu___174_12507.attempting; wl_deferred = uu___174_12507.wl_deferred; ctr = uu___174_12507.ctr; defer_ok = false; smt_ok = uu___174_12507.smt_ok; tcenv = uu___174_12507.tcenv})
in (

let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| ((u, lower_bounds))::groups -> begin
(

let uu____12552 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))
in (match (uu____12552) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| uu____12554 -> begin
(ad_hoc_fallback ())
end))
end))
in (solve_all_groups wl groups)))
end
| None -> begin
(ad_hoc_fallback ())
end)))))))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun env ineqs -> (

let tx = (FStar_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Unionfind.commit tx);
)))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail = (fun uu____12587 -> (match (uu____12587) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Errors.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in ((

let uu____12597 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____12597) with
| true -> begin
(

let uu____12598 = (wl_to_string wl)
in (

let uu____12599 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" uu____12598 uu____12599)))
end
| uu____12609 -> begin
()
end));
(

let g = (

let uu____12611 = (solve_and_commit env wl fail)
in (match (uu____12611) with
| Some ([]) -> begin
(

let uu___175_12618 = g
in {FStar_TypeChecker_Env.guard_f = uu___175_12618.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu___175_12618.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___175_12618.FStar_TypeChecker_Env.implicits})
end
| uu____12621 -> begin
(failwith "impossible: Unexpected deferred constraints remain")
end))
in ((solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___176_12624 = g
in {FStar_TypeChecker_Env.guard_f = uu___176_12624.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___176_12624.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = uu___176_12624.FStar_TypeChecker_Env.implicits});
));
))))


let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (

let g = (solve_deferred_constraints env g)
in ((

let uu____12643 = (

let uu____12644 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12644)))
in (match (uu____12643) with
| true -> begin
()
end
| uu____12645 -> begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((

let uu____12648 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Norm")))
in (match (uu____12648) with
| true -> begin
(

let uu____12649 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12650 = (

let uu____12651 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____12651))
in (FStar_Errors.diag uu____12649 uu____12650)))
end
| uu____12652 -> begin
()
end));
(

let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((

let uu____12656 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12656) with
| true -> begin
(

let uu____12657 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12658 = (

let uu____12659 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____12659))
in (FStar_Errors.diag uu____12657 uu____12658)))
end
| uu____12660 -> begin
()
end));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc);
)
end));
)
end)
end));
(

let uu___177_12661 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___177_12661.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___177_12661.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___177_12661.FStar_TypeChecker_Env.implicits});
)))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (

let uu____12685 = (FStar_Unionfind.find u)
in (match (uu____12685) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| uu____12694 -> begin
false
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____12709 = acc
in (match (uu____12709) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____12720 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd)::tl -> begin
(

let uu____12755 = hd
in (match (uu____12755) with
| (uu____12762, env, u, tm, k, r) -> begin
(

let uu____12768 = (unresolved u)
in (match (uu____12768) with
| true -> begin
(until_fixpoint (((hd)::out), (changed)) tl)
end
| uu____12782 -> begin
(

let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in ((

let uu____12786 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____12786) with
| true -> begin
(

let uu____12787 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____12791 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____12792 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" uu____12787 uu____12791 uu____12792))))
end
| uu____12793 -> begin
()
end));
(

let uu____12794 = (env.FStar_TypeChecker_Env.type_of (

let uu___178_12798 = env
in {FStar_TypeChecker_Env.solver = uu___178_12798.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___178_12798.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___178_12798.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___178_12798.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___178_12798.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___178_12798.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___178_12798.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___178_12798.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___178_12798.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___178_12798.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___178_12798.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___178_12798.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___178_12798.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___178_12798.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___178_12798.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___178_12798.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___178_12798.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___178_12798.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___178_12798.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___178_12798.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___178_12798.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___178_12798.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___178_12798.FStar_TypeChecker_Env.qname_and_index}) tm)
in (match (uu____12794) with
| (uu____12799, uu____12800, g) -> begin
(

let g = (match (env.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___179_12803 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___179_12803.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___179_12803.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___179_12803.FStar_TypeChecker_Env.implicits})
end
| uu____12804 -> begin
g
end)
in (

let g' = (discharge_guard' (Some ((fun uu____12808 -> (FStar_Syntax_Print.term_to_string tm)))) env g)
in (until_fixpoint (((FStar_List.append g'.FStar_TypeChecker_Env.implicits out)), (true)) tl)))
end));
)))
end))
end))
end)
end)))
in (

let uu___180_12822 = g
in (

let uu____12823 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___180_12822.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___180_12822.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___180_12822.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____12823})))))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g = (

let uu____12851 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____12851 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(

let uu____12858 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore uu____12858))
end
| ((reason, uu____12860, uu____12861, e, t, r))::uu____12865 -> begin
(

let uu____12879 = (

let uu____12880 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____12881 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" uu____12880 uu____12881 reason)))
in (FStar_Errors.report r uu____12879))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___181_12888 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___181_12888.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___181_12888.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (((u1), (u2)))::[]; FStar_TypeChecker_Env.implicits = uu___181_12888.FStar_TypeChecker_Env.implicits}))





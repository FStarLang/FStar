
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

let uu___127_483 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = uu___127_483.wl_deferred; ctr = uu___127_483.ctr; defer_ok = uu___127_483.defer_ok; smt_ok = smt_ok; tcenv = uu___127_483.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard = (fun env g -> (

let uu___128_508 = (empty_worklist env)
in (

let uu____509 = (FStar_List.map Prims.snd g)
in {attempting = uu____509; wl_deferred = uu___128_508.wl_deferred; ctr = uu___128_508.ctr; defer_ok = false; smt_ok = uu___128_508.smt_ok; tcenv = uu___128_508.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu___129_521 = wl
in {attempting = uu___129_521.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = uu___129_521.ctr; defer_ok = uu___129_521.defer_ok; smt_ok = uu___129_521.smt_ok; tcenv = uu___129_521.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let uu___130_533 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = uu___130_533.wl_deferred; ctr = uu___130_533.ctr; defer_ok = uu___130_533.defer_ok; smt_ok = uu___130_533.smt_ok; tcenv = uu___130_533.tcenv}))


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

let uu___131_565 = p
in {FStar_TypeChecker_Common.pid = uu___131_565.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = uu___131_565.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___131_565.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___131_565.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___131_565.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___131_565.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___131_565.FStar_TypeChecker_Common.rank}))


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

let uu____876 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____876) with
| true -> begin
(

let uu____877 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (

let uu____878 = (prob_to_string env d)
in (

let uu____879 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" uu____877 uu____878 uu____879 s))))
end
| uu____881 -> begin
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
| uu____884 -> begin
(failwith "impossible")
end)
in (

let uu____885 = (match (d) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____893 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (

let uu____894 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((uu____893), (uu____894))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____898 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (

let uu____899 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((uu____898), (uu____899))))
end)
in (match (uu____885) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___112_908 -> (match (uu___112_908) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| uu____915 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, uu____918), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun uu___113_941 -> (match (uu___113_941) with
| UNIV (uu____943) -> begin
None
end
| TERM ((u, uu____947), t) -> begin
(

let uu____951 = (FStar_Unionfind.equivalent uv u)
in (match (uu____951) with
| true -> begin
Some (t)
end
| uu____956 -> begin
None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun uu___114_970 -> (match (uu___114_970) with
| UNIV (u', t) -> begin
(

let uu____974 = (FStar_Unionfind.equivalent u u')
in (match (uu____974) with
| true -> begin
Some (t)
end
| uu____977 -> begin
None
end))
end
| uu____978 -> begin
None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____985 = (

let uu____986 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____986))
in (FStar_Syntax_Subst.compress uu____985)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____993 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress uu____993)))


let norm_arg = (fun env t -> (

let uu____1012 = (sn env (Prims.fst t))
in ((uu____1012), ((Prims.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____1029 -> (match (uu____1029) with
| (x, imp) -> begin
(

let uu____1036 = (

let uu___132_1037 = x
in (

let uu____1038 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___132_1037.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___132_1037.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1038}))
in ((uu____1036), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(

let uu____1053 = (aux u)
in FStar_Syntax_Syntax.U_succ (uu____1053))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1056 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____1056))
end
| uu____1058 -> begin
u
end)))
in (

let uu____1059 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1059))))


let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement = (fun env wl t1 -> (

let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(match (norm) with
| true -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| uu____1165 -> begin
(

let uu____1166 = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (match (uu____1166) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = uu____1178; FStar_Syntax_Syntax.pos = uu____1179; FStar_Syntax_Syntax.vars = uu____1180} -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| tt -> begin
(

let uu____1201 = (

let uu____1202 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____1203 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1202 uu____1203)))
in (failwith uu____1201))
end))
end)
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(match (norm) with
| true -> begin
((t1), (None))
end
| uu____1236 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (

let uu____1238 = (

let uu____1239 = (FStar_Syntax_Subst.compress t1')
in uu____1239.FStar_Syntax_Syntax.n)
in (match (uu____1238) with
| FStar_Syntax_Syntax.Tm_refine (uu____1251) -> begin
(aux true t1')
end
| uu____1256 -> begin
((t1), (None))
end)))
end)
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
((t1), (None))
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(

let uu____1291 = (

let uu____1292 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1293 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1292 uu____1293)))
in (failwith uu____1291))
end))
in (

let uu____1303 = (whnf env t1)
in (aux false uu____1303))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____1312 = (

let uu____1322 = (empty_worklist env)
in (base_and_refinement env uu____1322 t))
in (FStar_All.pipe_right uu____1312 Prims.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (

let uu____1346 = (FStar_Syntax_Syntax.null_bv t)
in ((uu____1346), (FStar_Syntax_Util.t_true))))


let as_refinement = (fun env wl t -> (

let uu____1366 = (base_and_refinement env wl t)
in (match (uu____1366) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement = (fun uu____1425 -> (match (uu____1425) with
| (t_base, refopt) -> begin
(

let uu____1439 = (match (refopt) with
| Some (y, phi) -> begin
((y), (phi))
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (uu____1439) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl uu___115_1463 -> (match (uu___115_1463) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____1467 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1468 = (

let uu____1469 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string uu____1469))
in (

let uu____1470 = (

let uu____1471 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string uu____1471))
in (FStar_Util.format4 "%s: %s  (%s)  %s" uu____1467 uu____1468 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1470))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____1475 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1476 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____1477 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" uu____1475 uu____1476 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1477))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (

let uu____1481 = (

let uu____1483 = (

let uu____1485 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____1495 -> (match (uu____1495) with
| (uu____1499, uu____1500, x) -> begin
x
end))))
in (FStar_List.append wl.attempting uu____1485))
in (FStar_List.map (wl_prob_to_string wl) uu____1483))
in (FStar_All.pipe_right uu____1481 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____1518 = (

let uu____1528 = (

let uu____1529 = (FStar_Syntax_Subst.compress k)
in uu____1529.FStar_Syntax_Syntax.n)
in (match (uu____1528) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (((FStar_List.length bs) = (FStar_List.length ys))) with
| true -> begin
(

let uu____1570 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (uu____1570)))
end
| uu____1583 -> begin
(

let uu____1584 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____1584) with
| (ys', t, uu____1605) -> begin
(

let uu____1618 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t))), (uu____1618)))
end))
end)
end
| uu____1639 -> begin
(

let uu____1640 = (

let uu____1646 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____1646)))
in ((((ys), (t))), (uu____1640)))
end))
in (match (uu____1518) with
| ((ys, t), (xs, c)) -> begin
(match (((FStar_List.length xs) <> (FStar_List.length ys))) with
| true -> begin
(FStar_Syntax_Util.abs ys t (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ([]))))))
end
| uu____1699 -> begin
(

let c = (

let uu____1701 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp uu____1701 c))
in (

let uu____1703 = (

let uu____1710 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_32 -> FStar_Util.Inl (_0_32)))
in (FStar_All.pipe_right uu____1710 (fun _0_33 -> Some (_0_33))))
in (FStar_Syntax_Util.abs ys t uu____1703)))
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

let uu____1761 = (p_guard prob)
in (match (uu____1761) with
| (uu____1764, uv) -> begin
((

let uu____1767 = (

let uu____1768 = (FStar_Syntax_Subst.compress uv)
in uu____1768.FStar_Syntax_Syntax.n)
in (match (uu____1767) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi = (u_abs k bs phi)
in ((

let uu____1788 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____1788) with
| true -> begin
(

let uu____1789 = (FStar_Util.string_of_int (p_pid prob))
in (

let uu____1790 = (FStar_Syntax_Print.term_to_string uv)
in (

let uu____1791 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" uu____1789 uu____1790 uu____1791))))
end
| uu____1792 -> begin
()
end));
(FStar_Syntax_Util.set_uvar uvar phi);
)))
end
| uu____1795 -> begin
(match ((not (resolve_ok))) with
| true -> begin
(failwith "Impossible: this instance has already been assigned a solution")
end
| uu____1796 -> begin
()
end)
end));
(commit uvis);
(

let uu___133_1798 = wl
in {attempting = uu___133_1798.attempting; wl_deferred = uu___133_1798.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___133_1798.defer_ok; smt_ok = uu___133_1798.smt_ok; tcenv = uu___133_1798.tcenv});
)
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____1811 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____1811) with
| true -> begin
(

let uu____1812 = (FStar_Util.string_of_int pid)
in (

let uu____1813 = (

let uu____1814 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right uu____1814 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____1812 uu____1813)))
end
| uu____1817 -> begin
()
end));
(commit sol);
(

let uu___134_1819 = wl
in {attempting = uu___134_1819.attempting; wl_deferred = uu___134_1819.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___134_1819.defer_ok; smt_ok = uu___134_1819.smt_ok; tcenv = uu___134_1819.tcenv});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard = (fun t g -> (match (((t), (g))) with
| (uu____1848, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(

let uu____1856 = (FStar_Syntax_Util.mk_conj t f)
in Some (uu____1856))
end))
in ((

let uu____1862 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____1862) with
| true -> begin
(

let uu____1863 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (

let uu____1864 = (

let uu____1865 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right uu____1865 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____1863 uu____1864)))
end
| uu____1868 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
)))


let rec occurs = (fun wl uk t -> (

let uu____1890 = (

let uu____1894 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right uu____1894 FStar_Util.set_elements))
in (FStar_All.pipe_right uu____1890 (FStar_Util.for_some (fun uu____1915 -> (match (uu____1915) with
| (uv, uu____1923) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (

let uu____1967 = (occurs wl uk t)
in (not (uu____1967)))
in (

let msg = (match (occurs_ok) with
| true -> begin
None
end
| uu____1971 -> begin
(

let uu____1972 = (

let uu____1973 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (

let uu____1977 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" uu____1973 uu____1977)))
in Some (uu____1972))
end)
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let uu____2025 = (occurs_check env wl uk t)
in (match (uu____2025) with
| (occurs_ok, msg) -> begin
(

let uu____2042 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (uu____2042), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set v1)
in (

let uu____2106 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____2130 uu____2131 -> (match (((uu____2130), (uu____2131))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____2174 = (

let uu____2175 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation uu____2175))
in (match (uu____2174) with
| true -> begin
((isect), (isect_set))
end
| uu____2186 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____2189 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____2189) with
| true -> begin
(

let uu____2196 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (uu____2196)))
end
| uu____2204 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (uu____2106) with
| (isect, uu____2218) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____2267 uu____2268 -> (match (((uu____2267), (uu____2268))) with
| ((a, uu____2278), (b, uu____2280)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(

let uu____2324 = (FStar_All.pipe_right seen (FStar_Util.for_some (fun uu____2330 -> (match (uu____2330) with
| (b, uu____2334) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end))))
in (match (uu____2324) with
| true -> begin
None
end
| uu____2340 -> begin
Some (((a), ((Prims.snd hd))))
end))
end
| uu____2343 -> begin
None
end)))


let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| (hd)::rest -> begin
(

let uu____2386 = (pat_var_opt env seen hd)
in (match (uu____2386) with
| None -> begin
((

let uu____2394 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____2394) with
| true -> begin
(

let uu____2395 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" uu____2395))
end
| uu____2396 -> begin
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

let uu____2407 = (

let uu____2408 = (FStar_Syntax_Subst.compress t)
in uu____2408.FStar_Syntax_Syntax.n)
in (match (uu____2407) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
true
end
| uu____2424 -> begin
false
end)))


let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = uu____2486; FStar_Syntax_Syntax.pos = uu____2487; FStar_Syntax_Syntax.vars = uu____2488}, args) -> begin
((t), (uv), (k), (args))
end
| uu____2529 -> begin
(failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let uu____2583 = (destruct_flex_t t)
in (match (uu____2583) with
| (t, uv, k, args) -> begin
(

let uu____2651 = (pat_vars env [] args)
in (match (uu____2651) with
| Some (vars) -> begin
((((t), (uv), (k), (args))), (Some (vars)))
end
| uu____2707 -> begin
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
| uu____2755 -> begin
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
| uu____2778 -> begin
false
end))


let uu___is_FullMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullMatch -> begin
true
end
| uu____2782 -> begin
false
end))


let head_match : match_result  ->  match_result = (fun uu___116_2785 -> (match (uu___116_2785) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____2794 -> begin
HeadMatch
end))


let fv_delta_depth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.delta_depth = (fun env fv -> (match (fv.FStar_Syntax_Syntax.fv_delta) with
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(match ((env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)) with
| true -> begin
d
end
| uu____2806 -> begin
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
| uu____2879 -> begin
MisMatch (((None), (None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____2884 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____2884) with
| true -> begin
FullMatch
end
| uu____2885 -> begin
MisMatch (((Some ((fv_delta_depth env f))), (Some ((fv_delta_depth env g)))))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____2889), FStar_Syntax_Syntax.Tm_uinst (g, uu____2891)) -> begin
(

let uu____2900 = (head_matches env f g)
in (FStar_All.pipe_right uu____2900 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(match ((c = d)) with
| true -> begin
FullMatch
end
| uu____2903 -> begin
MisMatch (((None), (None)))
end)
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, uu____2907), FStar_Syntax_Syntax.Tm_uvar (uv', uu____2909)) -> begin
(

let uu____2934 = (FStar_Unionfind.equivalent uv uv')
in (match (uu____2934) with
| true -> begin
FullMatch
end
| uu____2938 -> begin
MisMatch (((None), (None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____2942), FStar_Syntax_Syntax.Tm_refine (y, uu____2944)) -> begin
(

let uu____2953 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____2953 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____2955), uu____2956) -> begin
(

let uu____2961 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right uu____2961 head_match))
end
| (uu____2962, FStar_Syntax_Syntax.Tm_refine (x, uu____2964)) -> begin
(

let uu____2969 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____2969 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, uu____2975), FStar_Syntax_Syntax.Tm_app (head', uu____2977)) -> begin
(

let uu____3006 = (head_matches env head head')
in (FStar_All.pipe_right uu____3006 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head, uu____3008), uu____3009) -> begin
(

let uu____3024 = (head_matches env head t2)
in (FStar_All.pipe_right uu____3024 head_match))
end
| (uu____3025, FStar_Syntax_Syntax.Tm_app (head, uu____3027)) -> begin
(

let uu____3042 = (head_matches env t1 head)
in (FStar_All.pipe_right uu____3042 head_match))
end
| uu____3043 -> begin
(

let uu____3046 = (

let uu____3051 = (delta_depth_of_term env t1)
in (

let uu____3053 = (delta_depth_of_term env t2)
in ((uu____3051), (uu____3053))))
in MisMatch (uu____3046))
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let uu____3089 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____3089) with
| (head, uu____3101) -> begin
(

let uu____3116 = (

let uu____3117 = (FStar_Syntax_Util.un_uinst head)
in uu____3117.FStar_Syntax_Syntax.n)
in (match (uu____3116) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3122 = (

let uu____3123 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3123 FStar_Option.isSome))
in (match (uu____3122) with
| true -> begin
(

let uu____3137 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right uu____3137 (fun _0_34 -> Some (_0_34))))
end
| uu____3139 -> begin
None
end))
end
| uu____3140 -> begin
None
end))
end)))
in (

let success = (fun d r t1 t2 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
Some (((t1), (t2)))
end
| uu____3167 -> begin
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
| uu____3219 -> begin
(

let uu____3220 = (

let uu____3225 = (maybe_inline t1)
in (

let uu____3227 = (maybe_inline t2)
in ((uu____3225), (uu____3227))))
in (match (uu____3220) with
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

let uu____3252 = (FStar_TypeChecker_Common.decr_delta_depth d1)
in (match (uu____3252) with
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

let uu____3267 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in ((t1'), (t2)))
end
| uu____3273 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (

let uu____3275 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in ((t1), (uu____3275))))
end)
in (match (uu____3267) with
| (t1, t2) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t1 t2)
end)))
end
| MisMatch (uu____3283) -> begin
(fail r)
end
| uu____3288 -> begin
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
| uu____3313 -> begin
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
| uu____3343 -> begin
false
end))


let __proj__C__item___0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_0) -> begin
_0
end))


type tcs =
tc Prims.list


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____3358 = (FStar_Syntax_Util.type_u ())
in (match (uu____3358) with
| (t, uu____3362) -> begin
(

let uu____3363 = (new_uvar r binders t)
in (Prims.fst uu____3363))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____3372 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____3372 Prims.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (

let uu____3414 = (head_matches env t t')
in (match (uu____3414) with
| MisMatch (uu____3415) -> begin
false
end
| uu____3420 -> begin
true
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(

let rebuild = (fun args' -> (

let args = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((uu____3480, imp), T (t, uu____3483)) -> begin
((t), (imp))
end
| uu____3500 -> begin
(failwith "Bad reconstruction")
end)) args args')
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), (args))))) None t.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun uu____3544 -> (match (uu____3544) with
| (t, uu____3552) -> begin
((None), (INVARIANT), (T (((t), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let fail = (fun uu____3585 -> (failwith "Bad reconstruction"))
in (

let uu____3586 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3586) with
| (bs, c) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs tcs -> (match (((bs), (tcs))) with
| (((x, imp))::bs, (T (t, uu____3639))::tcs) -> begin
(aux (((((

let uu___135_3661 = x
in {FStar_Syntax_Syntax.ppname = uu___135_3661.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___135_3661.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp)))::out) bs tcs)
end
| ([], (C (c))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| uu____3671 -> begin
(failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (

let rec decompose = (fun out uu___117_3702 -> (match (uu___117_3702) with
| [] -> begin
(FStar_List.rev ((((None), (COVARIANT), (C (c))))::out))
end
| (hd)::rest -> begin
(decompose ((((Some (hd)), (CONTRAVARIANT), (T ((((Prims.fst hd).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (

let uu____3765 = (decompose [] bs)
in ((rebuild), (matches), (uu____3765)))))
end)))
end
| uu____3793 -> begin
(

let rebuild = (fun uu___118_3798 -> (match (uu___118_3798) with
| [] -> begin
t
end
| uu____3800 -> begin
(failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t -> true)), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun uu___119_3819 -> (match (uu___119_3819) with
| T (t, uu____3821) -> begin
t
end
| uu____3830 -> begin
(failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun uu___120_3833 -> (match (uu___120_3833) with
| T (t, uu____3835) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| uu____3844 -> begin
(failwith "Impossible")
end))


let imitation_sub_probs = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope args q -> (match (q) with
| (uu____3925, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope r)
in (

let uu____3944 = (new_uvar r scope k)
in (match (uu____3944) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| uu____3956 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) None r)
end)
in (

let uu____3971 = (

let uu____3972 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _0_35 -> FStar_TypeChecker_Common.TProb (_0_35)) uu____3972))
in ((T (((gi_xs), (mk_kind)))), (uu____3971))))
end)))
end
| (uu____3981, uu____3982, C (uu____3983)) -> begin
(failwith "impos")
end))
in (

let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs -> begin
(

let uu____4070 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.tk = uu____4081; FStar_Syntax_Syntax.pos = uu____4082; FStar_Syntax_Syntax.vars = uu____4083})) -> begin
(

let uu____4098 = (sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____4098) with
| (T (gi_xs, uu____4114), prob) -> begin
(

let uu____4124 = (

let uu____4125 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_36 -> C (_0_36)) uu____4125))
in ((uu____4124), ((prob)::[])))
end
| uu____4127 -> begin
(failwith "impossible")
end))
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.tk = uu____4137; FStar_Syntax_Syntax.pos = uu____4138; FStar_Syntax_Syntax.vars = uu____4139})) -> begin
(

let uu____4154 = (sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____4154) with
| (T (gi_xs, uu____4170), prob) -> begin
(

let uu____4180 = (

let uu____4181 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_37 -> C (_0_37)) uu____4181))
in ((uu____4180), ((prob)::[])))
end
| uu____4183 -> begin
(failwith "impossible")
end))
end
| (uu____4189, uu____4190, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = uu____4192; FStar_Syntax_Syntax.pos = uu____4193; FStar_Syntax_Syntax.vars = uu____4194})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((None), (INVARIANT), (T ((((Prims.fst t)), (generic_kind))))))))
in (

let components = (((None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let uu____4268 = (

let uu____4273 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right uu____4273 FStar_List.unzip))
in (match (uu____4268) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (

let uu____4302 = (

let uu____4303 = (

let uu____4306 = (FStar_List.hd tcs)
in (FStar_All.pipe_right uu____4306 un_T))
in (

let uu____4307 = (

let uu____4313 = (FStar_List.tl tcs)
in (FStar_All.pipe_right uu____4313 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____4303; FStar_Syntax_Syntax.effect_args = uu____4307; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____4302))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| uu____4318 -> begin
(

let uu____4325 = (sub_prob scope args q)
in (match (uu____4325) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (uu____4070) with
| (tc, probs) -> begin
(

let uu____4343 = (match (q) with
| (Some (b), uu____4369, uu____4370) -> begin
(

let uu____4378 = (

let uu____4382 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (uu____4382)::args)
in ((Some (b)), ((b)::scope), (uu____4378)))
end
| uu____4400 -> begin
((None), (scope), (args))
end)
in (match (uu____4343) with
| (bopt, scope, args) -> begin
(

let uu____4443 = (aux scope args qs)
in (match (uu____4443) with
| (sub_probs, tcs, f) -> begin
(

let f = (match (bopt) with
| None -> begin
(

let uu____4464 = (

let uu____4466 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::uu____4466)
in (FStar_Syntax_Util.mk_conj_l uu____4464))
end
| Some (b) -> begin
(

let uu____4478 = (

let uu____4480 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (

let uu____4481 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (uu____4480)::uu____4481))
in (FStar_Syntax_Util.mk_conj_l uu____4478))
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

let uu___136_4534 = p
in (

let uu____4537 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____4538 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___136_4534.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____4537; FStar_TypeChecker_Common.relation = uu___136_4534.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____4538; FStar_TypeChecker_Common.element = uu___136_4534.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___136_4534.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___136_4534.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___136_4534.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___136_4534.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___136_4534.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____4548 = (compress_tprob wl p)
in (FStar_All.pipe_right uu____4548 (fun _0_38 -> FStar_TypeChecker_Common.TProb (_0_38))))
end
| FStar_TypeChecker_Common.CProb (uu____4553) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (

let uu____4567 = (compress_prob wl pr)
in (FStar_All.pipe_right uu____4567 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____4573 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____4573) with
| (lh, uu____4586) -> begin
(

let uu____4601 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____4601) with
| (rh, uu____4614) -> begin
(

let uu____4629 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____4638), FStar_Syntax_Syntax.Tm_uvar (uu____4639)) -> begin
((flex_flex), (tp))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when ((tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____4664), uu____4665) -> begin
(

let uu____4674 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (uu____4674) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((flex_rigid), (tp))
end
| uu____4714 -> begin
(

let rank = (

let uu____4721 = (is_top_level_prob prob)
in (match (uu____4721) with
| true -> begin
flex_refine
end
| uu____4722 -> begin
flex_refine_inner
end))
in (

let uu____4723 = (

let uu___137_4726 = tp
in (

let uu____4729 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___137_4726.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___137_4726.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___137_4726.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____4729; FStar_TypeChecker_Common.element = uu___137_4726.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___137_4726.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___137_4726.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___137_4726.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___137_4726.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___137_4726.FStar_TypeChecker_Common.rank}))
in ((rank), (uu____4723))))
end)
end))
end
| (uu____4739, FStar_Syntax_Syntax.Tm_uvar (uu____4740)) -> begin
(

let uu____4749 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (uu____4749) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((rigid_flex), (tp))
end
| uu____4789 -> begin
(

let uu____4795 = (

let uu___138_4800 = tp
in (

let uu____4803 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___138_4800.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____4803; FStar_TypeChecker_Common.relation = uu___138_4800.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___138_4800.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___138_4800.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___138_4800.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___138_4800.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___138_4800.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___138_4800.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___138_4800.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (uu____4795)))
end)
end))
end
| (uu____4819, uu____4820) -> begin
((rigid_rigid), (tp))
end)
in (match (uu____4629) with
| (rank, tp) -> begin
(

let uu____4831 = (FStar_All.pipe_right (

let uu___139_4834 = tp
in {FStar_TypeChecker_Common.pid = uu___139_4834.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___139_4834.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___139_4834.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___139_4834.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___139_4834.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___139_4834.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___139_4834.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___139_4834.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___139_4834.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _0_39 -> FStar_TypeChecker_Common.TProb (_0_39)))
in ((rank), (uu____4831)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____4840 = (FStar_All.pipe_right (

let uu___140_4843 = cp
in {FStar_TypeChecker_Common.pid = uu___140_4843.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___140_4843.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___140_4843.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___140_4843.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___140_4843.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___140_4843.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___140_4843.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___140_4843.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___140_4843.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _0_40 -> FStar_TypeChecker_Common.CProb (_0_40)))
in ((rigid_rigid), (uu____4840)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun uu____4875 probs -> (match (uu____4875) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
((min), (out), (min_rank))
end
| (hd)::tl -> begin
(

let uu____4905 = (rank wl hd)
in (match (uu____4905) with
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
| uu____4930 -> begin
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
| uu____4946 -> begin
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
| uu____4970 -> begin
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
| uu____4982 -> begin
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
| uu____4994 -> begin
false
end))


let __proj__UFailed__item___0 : univ_eq_sol  ->  Prims.string = (fun projectee -> (match (projectee) with
| UFailed (_0) -> begin
_0
end))


let rec really_solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun pid_orig wl u1 u2 -> (

let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (

let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (

let uu____5031 = (FStar_Syntax_Util.univ_kernel u)
in (match (uu____5031) with
| (k, uu____5035) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| uu____5040 -> begin
false
end)
end)))))
end
| uu____5041 -> begin
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

let uu____5084 = (really_solve_universe_eq pid_orig wl u1 u2)
in (match (uu____5084) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed -> begin
failed
end))
end
| uu____5087 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end
| uu____5092 -> begin
(

let uu____5093 = (

let uu____5094 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____5095 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" uu____5094 uu____5095)))
in UFailed (uu____5093))
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

let uu____5112 = (really_solve_universe_eq pid_orig wl u u')
in (match (uu____5112) with
| USolved (wl) -> begin
(aux wl us)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____5115 -> begin
(

let uu____5118 = (

let uu____5119 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____5120 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" uu____5119 uu____5120 msg)))
in UFailed (uu____5118))
end))
in (match (((u1), (u2))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(

let uu____5127 = (

let uu____5128 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____5129 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____5128 uu____5129)))
in (failwith uu____5127))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((x.FStar_Ident.idText = y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____5132 -> begin
UFailed ("Incompatible universes")
end)
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
USolved (wl)
end
| (FStar_Syntax_Syntax.U_succ (u1), FStar_Syntax_Syntax.U_succ (u2)) -> begin
(really_solve_universe_eq pid_orig wl u1 u2)
end
| (FStar_Syntax_Syntax.U_unif (v1), FStar_Syntax_Syntax.U_unif (v2)) -> begin
(

let uu____5141 = (FStar_Unionfind.equivalent v1 v2)
in (match (uu____5141) with
| true -> begin
USolved (wl)
end
| uu____5143 -> begin
(

let wl = (extend_solution pid_orig ((UNIV (((v1), (u2))))::[]) wl)
in USolved (wl))
end))
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(

let u = (norm_univ wl u)
in (

let uu____5154 = (occurs_univ v1 u)
in (match (uu____5154) with
| true -> begin
(

let uu____5155 = (

let uu____5156 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____5157 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____5156 uu____5157)))
in (try_umax_components u1 u2 uu____5155))
end
| uu____5158 -> begin
(

let uu____5159 = (extend_solution pid_orig ((UNIV (((v1), (u))))::[]) wl)
in USolved (uu____5159))
end)))
end
| ((FStar_Syntax_Syntax.U_max (_), _)) | ((_, FStar_Syntax_Syntax.U_max (_))) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____5166 -> begin
(

let u1 = (norm_univ wl u1)
in (

let u2 = (norm_univ wl u2)
in (

let uu____5169 = (FStar_Syntax_Util.eq_univs u1 u2)
in (match (uu____5169) with
| true -> begin
USolved (wl)
end
| uu____5170 -> begin
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
| uu____5191 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders = (fun bc1 bc2 -> (

let uu____5240 = bc1
in (match (uu____5240) with
| (bs1, mk_cod1) -> begin
(

let uu____5265 = bc2
in (match (uu____5265) with
| (bs2, mk_cod2) -> begin
(

let curry = (fun n bs mk_cod -> (

let uu____5312 = (FStar_Util.first_N n bs)
in (match (uu____5312) with
| (bs, rest) -> begin
(

let uu____5326 = (mk_cod rest)
in ((bs), (uu____5326)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(

let uu____5344 = (

let uu____5348 = (mk_cod1 [])
in ((bs1), (uu____5348)))
in (

let uu____5350 = (

let uu____5354 = (mk_cod2 [])
in ((bs2), (uu____5354)))
in ((uu____5344), (uu____5350))))
end
| uu____5362 -> begin
(match ((l1 > l2)) with
| true -> begin
(

let uu____5376 = (curry l2 bs1 mk_cod1)
in (

let uu____5383 = (

let uu____5387 = (mk_cod2 [])
in ((bs2), (uu____5387)))
in ((uu____5376), (uu____5383))))
end
| uu____5395 -> begin
(

let uu____5396 = (

let uu____5400 = (mk_cod1 [])
in ((bs1), (uu____5400)))
in (

let uu____5402 = (curry l1 bs2 mk_cod2)
in ((uu____5396), (uu____5402))))
end)
end))))
end))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____5506 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5506) with
| true -> begin
(

let uu____5507 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" uu____5507))
end
| uu____5508 -> begin
()
end));
(

let uu____5509 = (next_prob probs)
in (match (uu____5509) with
| (Some (hd), tl, rank) -> begin
(

let probs = (

let uu___141_5522 = probs
in {attempting = tl; wl_deferred = uu___141_5522.wl_deferred; ctr = uu___141_5522.ctr; defer_ok = uu___141_5522.defer_ok; smt_ok = uu___141_5522.smt_ok; tcenv = uu___141_5522.tcenv})
in (match (hd) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match ((((not (probs.defer_ok)) && (flex_refine_inner <= rank)) && (rank <= flex_rigid))) with
| true -> begin
(

let uu____5529 = (solve_flex_rigid_join env tp probs)
in (match (uu____5529) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end))
end
| uu____5532 -> begin
(match ((((not (probs.defer_ok)) && (rigid_flex <= rank)) && (rank <= refine_flex))) with
| true -> begin
(

let uu____5533 = (solve_rigid_flex_meet env tp probs)
in (match (uu____5533) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end))
end
| uu____5536 -> begin
(solve_t' env (maybe_invert tp) probs)
end)
end)
end))
end
| (None, uu____5537, uu____5538) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| uu____5547 -> begin
(

let uu____5552 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____5580 -> (match (uu____5580) with
| (c, uu____5585, uu____5586) -> begin
(c < probs.ctr)
end))))
in (match (uu____5552) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(

let uu____5608 = (FStar_List.map (fun uu____5614 -> (match (uu____5614) with
| (uu____5620, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (uu____5608))
end
| uu____5623 -> begin
(

let uu____5628 = (

let uu___142_5629 = probs
in (

let uu____5630 = (FStar_All.pipe_right attempt (FStar_List.map (fun uu____5639 -> (match (uu____5639) with
| (uu____5643, uu____5644, y) -> begin
y
end))))
in {attempting = uu____5630; wl_deferred = rest; ctr = uu___142_5629.ctr; defer_ok = uu___142_5629.defer_ok; smt_ok = uu___142_5629.smt_ok; tcenv = uu___142_5629.tcenv}))
in (solve env uu____5628))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____5651 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____5651) with
| USolved (wl) -> begin
(

let uu____5653 = (solve_prob orig None [] wl)
in (solve env uu____5653))
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

let uu____5687 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____5687) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____5690 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t1 = (whnf env t1)
in (

let t2 = (whnf env t2)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = uu____5698; FStar_Syntax_Syntax.pos = uu____5699; FStar_Syntax_Syntax.vars = uu____5700}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = uu____5703; FStar_Syntax_Syntax.pos = uu____5704; FStar_Syntax_Syntax.vars = uu____5705}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____5721 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____5729 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____5729) with
| true -> begin
(

let uu____5730 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" uu____5730 msg))
end
| uu____5731 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____5732 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> ((

let uu____5738 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5738) with
| true -> begin
(

let uu____5739 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" uu____5739))
end
| uu____5740 -> begin
()
end));
(

let uu____5741 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____5741) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let uu____5783 = (head_matches_delta env () t1 t2)
in (match (uu____5783) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (uu____5805) -> begin
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

let uu____5831 = (match (ts) with
| Some (t1, t2) -> begin
(

let uu____5840 = (FStar_Syntax_Subst.compress t1)
in (

let uu____5841 = (FStar_Syntax_Subst.compress t2)
in ((uu____5840), (uu____5841))))
end
| None -> begin
(

let uu____5844 = (FStar_Syntax_Subst.compress t1)
in (

let uu____5845 = (FStar_Syntax_Subst.compress t2)
in ((uu____5844), (uu____5845))))
end)
in (match (uu____5831) with
| (t1, t2) -> begin
(

let eq_prob = (fun t1 t2 -> (

let uu____5867 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _0_41 -> FStar_TypeChecker_Common.TProb (_0_41)) uu____5867)))
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(

let uu____5890 = (

let uu____5896 = (

let uu____5899 = (

let uu____5902 = (

let uu____5903 = (

let uu____5908 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (uu____5908)))
in FStar_Syntax_Syntax.Tm_refine (uu____5903))
in (FStar_Syntax_Syntax.mk uu____5902))
in (uu____5899 None t1.FStar_Syntax_Syntax.pos))
in (

let uu____5921 = (

let uu____5923 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (uu____5923)::[])
in ((uu____5896), (uu____5921))))
in Some (uu____5890))
end
| (uu____5932, FStar_Syntax_Syntax.Tm_refine (x, uu____5934)) -> begin
(

let uu____5939 = (

let uu____5943 = (

let uu____5945 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (uu____5945)::[])
in ((t1), (uu____5943)))
in Some (uu____5939))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____5951), uu____5952) -> begin
(

let uu____5957 = (

let uu____5961 = (

let uu____5963 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (uu____5963)::[])
in ((t2), (uu____5961)))
in Some (uu____5957))
end
| uu____5968 -> begin
(

let uu____5971 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____5971) with
| (head1, uu____5986) -> begin
(

let uu____6001 = (

let uu____6002 = (FStar_Syntax_Util.un_uinst head1)
in uu____6002.FStar_Syntax_Syntax.n)
in (match (uu____6001) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____6009; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (i); FStar_Syntax_Syntax.fv_qual = uu____6011}) -> begin
(

let prev = (match ((i > (Prims.parse_int "1"))) with
| true -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i - (Prims.parse_int "1")))
end
| uu____6017 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t1)
in (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t2)
in (disjoin t1 t2))))
end
| uu____6020 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____6029) -> begin
(

let uu____6042 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___121_6051 -> (match (uu___121_6051) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(

let uu____6056 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____6056) with
| (u', uu____6067) -> begin
(

let uu____6082 = (

let uu____6083 = (whnf env u')
in uu____6083.FStar_Syntax_Syntax.n)
in (match (uu____6082) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____6087) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____6103 -> begin
false
end))
end))
end
| uu____6104 -> begin
false
end)
end
| uu____6106 -> begin
false
end))))
in (match (uu____6042) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun uu____6127 tps -> (match (uu____6127) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(

let uu____6154 = (

let uu____6159 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound uu____6159))
in (match (uu____6154) with
| Some (bound, sub) -> begin
(make_lower_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end))
end
| uu____6178 -> begin
None
end)
end))
in (

let uu____6183 = (

let uu____6188 = (

let uu____6192 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((uu____6192), ([])))
in (make_lower_bound uu____6188 lower_bounds))
in (match (uu____6183) with
| None -> begin
((

let uu____6199 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6199) with
| true -> begin
(FStar_Util.print_string "No lower bounds\n")
end
| uu____6200 -> begin
()
end));
None;
)
end
| Some (lhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in ((

let uu____6212 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6212) with
| true -> begin
(

let wl' = (

let uu___143_6214 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___143_6214.wl_deferred; ctr = uu___143_6214.ctr; defer_ok = uu___143_6214.defer_ok; smt_ok = uu___143_6214.smt_ok; tcenv = uu___143_6214.tcenv})
in (

let uu____6215 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" uu____6215)))
end
| uu____6216 -> begin
()
end));
(

let uu____6217 = (solve_t env eq_prob (

let uu___144_6218 = wl
in {attempting = sub_probs; wl_deferred = uu___144_6218.wl_deferred; ctr = uu___144_6218.ctr; defer_ok = uu___144_6218.defer_ok; smt_ok = uu___144_6218.smt_ok; tcenv = uu___144_6218.tcenv}))
in (match (uu____6217) with
| Success (uu____6220) -> begin
(

let wl = (

let uu___145_6222 = wl
in {attempting = rest; wl_deferred = uu___145_6222.wl_deferred; ctr = uu___145_6222.ctr; defer_ok = uu___145_6222.defer_ok; smt_ok = uu___145_6222.smt_ok; tcenv = uu___145_6222.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let uu____6224 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| uu____6227 -> begin
None
end));
))
end)))
end))
end
| uu____6228 -> begin
(failwith "Impossible: Not a rigid-flex")
end)))
end));
))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> ((

let uu____6235 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6235) with
| true -> begin
(

let uu____6236 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" uu____6236))
end
| uu____6237 -> begin
()
end));
(

let uu____6238 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____6238) with
| (u, args) -> begin
(

let uu____6265 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (uu____6265) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(

let max = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____6284 -> begin
i
end))
in (

let base_types_match = (fun t1 t2 -> (

let uu____6296 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____6296) with
| (h1, args1) -> begin
(

let uu____6324 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____6324) with
| (h2, uu____6337) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
(

let uu____6356 = (FStar_Syntax_Syntax.fv_eq tc1 tc2)
in (match (uu____6356) with
| true -> begin
(match (((FStar_List.length args1) = (Prims.parse_int "0"))) with
| true -> begin
Some ([])
end
| uu____6368 -> begin
(

let uu____6369 = (

let uu____6371 = (

let uu____6372 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_42 -> FStar_TypeChecker_Common.TProb (_0_42)) uu____6372))
in (uu____6371)::[])
in Some (uu____6369))
end)
end
| uu____6378 -> begin
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
| uu____6393 -> begin
(

let uu____6394 = (

let uu____6396 = (

let uu____6397 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_43 -> FStar_TypeChecker_Common.TProb (_0_43)) uu____6397))
in (uu____6396)::[])
in Some (uu____6394))
end)
end
| uu____6403 -> begin
None
end)
end
| uu____6405 -> begin
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

let uu____6471 = (

let uu____6477 = (

let uu____6480 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x uu____6480))
in ((uu____6477), (m)))
in Some (uu____6471))))))
end))
end
| (uu____6489, FStar_Syntax_Syntax.Tm_refine (y, uu____6491)) -> begin
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
| (FStar_Syntax_Syntax.Tm_refine (x, uu____6523), uu____6524) -> begin
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
| uu____6555 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____6589) -> begin
(

let uu____6602 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___122_6611 -> (match (uu___122_6611) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(

let uu____6616 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____6616) with
| (u', uu____6627) -> begin
(

let uu____6642 = (

let uu____6643 = (whnf env u')
in uu____6643.FStar_Syntax_Syntax.n)
in (match (uu____6642) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____6647) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____6663 -> begin
false
end))
end))
end
| uu____6664 -> begin
false
end)
end
| uu____6666 -> begin
false
end))))
in (match (uu____6602) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun uu____6691 tps -> (match (uu____6691) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(

let uu____6732 = (

let uu____6739 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound uu____6739))
in (match (uu____6732) with
| Some (bound, sub) -> begin
(make_upper_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end))
end
| uu____6774 -> begin
None
end)
end))
in (

let uu____6781 = (

let uu____6788 = (

let uu____6794 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((uu____6794), ([])))
in (make_upper_bound uu____6788 upper_bounds))
in (match (uu____6781) with
| None -> begin
((

let uu____6803 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6803) with
| true -> begin
(FStar_Util.print_string "No upper bounds\n")
end
| uu____6804 -> begin
()
end));
None;
)
end
| Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in ((

let uu____6822 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6822) with
| true -> begin
(

let wl' = (

let uu___146_6824 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___146_6824.wl_deferred; ctr = uu___146_6824.ctr; defer_ok = uu___146_6824.defer_ok; smt_ok = uu___146_6824.smt_ok; tcenv = uu___146_6824.tcenv})
in (

let uu____6825 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" uu____6825)))
end
| uu____6826 -> begin
()
end));
(

let uu____6827 = (solve_t env eq_prob (

let uu___147_6828 = wl
in {attempting = sub_probs; wl_deferred = uu___147_6828.wl_deferred; ctr = uu___147_6828.ctr; defer_ok = uu___147_6828.defer_ok; smt_ok = uu___147_6828.smt_ok; tcenv = uu___147_6828.tcenv}))
in (match (uu____6827) with
| Success (uu____6830) -> begin
(

let wl = (

let uu___148_6832 = wl
in {attempting = rest; wl_deferred = uu___148_6832.wl_deferred; ctr = uu___148_6832.ctr; defer_ok = uu___148_6832.defer_ok; smt_ok = uu___148_6832.smt_ok; tcenv = uu___148_6832.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let uu____6834 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| uu____6837 -> begin
None
end));
))
end)))
end))
end
| uu____6838 -> begin
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

let uu____6903 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6903) with
| true -> begin
(

let uu____6904 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" uu____6904))
end
| uu____6905 -> begin
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

let uu___149_6936 = hd1
in (

let uu____6937 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___149_6936.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___149_6936.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6937}))
in (

let hd2 = (

let uu___150_6941 = hd2
in (

let uu____6942 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___150_6941.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___150_6941.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6942}))
in (

let prob = (

let uu____6946 = (

let uu____6949 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort uu____6949 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _0_44 -> FStar_TypeChecker_Common.TProb (_0_44)) uu____6946))
in (

let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (

let subst = (

let uu____6957 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd1))))::uu____6957)
in (

let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (

let uu____6960 = (aux ((((hd1), (imp)))::scope) env subst xs ys)
in (match (uu____6960) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi = (

let uu____6978 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (

let uu____6981 = (FStar_Syntax_Util.close_forall ((((hd1), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj uu____6978 uu____6981)))
in ((

let uu____6987 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6987) with
| true -> begin
(

let uu____6988 = (FStar_Syntax_Print.term_to_string phi)
in (

let uu____6989 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" uu____6988 uu____6989)))
end
| uu____6990 -> begin
()
end));
FStar_Util.Inl ((((prob)::sub_probs), (phi)));
))
end
| fail -> begin
fail
end))))))))
end
| uu____7004 -> begin
FStar_Util.Inr ("arity or argument-qualifier mismatch")
end))
in (

let scope = (p_scope orig)
in (

let uu____7010 = (aux scope env [] bs1 bs2)
in (match (uu____7010) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end)))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let uu____7026 = (compress_tprob wl problem)
in (solve_t' env uu____7026 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (

let uu____7059 = (head_matches_delta env wl t1 t2)
in (match (uu____7059) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____7076), uu____7077) -> begin
(

let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____7099 -> begin
false
end))
in (match ((((may_relate head1) || (may_relate head2)) && wl.smt_ok)) with
| true -> begin
(

let guard = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end
| uu____7105 -> begin
(

let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(

let x = (FStar_Syntax_Syntax.new_bv None t1)
in (

let uu____7119 = (

let uu____7120 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 uu____7120 t2))
in (FStar_Syntax_Util.mk_forall x uu____7119)))
end))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB)) with
| true -> begin
(has_type_guard t1 t2)
end
| uu____7123 -> begin
(has_type_guard t2 t1)
end))
end)
in (

let uu____7124 = (solve_prob orig (Some (guard)) [] wl)
in (solve env uu____7124)))
end
| uu____7127 -> begin
(giveup env "head mismatch" orig)
end))
end
| (uu____7128, Some (t1, t2)) -> begin
(solve_t env (

let uu___151_7136 = problem
in {FStar_TypeChecker_Common.pid = uu___151_7136.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___151_7136.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___151_7136.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___151_7136.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___151_7136.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___151_7136.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___151_7136.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___151_7136.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____7137, None) -> begin
((

let uu____7144 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7144) with
| true -> begin
(

let uu____7145 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____7146 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____7147 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____7148 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" uu____7145 uu____7146 uu____7147 uu____7148)))))
end
| uu____7149 -> begin
()
end));
(

let uu____7150 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____7150) with
| (head1, args1) -> begin
(

let uu____7176 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____7176) with
| (head2, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((nargs <> (FStar_List.length args2))) with
| true -> begin
(

let uu____7216 = (

let uu____7217 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____7218 = (args_to_string args1)
in (

let uu____7219 = (FStar_Syntax_Print.term_to_string head2)
in (

let uu____7220 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____7217 uu____7218 uu____7219 uu____7220)))))
in (giveup env uu____7216 orig))
end
| uu____7221 -> begin
(

let uu____7222 = ((nargs = (Prims.parse_int "0")) || (

let uu____7225 = (FStar_Syntax_Util.eq_args args1 args2)
in (uu____7225 = FStar_Syntax_Util.Equal)))
in (match (uu____7222) with
| true -> begin
(

let uu____7226 = (solve_maybe_uinsts env orig head1 head2 wl)
in (match (uu____7226) with
| USolved (wl) -> begin
(

let uu____7228 = (solve_prob orig None [] wl)
in (solve env uu____7228))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end))
end
| uu____7231 -> begin
(

let uu____7232 = (base_and_refinement env wl t1)
in (match (uu____7232) with
| (base1, refinement1) -> begin
(

let uu____7258 = (base_and_refinement env wl t2)
in (match (uu____7258) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (None, None) -> begin
(

let uu____7312 = (solve_maybe_uinsts env orig head1 head2 wl)
in (match (uu____7312) with
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end
| USolved (wl) -> begin
(

let subprobs = (FStar_List.map2 (fun uu____7322 uu____7323 -> (match (((uu____7322), (uu____7323))) with
| ((a, uu____7333), (a', uu____7335)) -> begin
(

let uu____7340 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _0_45 -> FStar_TypeChecker_Common.TProb (_0_45)) uu____7340))
end)) args1 args2)
in (

let formula = (

let uu____7346 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____7346))
in (

let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end))
end
| uu____7350 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env (

let uu___152_7383 = problem
in {FStar_TypeChecker_Common.pid = uu___152_7383.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___152_7383.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___152_7383.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___152_7383.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___152_7383.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___152_7383.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___152_7383.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___152_7383.FStar_TypeChecker_Common.rank}) wl)))
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

let uu____7403 = p
in (match (uu____7403) with
| (((u, k), xs, c), ps, (h, uu____7414, qs)) -> begin
(

let xs = (sn_binders env xs)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____7463 = (imitation_sub_probs orig env xs ps qs)
in (match (uu____7463) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (

let uu____7477 = (h gs_xs)
in (

let uu____7478 = (

let uu____7485 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_46 -> FStar_Util.Inl (_0_46)))
in (FStar_All.pipe_right uu____7485 (fun _0_47 -> Some (_0_47))))
in (FStar_Syntax_Util.abs xs uu____7477 uu____7478)))
in ((

let uu____7516 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7516) with
| true -> begin
(

let uu____7517 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (

let uu____7518 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____7519 = (FStar_Syntax_Print.term_to_string im)
in (

let uu____7520 = (FStar_Syntax_Print.tag_of_term im)
in (

let uu____7521 = (

let uu____7522 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right uu____7522 (FStar_String.concat ", ")))
in (

let uu____7525 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" uu____7517 uu____7518 uu____7519 uu____7520 uu____7521 uu____7525)))))))
end
| uu____7526 -> begin
()
end));
(

let wl = (solve_prob orig (Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl)
in (solve env (attempt sub_probs wl)));
))
end))))
end)))
in (

let imitate' = (fun orig env wl uu___123_7543 -> (match (uu___123_7543) with
| None -> begin
(giveup env "unable to compute subterms" orig)
end
| Some (p) -> begin
(imitate orig env wl p)
end))
in (

let project = (fun orig env wl i p -> (

let uu____7572 = p
in (match (uu____7572) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____7630 = (FStar_List.nth ps i)
in (match (uu____7630) with
| (pi, uu____7633) -> begin
(

let uu____7638 = (FStar_List.nth xs i)
in (match (uu____7638) with
| (xi, uu____7645) -> begin
(

let rec gs = (fun k -> (

let uu____7654 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____7654) with
| (bs, k) -> begin
(

let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
(([]), ([]))
end
| ((a, uu____7706))::tl -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (

let uu____7714 = (new_uvar r xs k_a)
in (match (uu____7714) with
| (gi_xs, gi) -> begin
(

let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (

let gi_ps = ((FStar_Syntax_Syntax.mk_Tm_app gi ps) (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst = (FStar_Syntax_Syntax.NT (((a), (gi_xs))))::subst
in (

let uu____7733 = (aux subst tl)
in (match (uu____7733) with
| (gi_xs', gi_ps') -> begin
(

let uu____7748 = (

let uu____7750 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (uu____7750)::gi_xs')
in (

let uu____7751 = (

let uu____7753 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (uu____7753)::gi_ps')
in ((uu____7748), (uu____7751))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in (

let uu____7756 = (

let uu____7757 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation uu____7757))
in (match (uu____7756) with
| true -> begin
None
end
| uu____7759 -> begin
(

let uu____7760 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (uu____7760) with
| (g_xs, uu____7767) -> begin
(

let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (

let uu____7774 = ((FStar_Syntax_Syntax.mk_Tm_app xi g_xs) None r)
in (

let uu____7779 = (

let uu____7786 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_48 -> FStar_Util.Inl (_0_48)))
in (FStar_All.pipe_right uu____7786 (fun _0_49 -> Some (_0_49))))
in (FStar_Syntax_Util.abs xs uu____7774 uu____7779)))
in (

let sub = (

let uu____7817 = (

let uu____7820 = ((FStar_Syntax_Syntax.mk_Tm_app proj ps) None r)
in (

let uu____7827 = (

let uu____7830 = (FStar_List.map (fun uu____7836 -> (match (uu____7836) with
| (uu____7841, uu____7842, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h uu____7830))
in (mk_problem (p_scope orig) orig uu____7820 (p_rel orig) uu____7827 None "projection")))
in (FStar_All.pipe_left (fun _0_50 -> FStar_TypeChecker_Common.TProb (_0_50)) uu____7817))
in ((

let uu____7852 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7852) with
| true -> begin
(

let uu____7853 = (FStar_Syntax_Print.term_to_string proj)
in (

let uu____7854 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" uu____7853 uu____7854)))
end
| uu____7855 -> begin
()
end));
(

let wl = (

let uu____7857 = (

let uu____7859 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (uu____7859))
in (solve_prob orig uu____7857 ((TERM (((u), (proj))))::[]) wl))
in (

let uu____7864 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _0_51 -> Some (_0_51)) uu____7864)));
))))
end))
end)))
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl -> (

let uu____7888 = lhs
in (match (uu____7888) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let uu____7911 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (uu____7911) with
| (xs, c) -> begin
(match (((FStar_List.length xs) = (FStar_List.length ps))) with
| true -> begin
(

let uu____7933 = (

let uu____7959 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____7959)))
in Some (uu____7933))
end
| uu____8025 -> begin
(

let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (

let uu____8042 = (

let uu____8046 = (

let uu____8047 = (FStar_Syntax_Subst.compress k)
in uu____8047.FStar_Syntax_Syntax.n)
in ((uu____8046), (args)))
in (match (uu____8042) with
| (uu____8054, []) -> begin
(

let uu____8056 = (

let uu____8062 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____8062)))
in Some (uu____8056))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(

let uu____8079 = (FStar_Syntax_Util.head_and_args k)
in (match (uu____8079) with
| (uv, uv_args) -> begin
(

let uu____8108 = (

let uu____8109 = (FStar_Syntax_Subst.compress uv)
in uu____8109.FStar_Syntax_Syntax.n)
in (match (uu____8108) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____8116) -> begin
(

let uu____8129 = (pat_vars env [] uv_args)
in (match (uu____8129) with
| None -> begin
None
end
| Some (scope) -> begin
(

let xs = (FStar_All.pipe_right args (FStar_List.map (fun uu____8143 -> (

let uu____8144 = (

let uu____8145 = (

let uu____8146 = (

let uu____8149 = (

let uu____8150 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8150 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____8149))
in (Prims.fst uu____8146))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) uu____8145))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____8144)))))
in (

let c = (

let uu____8156 = (

let uu____8157 = (

let uu____8160 = (

let uu____8161 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8161 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____8160))
in (Prims.fst uu____8157))
in (FStar_Syntax_Syntax.mk_Total uu____8156))
in (

let k' = (FStar_Syntax_Util.arrow xs c)
in (

let uv_sol = (

let uu____8170 = (

let uu____8177 = (

let uu____8183 = (

let uu____8184 = (

let uu____8187 = (

let uu____8188 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8188 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total uu____8187))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8184))
in FStar_Util.Inl (uu____8183))
in Some (uu____8177))
in (FStar_Syntax_Util.abs scope k' uu____8170))
in ((FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)));
Some (((xs), (c)));
)))))
end))
end
| uu____8211 -> begin
None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), uu____8216) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs)
in (match ((n_xs = n_args)) with
| true -> begin
(

let uu____8242 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right uu____8242 (fun _0_52 -> Some (_0_52))))
end
| uu____8252 -> begin
(match ((n_xs < n_args)) with
| true -> begin
(

let uu____8261 = (FStar_Util.first_N n_xs args)
in (match (uu____8261) with
| (args, rest) -> begin
(

let uu____8277 = (FStar_Syntax_Subst.open_comp xs c)
in (match (uu____8277) with
| (xs, c) -> begin
(

let uu____8285 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt uu____8285 (fun uu____8296 -> (match (uu____8296) with
| (xs', c) -> begin
Some ((((FStar_List.append xs xs')), (c)))
end))))
end))
end))
end
| uu____8317 -> begin
(

let uu____8318 = (FStar_Util.first_N n_args xs)
in (match (uu____8318) with
| (xs, rest) -> begin
(

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c))))) None k.FStar_Syntax_Syntax.pos)
in (

let uu____8364 = (

let uu____8367 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs uu____8367))
in (FStar_All.pipe_right uu____8364 (fun _0_53 -> Some (_0_53)))))
end))
end)
end)))
end
| uu____8375 -> begin
(

let uu____8379 = (

let uu____8380 = (FStar_Syntax_Print.uvar_to_string uv)
in (

let uu____8384 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____8385 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" uu____8380 uu____8384 uu____8385))))
in (failwith uu____8379))
end)))
in (

let uu____8389 = (elim k_uv ps)
in (FStar_Util.bind_opt uu____8389 (fun uu____8417 -> (match (uu____8417) with
| (xs, c) -> begin
(

let uu____8445 = (

let uu____8468 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____8468)))
in Some (uu____8445))
end))))))
end)
end)))
in (

let rec imitate_or_project = (fun n stopt i -> (match (((i >= n) || (FStar_Option.isNone stopt))) with
| true -> begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end
| uu____8537 -> begin
(

let st = (FStar_Option.get stopt)
in (

let tx = (FStar_Unionfind.new_transaction ())
in (match ((i = (~- ((Prims.parse_int "1"))))) with
| true -> begin
(

let uu____8540 = (imitate orig env wl st)
in (match (uu____8540) with
| Failed (uu____8545) -> begin
((FStar_Unionfind.rollback tx);
(imitate_or_project n stopt (i + (Prims.parse_int "1")));
)
end
| sol -> begin
sol
end))
end
| uu____8550 -> begin
(

let uu____8551 = (project orig env wl i st)
in (match (uu____8551) with
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

let uu____8569 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____8569) with
| (hd, uu____8580) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| uu____8598 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd)
in (

let uu____8601 = (FStar_Util.set_is_subset_of fvs_hd fvs1)
in (match (uu____8601) with
| true -> begin
true
end
| uu____8602 -> begin
((

let uu____8604 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8604) with
| true -> begin
(

let uu____8605 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" uu____8605))
end
| uu____8606 -> begin
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

let uu____8613 = (

let uu____8616 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____8616 Prims.fst))
in (FStar_All.pipe_right uu____8613 FStar_Syntax_Free.names))
in (

let uu____8647 = (FStar_Util.set_is_empty fvs_hd)
in (match (uu____8647) with
| true -> begin
(~- ((Prims.parse_int "1")))
end
| uu____8648 -> begin
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

let uu____8656 = (occurs_check env wl ((uv), (k_uv)) t2)
in (match (uu____8656) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____8664 = (

let uu____8665 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____8665))
in (giveup_or_defer orig uu____8664))
end
| uu____8666 -> begin
(

let uu____8667 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____8667) with
| true -> begin
(

let uu____8668 = (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t2)) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))
in (match (uu____8668) with
| true -> begin
(

let uu____8669 = (subterms args_lhs)
in (imitate' orig env wl uu____8669))
end
| uu____8671 -> begin
((

let uu____8673 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8673) with
| true -> begin
(

let uu____8674 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____8675 = (names_to_string fvs1)
in (

let uu____8676 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" uu____8674 uu____8675 uu____8676))))
end
| uu____8677 -> begin
()
end));
(

let sol = (match (vars) with
| [] -> begin
t2
end
| uu____8681 -> begin
(

let uu____8682 = (sn_binders env vars)
in (u_abs k_uv uu____8682 t2))
end)
in (

let wl = (solve_prob orig None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl)
in (solve env wl)));
)
end))
end
| uu____8689 -> begin
(match ((((not (patterns_only)) && wl.defer_ok) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end
| uu____8690 -> begin
(

let uu____8691 = ((not (patterns_only)) && (check_head fvs1 t2))
in (match (uu____8691) with
| true -> begin
((

let uu____8693 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8693) with
| true -> begin
(

let uu____8694 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____8695 = (names_to_string fvs1)
in (

let uu____8696 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" uu____8694 uu____8695 uu____8696))))
end
| uu____8697 -> begin
()
end));
(

let uu____8698 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____8698 (~- ((Prims.parse_int "1")))));
)
end
| uu____8707 -> begin
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
| uu____8708 -> begin
(

let uu____8709 = (

let uu____8710 = (FStar_Syntax_Free.names t1)
in (check_head uu____8710 t2))
in (match (uu____8709) with
| true -> begin
(

let im_ok = (imitate_ok t2)
in ((

let uu____8714 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8714) with
| true -> begin
(

let uu____8715 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" uu____8715 (match ((im_ok < (Prims.parse_int "0"))) with
| true -> begin
"imitating"
end
| uu____8716 -> begin
"projecting"
end)))
end
| uu____8717 -> begin
()
end));
(

let uu____8718 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____8718 im_ok));
))
end
| uu____8727 -> begin
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
| uu____8738 -> begin
(

let force_quasi_pattern = (fun xs_opt uu____8760 -> (match (uu____8760) with
| (t, u, k, args) -> begin
(

let uu____8790 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____8790) with
| (all_formals, uu____8801) -> begin
(

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match (((formals), (args))) with
| ([], []) -> begin
(

let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun uu____8893 -> (match (uu____8893) with
| (x, imp) -> begin
(

let uu____8900 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____8900), (imp)))
end))))
in (

let pattern_vars = (FStar_List.rev pattern_vars)
in (

let kk = (

let uu____8908 = (FStar_Syntax_Util.type_u ())
in (match (uu____8908) with
| (t, uu____8912) -> begin
(

let uu____8913 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst uu____8913))
end))
in (

let uu____8916 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (uu____8916) with
| (t', tm_u1) -> begin
(

let uu____8923 = (destruct_flex_t t')
in (match (uu____8923) with
| (uu____8943, u1, k1, uu____8946) -> begin
(

let sol = (

let uu____8974 = (

let uu____8979 = (u_abs k all_formals t')
in ((((u), (k))), (uu____8979)))
in TERM (uu____8974))
in (

let t_app = ((FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args) None t.FStar_Syntax_Syntax.pos)
in ((sol), (((t_app), (u1), (k1), (pat_args))))))
end))
end)))))
end
| ((formal)::formals, (hd)::tl) -> begin
(

let uu____9039 = (pat_var_opt env pat_args hd)
in (match (uu____9039) with
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun uu____9068 -> (match (uu____9068) with
| (x, uu____9072) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in (match ((not (maybe_pat))) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| uu____9075 -> begin
(

let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____9078 = (

let uu____9079 = (FStar_Util.set_is_subset_of fvs pattern_var_set)
in (not (uu____9079)))
in (match (uu____9078) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| uu____9082 -> begin
(

let uu____9083 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) uu____9083 formals tl))
end)))
end))
end))
end
| uu____9089 -> begin
(failwith "Impossible")
end))
in (

let uu____9100 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] uu____9100 all_formals args)))
end))
end))
in (

let solve_both_pats = (fun wl uu____9148 uu____9149 r -> (match (((uu____9148), (uu____9149))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
(

let uu____9303 = ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys))
in (match (uu____9303) with
| true -> begin
(

let uu____9307 = (solve_prob orig None [] wl)
in (solve env uu____9307))
end
| uu____9308 -> begin
(

let xs = (sn_binders env xs)
in (

let ys = (sn_binders env ys)
in (

let zs = (intersect_vars xs ys)
in ((

let uu____9322 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9322) with
| true -> begin
(

let uu____9323 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (

let uu____9324 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (

let uu____9325 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (

let uu____9326 = (FStar_Syntax_Print.term_to_string k1)
in (

let uu____9327 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" uu____9323 uu____9324 uu____9325 uu____9326 uu____9327))))))
end
| uu____9328 -> begin
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

let uu____9369 = (FStar_Syntax_Util.subst_of_list xs args)
in (FStar_Syntax_Subst.subst uu____9369 k))
end
| uu____9371 -> begin
(match ((args_len < xs_len)) with
| true -> begin
(

let uu____9377 = (FStar_Util.first_N args_len xs)
in (match (uu____9377) with
| (xs, xs_rest) -> begin
(

let k = (

let uu____9407 = (FStar_Syntax_Syntax.mk_GTotal k)
in (FStar_Syntax_Util.arrow xs_rest uu____9407))
in (

let uu____9410 = (FStar_Syntax_Util.subst_of_list xs args)
in (FStar_Syntax_Subst.subst uu____9410 k)))
end))
end
| uu____9412 -> begin
(

let uu____9413 = (

let uu____9414 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____9415 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (

let uu____9416 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" uu____9414 uu____9415 uu____9416))))
in (failwith uu____9413))
end)
end))))
in (

let uu____9417 = (

let uu____9423 = (

let uu____9431 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals uu____9431))
in (match (uu____9423) with
| (bs, k1') -> begin
(

let uu____9449 = (

let uu____9457 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals uu____9457))
in (match (uu____9449) with
| (cs, k2') -> begin
(

let k1'_xs = (subst_k k1' bs args1)
in (

let k2'_ys = (subst_k k2' cs args2)
in (

let sub_prob = (

let uu____9478 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_54 -> FStar_TypeChecker_Common.TProb (_0_54)) uu____9478))
in (

let uu____9483 = (

let uu____9486 = (

let uu____9487 = (FStar_Syntax_Subst.compress k1')
in uu____9487.FStar_Syntax_Syntax.n)
in (

let uu____9490 = (

let uu____9491 = (FStar_Syntax_Subst.compress k2')
in uu____9491.FStar_Syntax_Syntax.n)
in ((uu____9486), (uu____9490))))
in (match (uu____9483) with
| (FStar_Syntax_Syntax.Tm_type (uu____9499), uu____9500) -> begin
((k1'), ((sub_prob)::[]))
end
| (uu____9504, FStar_Syntax_Syntax.Tm_type (uu____9505)) -> begin
((k2'), ((sub_prob)::[]))
end
| uu____9509 -> begin
(

let uu____9512 = (FStar_Syntax_Util.type_u ())
in (match (uu____9512) with
| (t, uu____9521) -> begin
(

let uu____9522 = (new_uvar r zs t)
in (match (uu____9522) with
| (k_zs, uu____9531) -> begin
(

let kprob = (

let uu____9533 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k_zs None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_55 -> FStar_TypeChecker_Common.TProb (_0_55)) uu____9533))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end)))))
end))
end))
in (match (uu____9417) with
| (k_u', sub_probs) -> begin
(

let uu____9547 = (

let uu____9555 = (

let uu____9556 = (new_uvar r zs k_u')
in (FStar_All.pipe_left Prims.fst uu____9556))
in (

let uu____9561 = (

let uu____9564 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs uu____9564))
in (

let uu____9567 = (

let uu____9570 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys uu____9570))
in ((uu____9555), (uu____9561), (uu____9567)))))
in (match (uu____9547) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs u_zs)
in (

let uu____9589 = (occurs_check env wl ((u1), (k1)) sub1)
in (match (uu____9589) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end
| uu____9601 -> begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in (

let uu____9613 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____9613) with
| true -> begin
(

let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end
| uu____9618 -> begin
(

let sub2 = (u_abs knew2 ys u_zs)
in (

let uu____9620 = (occurs_check env wl ((u2), (k2)) sub2)
in (match (uu____9620) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end
| uu____9632 -> begin
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

let solve_one_pat = (fun uu____9672 uu____9673 -> (match (((uu____9672), (uu____9673))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
((

let uu____9777 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9777) with
| true -> begin
(

let uu____9778 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____9779 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" uu____9778 uu____9779)))
end
| uu____9780 -> begin
()
end));
(

let uu____9781 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____9781) with
| true -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____9791 uu____9792 -> (match (((uu____9791), (uu____9792))) with
| ((a, uu____9802), (t2, uu____9804)) -> begin
(

let uu____9809 = (

let uu____9812 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig uu____9812 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right uu____9809 (fun _0_56 -> FStar_TypeChecker_Common.TProb (_0_56))))
end)) xs args2)
in (

let guard = (

let uu____9816 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____9816))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end
| uu____9822 -> begin
(

let t2 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t2)
in (

let uu____9826 = (occurs_check env wl ((u1), (k1)) t2)
in (match (uu____9826) with
| (occurs_ok, uu____9835) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in (

let uu____9840 = (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars))
in (match (uu____9840) with
| true -> begin
(

let sol = (

let uu____9842 = (

let uu____9847 = (u_abs k1 xs t2)
in ((((u1), (k1))), (uu____9847)))
in TERM (uu____9842))
in (

let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end
| uu____9859 -> begin
(

let uu____9860 = (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok))
in (match (uu____9860) with
| true -> begin
(

let uu____9861 = (force_quasi_pattern (Some (xs)) ((t2), (u2), (k2), (args2)))
in (match (uu____9861) with
| (sol, (uu____9875, u2, k2, ys)) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____9885 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____9885) with
| true -> begin
(

let uu____9886 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" uu____9886))
end
| uu____9887 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| uu____9891 -> begin
(giveup env "impossible" orig)
end);
))
end))
end
| uu____9892 -> begin
(giveup_or_defer orig "flex-flex constraint")
end))
end)))
end))))
end));
)
end))
in (

let uu____9893 = lhs
in (match (uu____9893) with
| (t1, u1, k1, args1) -> begin
(

let uu____9898 = rhs
in (match (uu____9898) with
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
| uu____9924 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end
| uu____9929 -> begin
(

let uu____9930 = (force_quasi_pattern None ((t1), (u1), (k1), (args1)))
in (match (uu____9930) with
| (sol, uu____9937) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____9940 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____9940) with
| true -> begin
(

let uu____9941 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" uu____9941))
end
| uu____9942 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| uu____9946 -> begin
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

let uu____9948 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____9948) with
| true -> begin
(

let uu____9949 = (solve_prob orig None [] wl)
in (solve env uu____9949))
end
| uu____9950 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in (

let uu____9953 = (FStar_Util.physical_equality t1 t2)
in (match (uu____9953) with
| true -> begin
(

let uu____9954 = (solve_prob orig None [] wl)
in (solve env uu____9954))
end
| uu____9955 -> begin
((

let uu____9957 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____9957) with
| true -> begin
(

let uu____9958 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" uu____9958))
end
| uu____9959 -> begin
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

let mk_c = (fun c uu___124_10004 -> (match (uu___124_10004) with
| [] -> begin
c
end
| bs -> begin
(

let uu____10018 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c))))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____10018))
end))
in (

let uu____10032 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____10032) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (

let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (

let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (

let rel = (

let uu____10118 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____10118) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____10119 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (

let uu____10120 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _0_57 -> FStar_TypeChecker_Common.CProb (_0_57)) uu____10120)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___125_10197 -> (match (uu___125_10197) with
| [] -> begin
t
end
| bs -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l))))) None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____10236 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____10236) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (

let uu____10319 = (

let uu____10322 = (FStar_Syntax_Subst.subst subst tbody1)
in (

let uu____10323 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig uu____10322 problem.FStar_TypeChecker_Common.relation uu____10323 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _0_58 -> FStar_TypeChecker_Common.TProb (_0_58)) uu____10319))))
end)))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____10338) -> begin
true
end
| uu____10353 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____10372 -> begin
(

let t = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____10378 -> begin
FStar_Util.Inr (t)
end))
end))
in (

let uu____10381 = (

let uu____10392 = (maybe_eta t1)
in (

let uu____10397 = (maybe_eta t2)
in ((uu____10392), (uu____10397))))
in (match (uu____10381) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(solve_t env (

let uu___153_10428 = problem
in {FStar_TypeChecker_Common.pid = uu___153_10428.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___153_10428.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___153_10428.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___153_10428.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___153_10428.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___153_10428.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___153_10428.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___153_10428.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs))) | ((FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs))) -> begin
(

let uu____10461 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____10461) with
| true -> begin
(

let uu____10462 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____10462 t_abs wl))
end
| uu____10466 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| uu____10467 -> begin
(failwith "Impossible: at least one side is an abstraction")
end))))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____10478), FStar_Syntax_Syntax.Tm_refine (uu____10479)) -> begin
(

let uu____10488 = (as_refinement env wl t1)
in (match (uu____10488) with
| (x1, phi1) -> begin
(

let uu____10493 = (as_refinement env wl t2)
in (match (uu____10493) with
| (x2, phi2) -> begin
(

let base_prob = (

let uu____10499 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _0_59 -> FStar_TypeChecker_Common.TProb (_0_59)) uu____10499))
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

let uu____10532 = (imp phi1 phi2)
in (FStar_All.pipe_right uu____10532 (guard_on_element problem x1))))
in (

let fallback = (fun uu____10536 -> (

let impl = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end
| uu____10538 -> begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end)
in (

let guard = (

let uu____10542 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____10542 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl))))))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let ref_prob = (

let uu____10549 = (

let uu____10552 = (

let uu____10553 = (FStar_Syntax_Syntax.mk_binder x1)
in (uu____10553)::(p_scope orig))
in (mk_problem uu____10552 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _0_60 -> FStar_TypeChecker_Common.TProb (_0_60)) uu____10549))
in (

let uu____10556 = (solve env (

let uu___154_10557 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___154_10557.ctr; defer_ok = false; smt_ok = uu___154_10557.smt_ok; tcenv = uu___154_10557.tcenv}))
in (match (uu____10556) with
| Failed (uu____10561) -> begin
(fallback ())
end
| Success (uu____10564) -> begin
(

let guard = (

let uu____10568 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (

let uu____10571 = (

let uu____10572 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right uu____10572 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj uu____10568 uu____10571)))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (

let wl = (

let uu___155_10579 = wl
in {attempting = uu___155_10579.attempting; wl_deferred = uu___155_10579.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___155_10579.defer_ok; smt_ok = uu___155_10579.smt_ok; tcenv = uu___155_10579.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end)))
end
| uu____10580 -> begin
(fallback ())
end)))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(

let uu____10633 = (destruct_flex_t t1)
in (

let uu____10634 = (destruct_flex_t t2)
in (flex_flex orig uu____10633 uu____10634)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(

let uu____10650 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____10650 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_arrow (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
(solve_t' env (

let uu___156_10699 = problem
in {FStar_TypeChecker_Common.pid = uu___156_10699.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___156_10699.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___156_10699.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___156_10699.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___156_10699.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___156_10699.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___156_10699.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___156_10699.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___156_10699.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____10715 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____10717 = (

let uu____10718 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____10718))
in (match (uu____10717) with
| true -> begin
(

let uu____10719 = (FStar_All.pipe_left (fun _0_61 -> FStar_TypeChecker_Common.TProb (_0_61)) (

let uu___157_10722 = problem
in {FStar_TypeChecker_Common.pid = uu___157_10722.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___157_10722.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___157_10722.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___157_10722.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___157_10722.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___157_10722.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___157_10722.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___157_10722.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___157_10722.FStar_TypeChecker_Common.rank}))
in (

let uu____10723 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____10719 uu____10723 t2 wl)))
end
| uu____10727 -> begin
(

let uu____10728 = (base_and_refinement env wl t2)
in (match (uu____10728) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(

let uu____10758 = (FStar_All.pipe_left (fun _0_62 -> FStar_TypeChecker_Common.TProb (_0_62)) (

let uu___158_10761 = problem
in {FStar_TypeChecker_Common.pid = uu___158_10761.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___158_10761.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___158_10761.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___158_10761.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___158_10761.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___158_10761.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___158_10761.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___158_10761.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___158_10761.FStar_TypeChecker_Common.rank}))
in (

let uu____10762 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____10758 uu____10762 t_base wl)))
end
| Some (y, phi) -> begin
(

let y' = (

let uu___159_10777 = y
in {FStar_Syntax_Syntax.ppname = uu___159_10777.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___159_10777.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element problem y' phi)
in (

let base_prob = (

let uu____10780 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_63 -> FStar_TypeChecker_Common.TProb (_0_63)) uu____10780))
in (

let guard = (

let uu____10788 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____10788 impl))
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
| uu____10809 -> begin
(

let uu____10810 = (base_and_refinement env wl t1)
in (match (uu____10810) with
| (t_base, uu____10821) -> begin
(solve_t env (

let uu___160_10836 = problem
in {FStar_TypeChecker_Common.pid = uu___160_10836.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___160_10836.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___160_10836.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___160_10836.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___160_10836.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___160_10836.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___160_10836.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___160_10836.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (FStar_Syntax_Syntax.Tm_refine (uu____10839), uu____10840) -> begin
(

let t2 = (

let uu____10848 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement uu____10848))
in (solve_t env (

let uu___161_10861 = problem
in {FStar_TypeChecker_Common.pid = uu___161_10861.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___161_10861.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___161_10861.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___161_10861.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___161_10861.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___161_10861.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___161_10861.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___161_10861.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___161_10861.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____10862, FStar_Syntax_Syntax.Tm_refine (uu____10863)) -> begin
(

let t1 = (

let uu____10871 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement uu____10871))
in (solve_t env (

let uu___162_10884 = problem
in {FStar_TypeChecker_Common.pid = uu___162_10884.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___162_10884.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___162_10884.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___162_10884.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_10884.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_10884.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_10884.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_10884.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_10884.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(

let head1 = (

let uu____10914 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____10914 Prims.fst))
in (

let head2 = (

let uu____10945 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____10945 Prims.fst))
in (

let uu____10973 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____10973) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____10982 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____10982) with
| true -> begin
(

let guard = (

let uu____10991 = (

let uu____10992 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____10992 = FStar_Syntax_Util.Equal))
in (match (uu____10991) with
| true -> begin
None
end
| uu____10998 -> begin
(

let uu____10999 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _0_64 -> Some (_0_64)) uu____10999))
end))
in (

let uu____11009 = (solve_prob orig guard [] wl)
in (solve env uu____11009)))
end
| uu____11010 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____11011 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, uu____11013, uu____11014), uu____11015) -> begin
(solve_t' env (

let uu___163_11034 = problem
in {FStar_TypeChecker_Common.pid = uu___163_11034.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___163_11034.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___163_11034.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___163_11034.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___163_11034.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___163_11034.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___163_11034.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___163_11034.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___163_11034.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____11037, FStar_Syntax_Syntax.Tm_ascribed (t2, uu____11039, uu____11040)) -> begin
(solve_t' env (

let uu___164_11059 = problem
in {FStar_TypeChecker_Common.pid = uu___164_11059.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___164_11059.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___164_11059.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___164_11059.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_11059.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_11059.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_11059.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_11059.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_11059.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(

let uu____11072 = (

let uu____11073 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____11074 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____11073 uu____11074)))
in (failwith uu____11072))
end
| uu____11075 -> begin
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

let uu____11107 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____11107) with
| true -> begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end
| uu____11108 -> begin
()
end));
(

let sub_probs = (FStar_List.map2 (fun uu____11115 uu____11116 -> (match (((uu____11115), (uu____11116))) with
| ((a1, uu____11126), (a2, uu____11128)) -> begin
(

let uu____11133 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _0_65 -> FStar_TypeChecker_Common.TProb (_0_65)) uu____11133))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (

let uu____11139 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____11139))
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
| ((wp1, uu____11162))::[] -> begin
wp1
end
| uu____11175 -> begin
(

let uu____11181 = (

let uu____11182 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" uu____11182))
in (failwith uu____11181))
end)
in (

let c1 = (

let uu____11186 = (

let uu____11192 = (

let uu____11193 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____11193))
in (uu____11192)::[])
in {FStar_Syntax_Syntax.comp_univs = c1.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____11186; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2)))
end
| uu____11194 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___126_11197 -> (match (uu___126_11197) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| uu____11198 -> begin
false
end))))
in (

let uu____11199 = (match (((c1.FStar_Syntax_Syntax.effect_args), (c2.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____11223))::uu____11224, ((wp2, uu____11226))::uu____11227) -> begin
((wp1), (wp2))
end
| uu____11268 -> begin
(

let uu____11281 = (

let uu____11282 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____11283 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____11282 uu____11283)))
in (failwith uu____11281))
end)
in (match (uu____11199) with
| (wpc1, wpc2) -> begin
(

let uu____11300 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____11300) with
| true -> begin
(

let uu____11303 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env uu____11303 wl))
end
| uu____11306 -> begin
(

let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____11309 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____11311 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11311) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____11312 -> begin
()
end));
(

let uu____11313 = (

let uu____11316 = (

let uu____11317 = (

let uu____11327 = (

let uu____11328 = (

let uu____11329 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (uu____11329)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____11328 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (

let uu____11330 = (

let uu____11332 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____11333 = (

let uu____11335 = (

let uu____11336 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11336))
in (uu____11335)::[])
in (uu____11332)::uu____11333))
in ((uu____11327), (uu____11330))))
in FStar_Syntax_Syntax.Tm_app (uu____11317))
in (FStar_Syntax_Syntax.mk uu____11316))
in (uu____11313 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r));
)
end
| uu____11346 -> begin
(

let uu____11347 = (

let uu____11350 = (

let uu____11351 = (

let uu____11361 = (

let uu____11362 = (

let uu____11363 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (uu____11363)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____11362 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (

let uu____11364 = (

let uu____11366 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (

let uu____11367 = (

let uu____11369 = (FStar_Syntax_Syntax.as_arg wpc2)
in (

let uu____11370 = (

let uu____11372 = (

let uu____11373 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11373))
in (uu____11372)::[])
in (uu____11369)::uu____11370))
in (uu____11366)::uu____11367))
in ((uu____11361), (uu____11364))))
in FStar_Syntax_Syntax.Tm_app (uu____11351))
in (FStar_Syntax_Syntax.mk uu____11350))
in (uu____11347 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r))
end)
end)
in (

let base_prob = (

let uu____11384 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _0_66 -> FStar_TypeChecker_Common.TProb (_0_66)) uu____11384))
in (

let wl = (

let uu____11390 = (

let uu____11392 = (

let uu____11395 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____11395 g))
in (FStar_All.pipe_left (fun _0_67 -> Some (_0_67)) uu____11392))
in (solve_prob orig uu____11390 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end))
end)))
end)))
in (

let uu____11405 = (FStar_Util.physical_equality c1 c2)
in (match (uu____11405) with
| true -> begin
(

let uu____11406 = (solve_prob orig None [] wl)
in (solve env uu____11406))
end
| uu____11407 -> begin
((

let uu____11409 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11409) with
| true -> begin
(

let uu____11410 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____11411 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____11410 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____11411)))
end
| uu____11412 -> begin
()
end));
(

let uu____11413 = (

let uu____11416 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____11417 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____11416), (uu____11417))))
in (match (uu____11413) with
| (c1, c2) -> begin
(match (((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____11421), FStar_Syntax_Syntax.Total (t2, uu____11423)) when (FStar_Syntax_Util.non_informative t2) -> begin
(

let uu____11436 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env uu____11436 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____11439), FStar_Syntax_Syntax.Total (uu____11440)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.Total (t2, _))) | ((FStar_Syntax_Syntax.GTotal (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) | ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) -> begin
(

let uu____11489 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env uu____11489 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(

let uu____11496 = (

let uu___165_11499 = problem
in (

let uu____11502 = (

let uu____11503 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____11503))
in {FStar_TypeChecker_Common.pid = uu___165_11499.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____11502; FStar_TypeChecker_Common.relation = uu___165_11499.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___165_11499.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___165_11499.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___165_11499.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___165_11499.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___165_11499.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___165_11499.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___165_11499.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____11496 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(

let uu____11508 = (

let uu___166_11511 = problem
in (

let uu____11514 = (

let uu____11515 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c2)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____11515))
in {FStar_TypeChecker_Common.pid = uu___166_11511.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___166_11511.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___166_11511.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____11514; FStar_TypeChecker_Common.element = uu___166_11511.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_11511.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___166_11511.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___166_11511.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_11511.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_11511.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____11508 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____11516), FStar_Syntax_Syntax.Comp (uu____11517)) -> begin
(

let uu____11518 = (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2))))
in (match (uu____11518) with
| true -> begin
(

let uu____11519 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env uu____11519 wl))
end
| uu____11522 -> begin
(

let c1_comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c1)
in (

let c2_comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c2)
in (match (((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name))) with
| true -> begin
(solve_eq c1_comp c2_comp)
end
| uu____11525 -> begin
(

let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (

let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in ((

let uu____11529 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11529) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____11530 -> begin
()
end));
(

let uu____11531 = (FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (uu____11531) with
| None -> begin
(

let uu____11533 = (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (

let uu____11534 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative uu____11534)))
in (match (uu____11533) with
| true -> begin
(

let edge = {FStar_TypeChecker_Env.msource = c1.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c2.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = (fun r t -> t)}
in (solve_sub c1 edge c2))
end
| uu____11538 -> begin
(

let uu____11539 = (

let uu____11540 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____11541 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____11540 uu____11541)))
in (giveup env uu____11539 orig))
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

let uu____11546 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____11566 -> (match (uu____11566) with
| (uu____11577, uu____11578, u, uu____11580, uu____11581, uu____11582) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____11546 (FStar_String.concat ", "))))


let ineqs_to_string : (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.string = (fun ineqs -> (

let vars = (

let uu____11611 = (FStar_All.pipe_right (Prims.fst ineqs) (FStar_List.map FStar_Syntax_Print.univ_to_string))
in (FStar_All.pipe_right uu____11611 (FStar_String.concat ", ")))
in (

let ineqs = (

let uu____11621 = (FStar_All.pipe_right (Prims.snd ineqs) (FStar_List.map (fun uu____11633 -> (match (uu____11633) with
| (u1, u2) -> begin
(

let uu____11638 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____11639 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "%s < %s" uu____11638 uu____11639)))
end))))
in (FStar_All.pipe_right uu____11621 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred), (g.FStar_TypeChecker_Env.univ_ineqs))) with
| (FStar_TypeChecker_Common.Trivial, [], (uu____11651, [])) -> begin
"{}"
end
| uu____11664 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____11674 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____11674) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____11675 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____11677 = (FStar_List.map (fun uu____11681 -> (match (uu____11681) with
| (uu____11684, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right uu____11677 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (

let uu____11688 = (ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs)
in (FStar_Util.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n" form carry uu____11688 imps)))))
end))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu____11708; FStar_TypeChecker_Env.implicits = uu____11709} -> begin
true
end
| uu____11723 -> begin
false
end))


let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []}


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
| uu____11750 -> begin
(failwith "impossible")
end)
in (

let uu____11751 = (

let uu___167_11752 = g
in (

let uu____11753 = (

let uu____11754 = (

let uu____11755 = (

let uu____11759 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____11759)::[])
in (

let uu____11760 = (

let uu____11767 = (

let uu____11773 = (

let uu____11774 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____11774 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____11773 (fun _0_68 -> FStar_Util.Inl (_0_68))))
in Some (uu____11767))
in (FStar_Syntax_Util.abs uu____11755 f uu____11760)))
in (FStar_All.pipe_left (fun _0_69 -> FStar_TypeChecker_Common.NonTrivial (_0_69)) uu____11754))
in {FStar_TypeChecker_Env.guard_f = uu____11753; FStar_TypeChecker_Env.deferred = uu___167_11752.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___167_11752.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___167_11752.FStar_TypeChecker_Env.implicits}))
in Some (uu____11751)))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___168_11795 = g
in (

let uu____11796 = (

let uu____11797 = (

let uu____11798 = (

let uu____11801 = (

let uu____11802 = (

let uu____11812 = (

let uu____11814 = (FStar_Syntax_Syntax.as_arg e)
in (uu____11814)::[])
in ((f), (uu____11812)))
in FStar_Syntax_Syntax.Tm_app (uu____11802))
in (FStar_Syntax_Syntax.mk uu____11801))
in (uu____11798 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _0_70 -> FStar_TypeChecker_Common.NonTrivial (_0_70)) uu____11797))
in {FStar_TypeChecker_Env.guard_f = uu____11796; FStar_TypeChecker_Env.deferred = uu___168_11795.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___168_11795.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___168_11795.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____11827) -> begin
(failwith "impossible")
end))


let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let uu____11837 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (uu____11837))
end))


let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____11846 -> begin
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

let uu____11877 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = uu____11877; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (((FStar_List.append (Prims.fst g1.FStar_TypeChecker_Env.univ_ineqs) (Prims.fst g2.FStar_TypeChecker_Env.univ_ineqs))), ((FStar_List.append (Prims.snd g1.FStar_TypeChecker_Env.univ_ineqs) (Prims.snd g2.FStar_TypeChecker_Env.univ_ineqs)))); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___169_11915 = g
in (

let uu____11916 = (

let uu____11917 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right uu____11917 (fun _0_71 -> FStar_TypeChecker_Common.NonTrivial (_0_71))))
in {FStar_TypeChecker_Env.guard_f = uu____11916; FStar_TypeChecker_Env.deferred = uu___169_11915.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___169_11915.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___169_11915.FStar_TypeChecker_Env.implicits}))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = (

let uu____11955 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____11955) with
| true -> begin
(

let uu____11956 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____11957 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____11956 (rel_to_string rel) uu____11957)))
end
| uu____11958 -> begin
"TOP"
end))
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (

let uu____11977 = (

let uu____11979 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_72 -> Some (_0_72)) uu____11979))
in (FStar_Syntax_Syntax.new_bv uu____11977 t1))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (

let uu____11985 = (

let uu____11987 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _0_73 -> Some (_0_73)) uu____11987))
in (

let uu____11989 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 uu____11985 uu____11989)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (

let probs = (

let uu____12012 = (FStar_Options.eager_inference ())
in (match (uu____12012) with
| true -> begin
(

let uu___170_12013 = probs
in {attempting = uu___170_12013.attempting; wl_deferred = uu___170_12013.wl_deferred; ctr = uu___170_12013.ctr; defer_ok = false; smt_ok = uu___170_12013.smt_ok; tcenv = uu___170_12013.tcenv})
end
| uu____12014 -> begin
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

let uu____12024 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____12024) with
| true -> begin
(

let uu____12025 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____12025))
end
| uu____12026 -> begin
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

let uu____12035 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____12035) with
| true -> begin
(

let uu____12036 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____12036))
end
| uu____12037 -> begin
()
end));
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in ((

let uu____12040 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____12040) with
| true -> begin
(

let uu____12041 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____12041))
end
| uu____12042 -> begin
()
end));
(

let f = (

let uu____12044 = (

let uu____12045 = (FStar_Syntax_Util.unmeta f)
in uu____12045.FStar_Syntax_Syntax.n)
in (match (uu____12044) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____12049 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end))
in (

let uu___171_12050 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = uu___171_12050.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___171_12050.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___171_12050.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(

let uu____12065 = (

let uu____12066 = (

let uu____12067 = (

let uu____12068 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right uu____12068 (fun _0_74 -> FStar_TypeChecker_Common.NonTrivial (_0_74))))
in {FStar_TypeChecker_Env.guard_f = uu____12067; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env uu____12066))
in (FStar_All.pipe_left (fun _0_75 -> Some (_0_75)) uu____12065))
end))


let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> ((

let uu____12092 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12092) with
| true -> begin
(

let uu____12093 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12094 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" uu____12093 uu____12094)))
end
| uu____12095 -> begin
()
end));
(

let prob = (

let uu____12097 = (

let uu____12100 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None uu____12100))
in (FStar_All.pipe_left (fun _0_76 -> FStar_TypeChecker_Common.TProb (_0_76)) uu____12097))
in (

let g = (

let uu____12105 = (

let uu____12107 = (singleton env prob)
in (solve_and_commit env uu____12107 (fun uu____12108 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12105))
in g));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____12122 = (try_teq env t1 t2)
in (match (uu____12122) with
| None -> begin
(

let uu____12124 = (

let uu____12125 = (

let uu____12128 = (FStar_TypeChecker_Err.basic_type_error env None t2 t1)
in (

let uu____12129 = (FStar_TypeChecker_Env.get_range env)
in ((uu____12128), (uu____12129))))
in FStar_Errors.Error (uu____12125))
in (Prims.raise uu____12124))
end
| Some (g) -> begin
((

let uu____12132 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12132) with
| true -> begin
(

let uu____12133 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12134 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____12135 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____12133 uu____12134 uu____12135))))
end
| uu____12136 -> begin
()
end));
g;
)
end)))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 smt_ok -> ((

let uu____12151 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12151) with
| true -> begin
(

let uu____12152 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____12153 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" uu____12152 uu____12153)))
end
| uu____12154 -> begin
()
end));
(

let uu____12155 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____12155) with
| (prob, x) -> begin
(

let g = (

let uu____12163 = (

let uu____12165 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____12165 (fun uu____12166 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12163))
in ((

let uu____12172 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____12172) with
| true -> begin
(

let uu____12173 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____12174 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____12175 = (

let uu____12176 = (FStar_Util.must g)
in (guard_to_string env uu____12176))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" uu____12173 uu____12174 uu____12175))))
end
| uu____12177 -> begin
()
end));
(abstract_guard x g);
))
end));
))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env e t1 t2 -> (

let uu____12200 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12201 = (FStar_TypeChecker_Err.basic_type_error env (Some (e)) t2 t1)
in (FStar_Errors.report uu____12200 uu____12201))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> ((

let uu____12213 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12213) with
| true -> begin
(

let uu____12214 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____12215 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" uu____12214 uu____12215)))
end
| uu____12216 -> begin
()
end));
(

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____12218 -> begin
FStar_TypeChecker_Common.SUB
end)
in (

let prob = (

let uu____12220 = (

let uu____12223 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None uu____12223 "sub_comp"))
in (FStar_All.pipe_left (fun _0_77 -> FStar_TypeChecker_Common.CProb (_0_77)) uu____12220))
in (

let uu____12226 = (

let uu____12228 = (singleton env prob)
in (solve_and_commit env uu____12228 (fun uu____12229 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12226))));
))


let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun tx env uu____12248 -> (match (uu____12248) with
| (variables, ineqs) -> begin
(

let fail = (fun u1 u2 -> ((FStar_Unionfind.rollback tx);
(

let uu____12273 = (

let uu____12274 = (

let uu____12277 = (

let uu____12278 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____12279 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Universe %s and %s are incompatible" uu____12278 uu____12279)))
in (

let uu____12280 = (FStar_TypeChecker_Env.get_range env)
in ((uu____12277), (uu____12280))))
in FStar_Errors.Error (uu____12274))
in (Prims.raise uu____12273));
))
in (

let equiv = (fun v v' -> (

let uu____12288 = (

let uu____12291 = (FStar_Syntax_Subst.compress_univ v)
in (

let uu____12292 = (FStar_Syntax_Subst.compress_univ v')
in ((uu____12291), (uu____12292))))
in (match (uu____12288) with
| (FStar_Syntax_Syntax.U_unif (v0), FStar_Syntax_Syntax.U_unif (v0')) -> begin
(FStar_Unionfind.equivalent v0 v0')
end
| uu____12300 -> begin
false
end)))
in (

let sols = (FStar_All.pipe_right variables (FStar_List.collect (fun v -> (

let uu____12314 = (FStar_Syntax_Subst.compress_univ v)
in (match (uu____12314) with
| FStar_Syntax_Syntax.U_unif (uu____12318) -> begin
(

let lower_bounds_of_v = (FStar_All.pipe_right ineqs (FStar_List.collect (fun uu____12329 -> (match (uu____12329) with
| (u, v') -> begin
(

let uu____12335 = (equiv v v')
in (match (uu____12335) with
| true -> begin
(

let uu____12337 = (FStar_All.pipe_right variables (FStar_Util.for_some (equiv u)))
in (match (uu____12337) with
| true -> begin
[]
end
| uu____12340 -> begin
(u)::[]
end))
end
| uu____12341 -> begin
[]
end))
end))))
in (

let lb = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max (lower_bounds_of_v)))
in (((lb), (v)))::[]))
end
| uu____12347 -> begin
[]
end)))))
in (

let uu____12350 = (

let wl = (

let uu___172_12353 = (empty_worklist env)
in {attempting = uu___172_12353.attempting; wl_deferred = uu___172_12353.wl_deferred; ctr = uu___172_12353.ctr; defer_ok = false; smt_ok = uu___172_12353.smt_ok; tcenv = uu___172_12353.tcenv})
in (FStar_All.pipe_right sols (FStar_List.map (fun uu____12360 -> (match (uu____12360) with
| (lb, v) -> begin
(

let uu____12365 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl lb v)
in (match (uu____12365) with
| USolved (wl) -> begin
()
end
| uu____12367 -> begin
(fail lb v)
end))
end)))))
in (

let rec check_ineq = (fun uu____12373 -> (match (uu____12373) with
| (u, v) -> begin
(

let u = (FStar_TypeChecker_Normalize.normalize_universe env u)
in (

let v = (FStar_TypeChecker_Normalize.normalize_universe env v)
in (match (((u), (v))) with
| (FStar_Syntax_Syntax.U_zero, uu____12380) -> begin
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
(check_ineq ((u), (v0)))
end
| (FStar_Syntax_Syntax.U_max (us), uu____12396) -> begin
(FStar_All.pipe_right us (FStar_Util.for_all (fun u -> (check_ineq ((u), (v))))))
end
| (uu____12400, FStar_Syntax_Syntax.U_max (vs)) -> begin
(FStar_All.pipe_right vs (FStar_Util.for_some (fun v -> (check_ineq ((u), (v))))))
end
| uu____12405 -> begin
false
end)))
end))
in (

let uu____12408 = (FStar_All.pipe_right ineqs (FStar_Util.for_all (fun uu____12414 -> (match (uu____12414) with
| (u, v) -> begin
(

let uu____12419 = (check_ineq ((u), (v)))
in (match (uu____12419) with
| true -> begin
true
end
| uu____12420 -> begin
((

let uu____12422 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____12422) with
| true -> begin
(

let uu____12423 = (FStar_Syntax_Print.univ_to_string u)
in (

let uu____12424 = (FStar_Syntax_Print.univ_to_string v)
in (FStar_Util.print2 "%s </= %s" uu____12423 uu____12424)))
end
| uu____12425 -> begin
()
end));
false;
)
end))
end))))
in (match (uu____12408) with
| true -> begin
()
end
| uu____12426 -> begin
((

let uu____12428 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____12428) with
| true -> begin
((

let uu____12430 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Partially solved inequality constraints are: %s\n" uu____12430));
(FStar_Unionfind.rollback tx);
(

let uu____12436 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Original solved inequality constraints are: %s\n" uu____12436));
)
end
| uu____12441 -> begin
()
end));
(

let uu____12442 = (

let uu____12443 = (

let uu____12446 = (FStar_TypeChecker_Env.get_range env)
in (("Failed to solve universe inequalities for inductives"), (uu____12446)))
in FStar_Errors.Error (uu____12443))
in (Prims.raise uu____12442));
)
end)))))))
end))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun env ineqs -> (

let tx = (FStar_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Unionfind.commit tx);
)))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail = (fun uu____12479 -> (match (uu____12479) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Errors.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in ((

let uu____12489 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____12489) with
| true -> begin
(

let uu____12490 = (wl_to_string wl)
in (

let uu____12491 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" uu____12490 uu____12491)))
end
| uu____12501 -> begin
()
end));
(

let g = (

let uu____12503 = (solve_and_commit env wl fail)
in (match (uu____12503) with
| Some ([]) -> begin
(

let uu___173_12510 = g
in {FStar_TypeChecker_Env.guard_f = uu___173_12510.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu___173_12510.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___173_12510.FStar_TypeChecker_Env.implicits})
end
| uu____12513 -> begin
(failwith "impossible: Unexpected deferred constraints remain")
end))
in ((solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___174_12516 = g
in {FStar_TypeChecker_Env.guard_f = uu___174_12516.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___174_12516.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = uu___174_12516.FStar_TypeChecker_Env.implicits});
));
))))


let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun use_env_range_msg env g use_smt -> (

let g = (solve_deferred_constraints env g)
in (

let ret_g = (

let uu___175_12542 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___175_12542.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___175_12542.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___175_12542.FStar_TypeChecker_Env.implicits})
in (

let uu____12543 = (

let uu____12544 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12544)))
in (match (uu____12543) with
| true -> begin
Some (ret_g)
end
| uu____12546 -> begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((

let uu____12550 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Norm")))
in (match (uu____12550) with
| true -> begin
(

let uu____12551 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12552 = (

let uu____12553 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____12553))
in (FStar_Errors.diag uu____12551 uu____12552)))
end
| uu____12554 -> begin
()
end));
(

let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(match ((not (use_smt))) with
| true -> begin
None
end
| uu____12559 -> begin
((

let uu____12562 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12562) with
| true -> begin
(

let uu____12563 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12564 = (

let uu____12565 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____12565))
in (FStar_Errors.diag uu____12563 uu____12564)))
end
| uu____12566 -> begin
()
end));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc);
Some (ret_g);
)
end)
end));
)
end)
end)))))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let uu____12573 = (discharge_guard' None env g true)
in (match (uu____12573) with
| Some (g) -> begin
g
end
| None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end)))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (

let uu____12593 = (FStar_Unionfind.find u)
in (match (uu____12593) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| uu____12602 -> begin
false
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____12617 = acc
in (match (uu____12617) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____12628 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd)::tl -> begin
(

let uu____12663 = hd
in (match (uu____12663) with
| (uu____12670, env, u, tm, k, r) -> begin
(

let uu____12676 = (unresolved u)
in (match (uu____12676) with
| true -> begin
(until_fixpoint (((hd)::out), (changed)) tl)
end
| uu____12690 -> begin
(

let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in ((

let uu____12694 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____12694) with
| true -> begin
(

let uu____12695 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____12699 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____12700 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" uu____12695 uu____12699 uu____12700))))
end
| uu____12701 -> begin
()
end));
(

let uu____12702 = (env.FStar_TypeChecker_Env.type_of (

let uu___176_12706 = env
in {FStar_TypeChecker_Env.solver = uu___176_12706.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___176_12706.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___176_12706.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___176_12706.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___176_12706.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___176_12706.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___176_12706.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___176_12706.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___176_12706.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___176_12706.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___176_12706.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___176_12706.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___176_12706.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___176_12706.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___176_12706.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___176_12706.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___176_12706.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___176_12706.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___176_12706.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___176_12706.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___176_12706.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___176_12706.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___176_12706.FStar_TypeChecker_Env.qname_and_index}) tm)
in (match (uu____12702) with
| (uu____12707, uu____12708, g) -> begin
(

let g = (match (env.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___177_12711 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___177_12711.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___177_12711.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___177_12711.FStar_TypeChecker_Env.implicits})
end
| uu____12712 -> begin
g
end)
in (

let g' = (

let uu____12714 = (discharge_guard' (Some ((fun uu____12718 -> (FStar_Syntax_Print.term_to_string tm)))) env g true)
in (match (uu____12714) with
| Some (g) -> begin
g
end
| None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end))
in (until_fixpoint (((FStar_List.append g'.FStar_TypeChecker_Env.implicits out)), (true)) tl)))
end));
)))
end))
end))
end)
end)))
in (

let uu___178_12733 = g
in (

let uu____12734 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___178_12733.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___178_12733.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___178_12733.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____12734})))))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g = (

let uu____12762 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____12762 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(

let uu____12769 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore uu____12769))
end
| ((reason, uu____12771, uu____12772, e, t, r))::uu____12776 -> begin
(

let uu____12790 = (

let uu____12791 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____12792 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" uu____12791 uu____12792 reason)))
in (FStar_Errors.report r uu____12790))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___179_12799 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___179_12799.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___179_12799.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ((((u1), (u2)))::[])); FStar_TypeChecker_Env.implicits = uu___179_12799.FStar_TypeChecker_Env.implicits}))


let teq_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____12817 = (try_teq env t1 t2)
in (match (uu____12817) with
| None -> begin
false
end
| Some (g) -> begin
(

let uu____12820 = (discharge_guard' None env g false)
in (match (uu____12820) with
| Some (uu____12824) -> begin
true
end
| None -> begin
false
end))
end)))





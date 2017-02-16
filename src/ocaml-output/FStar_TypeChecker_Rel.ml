
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

let may_relate = (fun head -> (

let uu____7092 = (

let uu____7093 = (FStar_Syntax_Util.un_uinst head)
in uu____7093.FStar_Syntax_Syntax.n)
in (match (uu____7092) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____7099 -> begin
false
end)))
in (

let uu____7100 = (((may_relate head1) || (may_relate head2)) && wl.smt_ok)
in (match (uu____7100) with
| true -> begin
(

let guard = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end
| uu____7106 -> begin
(

let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(

let x = (FStar_Syntax_Syntax.new_bv None t1)
in (

let uu____7120 = (

let uu____7121 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 uu____7121 t2))
in (FStar_Syntax_Util.mk_forall x uu____7120)))
end))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB)) with
| true -> begin
(has_type_guard t1 t2)
end
| uu____7124 -> begin
(has_type_guard t2 t1)
end))
end)
in (

let uu____7125 = (solve_prob orig (Some (guard)) [] wl)
in (solve env uu____7125)))
end
| uu____7128 -> begin
(giveup env "head mismatch" orig)
end)))
end
| (uu____7129, Some (t1, t2)) -> begin
(solve_t env (

let uu___151_7137 = problem
in {FStar_TypeChecker_Common.pid = uu___151_7137.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___151_7137.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___151_7137.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___151_7137.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___151_7137.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___151_7137.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___151_7137.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___151_7137.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____7138, None) -> begin
((

let uu____7145 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7145) with
| true -> begin
(

let uu____7146 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____7147 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____7148 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____7149 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" uu____7146 uu____7147 uu____7148 uu____7149)))))
end
| uu____7150 -> begin
()
end));
(

let uu____7151 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____7151) with
| (head1, args1) -> begin
(

let uu____7177 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____7177) with
| (head2, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((nargs <> (FStar_List.length args2))) with
| true -> begin
(

let uu____7217 = (

let uu____7218 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____7219 = (args_to_string args1)
in (

let uu____7220 = (FStar_Syntax_Print.term_to_string head2)
in (

let uu____7221 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____7218 uu____7219 uu____7220 uu____7221)))))
in (giveup env uu____7217 orig))
end
| uu____7222 -> begin
(

let uu____7223 = ((nargs = (Prims.parse_int "0")) || (

let uu____7226 = (FStar_Syntax_Util.eq_args args1 args2)
in (uu____7226 = FStar_Syntax_Util.Equal)))
in (match (uu____7223) with
| true -> begin
(

let uu____7227 = (solve_maybe_uinsts env orig head1 head2 wl)
in (match (uu____7227) with
| USolved (wl) -> begin
(

let uu____7229 = (solve_prob orig None [] wl)
in (solve env uu____7229))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end))
end
| uu____7232 -> begin
(

let uu____7233 = (base_and_refinement env wl t1)
in (match (uu____7233) with
| (base1, refinement1) -> begin
(

let uu____7259 = (base_and_refinement env wl t2)
in (match (uu____7259) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (None, None) -> begin
(

let uu____7313 = (solve_maybe_uinsts env orig head1 head2 wl)
in (match (uu____7313) with
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end
| USolved (wl) -> begin
(

let subprobs = (FStar_List.map2 (fun uu____7323 uu____7324 -> (match (((uu____7323), (uu____7324))) with
| ((a, uu____7334), (a', uu____7336)) -> begin
(

let uu____7341 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _0_45 -> FStar_TypeChecker_Common.TProb (_0_45)) uu____7341))
end)) args1 args2)
in (

let formula = (

let uu____7347 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____7347))
in (

let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end))
end
| uu____7351 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env (

let uu___152_7384 = problem
in {FStar_TypeChecker_Common.pid = uu___152_7384.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___152_7384.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___152_7384.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___152_7384.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___152_7384.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___152_7384.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___152_7384.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___152_7384.FStar_TypeChecker_Common.rank}) wl)))
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

let uu____7404 = p
in (match (uu____7404) with
| (((u, k), xs, c), ps, (h, uu____7415, qs)) -> begin
(

let xs = (sn_binders env xs)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____7464 = (imitation_sub_probs orig env xs ps qs)
in (match (uu____7464) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (

let uu____7478 = (h gs_xs)
in (

let uu____7479 = (

let uu____7486 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_46 -> FStar_Util.Inl (_0_46)))
in (FStar_All.pipe_right uu____7486 (fun _0_47 -> Some (_0_47))))
in (FStar_Syntax_Util.abs xs uu____7478 uu____7479)))
in ((

let uu____7517 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7517) with
| true -> begin
(

let uu____7518 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (

let uu____7519 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____7520 = (FStar_Syntax_Print.term_to_string im)
in (

let uu____7521 = (FStar_Syntax_Print.tag_of_term im)
in (

let uu____7522 = (

let uu____7523 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right uu____7523 (FStar_String.concat ", ")))
in (

let uu____7526 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" uu____7518 uu____7519 uu____7520 uu____7521 uu____7522 uu____7526)))))))
end
| uu____7527 -> begin
()
end));
(

let wl = (solve_prob orig (Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl)
in (solve env (attempt sub_probs wl)));
))
end))))
end)))
in (

let imitate' = (fun orig env wl uu___123_7544 -> (match (uu___123_7544) with
| None -> begin
(giveup env "unable to compute subterms" orig)
end
| Some (p) -> begin
(imitate orig env wl p)
end))
in (

let project = (fun orig env wl i p -> (

let uu____7573 = p
in (match (uu____7573) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____7631 = (FStar_List.nth ps i)
in (match (uu____7631) with
| (pi, uu____7634) -> begin
(

let uu____7639 = (FStar_List.nth xs i)
in (match (uu____7639) with
| (xi, uu____7646) -> begin
(

let rec gs = (fun k -> (

let uu____7655 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____7655) with
| (bs, k) -> begin
(

let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
(([]), ([]))
end
| ((a, uu____7707))::tl -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (

let uu____7715 = (new_uvar r xs k_a)
in (match (uu____7715) with
| (gi_xs, gi) -> begin
(

let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (

let gi_ps = ((FStar_Syntax_Syntax.mk_Tm_app gi ps) (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst = (FStar_Syntax_Syntax.NT (((a), (gi_xs))))::subst
in (

let uu____7734 = (aux subst tl)
in (match (uu____7734) with
| (gi_xs', gi_ps') -> begin
(

let uu____7749 = (

let uu____7751 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (uu____7751)::gi_xs')
in (

let uu____7752 = (

let uu____7754 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (uu____7754)::gi_ps')
in ((uu____7749), (uu____7752))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in (

let uu____7757 = (

let uu____7758 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation uu____7758))
in (match (uu____7757) with
| true -> begin
None
end
| uu____7760 -> begin
(

let uu____7761 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (uu____7761) with
| (g_xs, uu____7768) -> begin
(

let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (

let uu____7775 = ((FStar_Syntax_Syntax.mk_Tm_app xi g_xs) None r)
in (

let uu____7780 = (

let uu____7787 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_48 -> FStar_Util.Inl (_0_48)))
in (FStar_All.pipe_right uu____7787 (fun _0_49 -> Some (_0_49))))
in (FStar_Syntax_Util.abs xs uu____7775 uu____7780)))
in (

let sub = (

let uu____7818 = (

let uu____7821 = ((FStar_Syntax_Syntax.mk_Tm_app proj ps) None r)
in (

let uu____7828 = (

let uu____7831 = (FStar_List.map (fun uu____7837 -> (match (uu____7837) with
| (uu____7842, uu____7843, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h uu____7831))
in (mk_problem (p_scope orig) orig uu____7821 (p_rel orig) uu____7828 None "projection")))
in (FStar_All.pipe_left (fun _0_50 -> FStar_TypeChecker_Common.TProb (_0_50)) uu____7818))
in ((

let uu____7853 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7853) with
| true -> begin
(

let uu____7854 = (FStar_Syntax_Print.term_to_string proj)
in (

let uu____7855 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" uu____7854 uu____7855)))
end
| uu____7856 -> begin
()
end));
(

let wl = (

let uu____7858 = (

let uu____7860 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (uu____7860))
in (solve_prob orig uu____7858 ((TERM (((u), (proj))))::[]) wl))
in (

let uu____7865 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _0_51 -> Some (_0_51)) uu____7865)));
))))
end))
end)))
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl -> (

let uu____7889 = lhs
in (match (uu____7889) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let uu____7912 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (uu____7912) with
| (xs, c) -> begin
(match (((FStar_List.length xs) = (FStar_List.length ps))) with
| true -> begin
(

let uu____7934 = (

let uu____7960 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____7960)))
in Some (uu____7934))
end
| uu____8026 -> begin
(

let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (

let uu____8043 = (

let uu____8047 = (

let uu____8048 = (FStar_Syntax_Subst.compress k)
in uu____8048.FStar_Syntax_Syntax.n)
in ((uu____8047), (args)))
in (match (uu____8043) with
| (uu____8055, []) -> begin
(

let uu____8057 = (

let uu____8063 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____8063)))
in Some (uu____8057))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(

let uu____8080 = (FStar_Syntax_Util.head_and_args k)
in (match (uu____8080) with
| (uv, uv_args) -> begin
(

let uu____8109 = (

let uu____8110 = (FStar_Syntax_Subst.compress uv)
in uu____8110.FStar_Syntax_Syntax.n)
in (match (uu____8109) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____8117) -> begin
(

let uu____8130 = (pat_vars env [] uv_args)
in (match (uu____8130) with
| None -> begin
None
end
| Some (scope) -> begin
(

let xs = (FStar_All.pipe_right args (FStar_List.map (fun uu____8144 -> (

let uu____8145 = (

let uu____8146 = (

let uu____8147 = (

let uu____8150 = (

let uu____8151 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8151 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____8150))
in (Prims.fst uu____8147))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) uu____8146))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____8145)))))
in (

let c = (

let uu____8157 = (

let uu____8158 = (

let uu____8161 = (

let uu____8162 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8162 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____8161))
in (Prims.fst uu____8158))
in (FStar_Syntax_Syntax.mk_Total uu____8157))
in (

let k' = (FStar_Syntax_Util.arrow xs c)
in (

let uv_sol = (

let uu____8171 = (

let uu____8178 = (

let uu____8184 = (

let uu____8185 = (

let uu____8188 = (

let uu____8189 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8189 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total uu____8188))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8185))
in FStar_Util.Inl (uu____8184))
in Some (uu____8178))
in (FStar_Syntax_Util.abs scope k' uu____8171))
in ((FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)));
Some (((xs), (c)));
)))))
end))
end
| uu____8212 -> begin
None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), uu____8217) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs)
in (match ((n_xs = n_args)) with
| true -> begin
(

let uu____8243 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right uu____8243 (fun _0_52 -> Some (_0_52))))
end
| uu____8253 -> begin
(match ((n_xs < n_args)) with
| true -> begin
(

let uu____8262 = (FStar_Util.first_N n_xs args)
in (match (uu____8262) with
| (args, rest) -> begin
(

let uu____8278 = (FStar_Syntax_Subst.open_comp xs c)
in (match (uu____8278) with
| (xs, c) -> begin
(

let uu____8286 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt uu____8286 (fun uu____8297 -> (match (uu____8297) with
| (xs', c) -> begin
Some ((((FStar_List.append xs xs')), (c)))
end))))
end))
end))
end
| uu____8318 -> begin
(

let uu____8319 = (FStar_Util.first_N n_args xs)
in (match (uu____8319) with
| (xs, rest) -> begin
(

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c))))) None k.FStar_Syntax_Syntax.pos)
in (

let uu____8365 = (

let uu____8368 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs uu____8368))
in (FStar_All.pipe_right uu____8365 (fun _0_53 -> Some (_0_53)))))
end))
end)
end)))
end
| uu____8376 -> begin
(

let uu____8380 = (

let uu____8381 = (FStar_Syntax_Print.uvar_to_string uv)
in (

let uu____8385 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____8386 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" uu____8381 uu____8385 uu____8386))))
in (failwith uu____8380))
end)))
in (

let uu____8390 = (elim k_uv ps)
in (FStar_Util.bind_opt uu____8390 (fun uu____8418 -> (match (uu____8418) with
| (xs, c) -> begin
(

let uu____8446 = (

let uu____8469 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____8469)))
in Some (uu____8446))
end))))))
end)
end)))
in (

let rec imitate_or_project = (fun n stopt i -> (match (((i >= n) || (FStar_Option.isNone stopt))) with
| true -> begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end
| uu____8538 -> begin
(

let st = (FStar_Option.get stopt)
in (

let tx = (FStar_Unionfind.new_transaction ())
in (match ((i = (~- ((Prims.parse_int "1"))))) with
| true -> begin
(

let uu____8541 = (imitate orig env wl st)
in (match (uu____8541) with
| Failed (uu____8546) -> begin
((FStar_Unionfind.rollback tx);
(imitate_or_project n stopt (i + (Prims.parse_int "1")));
)
end
| sol -> begin
sol
end))
end
| uu____8551 -> begin
(

let uu____8552 = (project orig env wl i st)
in (match (uu____8552) with
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

let uu____8570 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____8570) with
| (hd, uu____8581) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| uu____8599 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd)
in (

let uu____8602 = (FStar_Util.set_is_subset_of fvs_hd fvs1)
in (match (uu____8602) with
| true -> begin
true
end
| uu____8603 -> begin
((

let uu____8605 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8605) with
| true -> begin
(

let uu____8606 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" uu____8606))
end
| uu____8607 -> begin
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

let uu____8614 = (

let uu____8617 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____8617 Prims.fst))
in (FStar_All.pipe_right uu____8614 FStar_Syntax_Free.names))
in (

let uu____8648 = (FStar_Util.set_is_empty fvs_hd)
in (match (uu____8648) with
| true -> begin
(~- ((Prims.parse_int "1")))
end
| uu____8649 -> begin
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

let uu____8657 = (occurs_check env wl ((uv), (k_uv)) t2)
in (match (uu____8657) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____8665 = (

let uu____8666 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____8666))
in (giveup_or_defer orig uu____8665))
end
| uu____8667 -> begin
(

let uu____8668 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____8668) with
| true -> begin
(

let uu____8669 = (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t2)) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))
in (match (uu____8669) with
| true -> begin
(

let uu____8670 = (subterms args_lhs)
in (imitate' orig env wl uu____8670))
end
| uu____8672 -> begin
((

let uu____8674 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8674) with
| true -> begin
(

let uu____8675 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____8676 = (names_to_string fvs1)
in (

let uu____8677 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" uu____8675 uu____8676 uu____8677))))
end
| uu____8678 -> begin
()
end));
(

let sol = (match (vars) with
| [] -> begin
t2
end
| uu____8682 -> begin
(

let uu____8683 = (sn_binders env vars)
in (u_abs k_uv uu____8683 t2))
end)
in (

let wl = (solve_prob orig None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl)
in (solve env wl)));
)
end))
end
| uu____8690 -> begin
(match ((((not (patterns_only)) && wl.defer_ok) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end
| uu____8691 -> begin
(

let uu____8692 = ((not (patterns_only)) && (check_head fvs1 t2))
in (match (uu____8692) with
| true -> begin
((

let uu____8694 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8694) with
| true -> begin
(

let uu____8695 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____8696 = (names_to_string fvs1)
in (

let uu____8697 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" uu____8695 uu____8696 uu____8697))))
end
| uu____8698 -> begin
()
end));
(

let uu____8699 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____8699 (~- ((Prims.parse_int "1")))));
)
end
| uu____8708 -> begin
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
| uu____8709 -> begin
(

let uu____8710 = (

let uu____8711 = (FStar_Syntax_Free.names t1)
in (check_head uu____8711 t2))
in (match (uu____8710) with
| true -> begin
(

let im_ok = (imitate_ok t2)
in ((

let uu____8715 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8715) with
| true -> begin
(

let uu____8716 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" uu____8716 (match ((im_ok < (Prims.parse_int "0"))) with
| true -> begin
"imitating"
end
| uu____8717 -> begin
"projecting"
end)))
end
| uu____8718 -> begin
()
end));
(

let uu____8719 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____8719 im_ok));
))
end
| uu____8728 -> begin
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
| uu____8739 -> begin
(

let force_quasi_pattern = (fun xs_opt uu____8761 -> (match (uu____8761) with
| (t, u, k, args) -> begin
(

let uu____8791 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____8791) with
| (all_formals, uu____8802) -> begin
(

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match (((formals), (args))) with
| ([], []) -> begin
(

let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun uu____8894 -> (match (uu____8894) with
| (x, imp) -> begin
(

let uu____8901 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____8901), (imp)))
end))))
in (

let pattern_vars = (FStar_List.rev pattern_vars)
in (

let kk = (

let uu____8909 = (FStar_Syntax_Util.type_u ())
in (match (uu____8909) with
| (t, uu____8913) -> begin
(

let uu____8914 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst uu____8914))
end))
in (

let uu____8917 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (uu____8917) with
| (t', tm_u1) -> begin
(

let uu____8924 = (destruct_flex_t t')
in (match (uu____8924) with
| (uu____8944, u1, k1, uu____8947) -> begin
(

let sol = (

let uu____8975 = (

let uu____8980 = (u_abs k all_formals t')
in ((((u), (k))), (uu____8980)))
in TERM (uu____8975))
in (

let t_app = ((FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args) None t.FStar_Syntax_Syntax.pos)
in ((sol), (((t_app), (u1), (k1), (pat_args))))))
end))
end)))))
end
| ((formal)::formals, (hd)::tl) -> begin
(

let uu____9040 = (pat_var_opt env pat_args hd)
in (match (uu____9040) with
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun uu____9069 -> (match (uu____9069) with
| (x, uu____9073) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in (match ((not (maybe_pat))) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| uu____9076 -> begin
(

let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____9079 = (

let uu____9080 = (FStar_Util.set_is_subset_of fvs pattern_var_set)
in (not (uu____9080)))
in (match (uu____9079) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| uu____9083 -> begin
(

let uu____9084 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) uu____9084 formals tl))
end)))
end))
end))
end
| uu____9090 -> begin
(failwith "Impossible")
end))
in (

let uu____9101 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] uu____9101 all_formals args)))
end))
end))
in (

let solve_both_pats = (fun wl uu____9149 uu____9150 r -> (match (((uu____9149), (uu____9150))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
(

let uu____9304 = ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys))
in (match (uu____9304) with
| true -> begin
(

let uu____9308 = (solve_prob orig None [] wl)
in (solve env uu____9308))
end
| uu____9309 -> begin
(

let xs = (sn_binders env xs)
in (

let ys = (sn_binders env ys)
in (

let zs = (intersect_vars xs ys)
in ((

let uu____9323 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9323) with
| true -> begin
(

let uu____9324 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (

let uu____9325 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (

let uu____9326 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (

let uu____9327 = (FStar_Syntax_Print.term_to_string k1)
in (

let uu____9328 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" uu____9324 uu____9325 uu____9326 uu____9327 uu____9328))))))
end
| uu____9329 -> begin
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

let uu____9370 = (FStar_Syntax_Util.subst_of_list xs args)
in (FStar_Syntax_Subst.subst uu____9370 k))
end
| uu____9372 -> begin
(match ((args_len < xs_len)) with
| true -> begin
(

let uu____9378 = (FStar_Util.first_N args_len xs)
in (match (uu____9378) with
| (xs, xs_rest) -> begin
(

let k = (

let uu____9408 = (FStar_Syntax_Syntax.mk_GTotal k)
in (FStar_Syntax_Util.arrow xs_rest uu____9408))
in (

let uu____9411 = (FStar_Syntax_Util.subst_of_list xs args)
in (FStar_Syntax_Subst.subst uu____9411 k)))
end))
end
| uu____9413 -> begin
(

let uu____9414 = (

let uu____9415 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____9416 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (

let uu____9417 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" uu____9415 uu____9416 uu____9417))))
in (failwith uu____9414))
end)
end))))
in (

let uu____9418 = (

let uu____9424 = (

let uu____9432 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals uu____9432))
in (match (uu____9424) with
| (bs, k1') -> begin
(

let uu____9450 = (

let uu____9458 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals uu____9458))
in (match (uu____9450) with
| (cs, k2') -> begin
(

let k1'_xs = (subst_k k1' bs args1)
in (

let k2'_ys = (subst_k k2' cs args2)
in (

let sub_prob = (

let uu____9479 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_54 -> FStar_TypeChecker_Common.TProb (_0_54)) uu____9479))
in (

let uu____9484 = (

let uu____9487 = (

let uu____9488 = (FStar_Syntax_Subst.compress k1')
in uu____9488.FStar_Syntax_Syntax.n)
in (

let uu____9491 = (

let uu____9492 = (FStar_Syntax_Subst.compress k2')
in uu____9492.FStar_Syntax_Syntax.n)
in ((uu____9487), (uu____9491))))
in (match (uu____9484) with
| (FStar_Syntax_Syntax.Tm_type (uu____9500), uu____9501) -> begin
((k1'), ((sub_prob)::[]))
end
| (uu____9505, FStar_Syntax_Syntax.Tm_type (uu____9506)) -> begin
((k2'), ((sub_prob)::[]))
end
| uu____9510 -> begin
(

let uu____9513 = (FStar_Syntax_Util.type_u ())
in (match (uu____9513) with
| (t, uu____9522) -> begin
(

let uu____9523 = (new_uvar r zs t)
in (match (uu____9523) with
| (k_zs, uu____9532) -> begin
(

let kprob = (

let uu____9534 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k_zs None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_55 -> FStar_TypeChecker_Common.TProb (_0_55)) uu____9534))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end)))))
end))
end))
in (match (uu____9418) with
| (k_u', sub_probs) -> begin
(

let uu____9548 = (

let uu____9556 = (

let uu____9557 = (new_uvar r zs k_u')
in (FStar_All.pipe_left Prims.fst uu____9557))
in (

let uu____9562 = (

let uu____9565 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs uu____9565))
in (

let uu____9568 = (

let uu____9571 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys uu____9571))
in ((uu____9556), (uu____9562), (uu____9568)))))
in (match (uu____9548) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs u_zs)
in (

let uu____9590 = (occurs_check env wl ((u1), (k1)) sub1)
in (match (uu____9590) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end
| uu____9602 -> begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in (

let uu____9614 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____9614) with
| true -> begin
(

let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end
| uu____9619 -> begin
(

let sub2 = (u_abs knew2 ys u_zs)
in (

let uu____9621 = (occurs_check env wl ((u2), (k2)) sub2)
in (match (uu____9621) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end
| uu____9633 -> begin
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

let solve_one_pat = (fun uu____9673 uu____9674 -> (match (((uu____9673), (uu____9674))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
((

let uu____9778 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9778) with
| true -> begin
(

let uu____9779 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____9780 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" uu____9779 uu____9780)))
end
| uu____9781 -> begin
()
end));
(

let uu____9782 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____9782) with
| true -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____9792 uu____9793 -> (match (((uu____9792), (uu____9793))) with
| ((a, uu____9803), (t2, uu____9805)) -> begin
(

let uu____9810 = (

let uu____9813 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig uu____9813 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right uu____9810 (fun _0_56 -> FStar_TypeChecker_Common.TProb (_0_56))))
end)) xs args2)
in (

let guard = (

let uu____9817 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____9817))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end
| uu____9823 -> begin
(

let t2 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t2)
in (

let uu____9827 = (occurs_check env wl ((u1), (k1)) t2)
in (match (uu____9827) with
| (occurs_ok, uu____9836) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in (

let uu____9841 = (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars))
in (match (uu____9841) with
| true -> begin
(

let sol = (

let uu____9843 = (

let uu____9848 = (u_abs k1 xs t2)
in ((((u1), (k1))), (uu____9848)))
in TERM (uu____9843))
in (

let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end
| uu____9860 -> begin
(

let uu____9861 = (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok))
in (match (uu____9861) with
| true -> begin
(

let uu____9862 = (force_quasi_pattern (Some (xs)) ((t2), (u2), (k2), (args2)))
in (match (uu____9862) with
| (sol, (uu____9876, u2, k2, ys)) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____9886 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____9886) with
| true -> begin
(

let uu____9887 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" uu____9887))
end
| uu____9888 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| uu____9892 -> begin
(giveup env "impossible" orig)
end);
))
end))
end
| uu____9893 -> begin
(giveup_or_defer orig "flex-flex constraint")
end))
end)))
end))))
end));
)
end))
in (

let uu____9894 = lhs
in (match (uu____9894) with
| (t1, u1, k1, args1) -> begin
(

let uu____9899 = rhs
in (match (uu____9899) with
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
| uu____9925 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end
| uu____9930 -> begin
(

let uu____9931 = (force_quasi_pattern None ((t1), (u1), (k1), (args1)))
in (match (uu____9931) with
| (sol, uu____9938) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____9941 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____9941) with
| true -> begin
(

let uu____9942 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" uu____9942))
end
| uu____9943 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| uu____9947 -> begin
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

let uu____9949 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____9949) with
| true -> begin
(

let uu____9950 = (solve_prob orig None [] wl)
in (solve env uu____9950))
end
| uu____9951 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in (

let uu____9954 = (FStar_Util.physical_equality t1 t2)
in (match (uu____9954) with
| true -> begin
(

let uu____9955 = (solve_prob orig None [] wl)
in (solve env uu____9955))
end
| uu____9956 -> begin
((

let uu____9958 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____9958) with
| true -> begin
(

let uu____9959 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" uu____9959))
end
| uu____9960 -> begin
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

let mk_c = (fun c uu___124_10005 -> (match (uu___124_10005) with
| [] -> begin
c
end
| bs -> begin
(

let uu____10019 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c))))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____10019))
end))
in (

let uu____10033 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____10033) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (

let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (

let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (

let rel = (

let uu____10119 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____10119) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____10120 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (

let uu____10121 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _0_57 -> FStar_TypeChecker_Common.CProb (_0_57)) uu____10121)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___125_10198 -> (match (uu___125_10198) with
| [] -> begin
t
end
| bs -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l))))) None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____10237 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____10237) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (

let uu____10320 = (

let uu____10323 = (FStar_Syntax_Subst.subst subst tbody1)
in (

let uu____10324 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig uu____10323 problem.FStar_TypeChecker_Common.relation uu____10324 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _0_58 -> FStar_TypeChecker_Common.TProb (_0_58)) uu____10320))))
end)))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____10339) -> begin
true
end
| uu____10354 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____10373 -> begin
(

let t = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____10379 -> begin
FStar_Util.Inr (t)
end))
end))
in (

let uu____10382 = (

let uu____10393 = (maybe_eta t1)
in (

let uu____10398 = (maybe_eta t2)
in ((uu____10393), (uu____10398))))
in (match (uu____10382) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(solve_t env (

let uu___153_10429 = problem
in {FStar_TypeChecker_Common.pid = uu___153_10429.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___153_10429.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___153_10429.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___153_10429.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___153_10429.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___153_10429.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___153_10429.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___153_10429.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs))) | ((FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs))) -> begin
(

let uu____10462 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____10462) with
| true -> begin
(

let uu____10463 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____10463 t_abs wl))
end
| uu____10467 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| uu____10468 -> begin
(failwith "Impossible: at least one side is an abstraction")
end))))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____10479), FStar_Syntax_Syntax.Tm_refine (uu____10480)) -> begin
(

let uu____10489 = (as_refinement env wl t1)
in (match (uu____10489) with
| (x1, phi1) -> begin
(

let uu____10494 = (as_refinement env wl t2)
in (match (uu____10494) with
| (x2, phi2) -> begin
(

let base_prob = (

let uu____10500 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _0_59 -> FStar_TypeChecker_Common.TProb (_0_59)) uu____10500))
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

let uu____10533 = (imp phi1 phi2)
in (FStar_All.pipe_right uu____10533 (guard_on_element problem x1))))
in (

let fallback = (fun uu____10537 -> (

let impl = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end
| uu____10539 -> begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end)
in (

let guard = (

let uu____10543 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____10543 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl))))))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let ref_prob = (

let uu____10550 = (

let uu____10553 = (

let uu____10554 = (FStar_Syntax_Syntax.mk_binder x1)
in (uu____10554)::(p_scope orig))
in (mk_problem uu____10553 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _0_60 -> FStar_TypeChecker_Common.TProb (_0_60)) uu____10550))
in (

let uu____10557 = (solve env (

let uu___154_10558 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___154_10558.ctr; defer_ok = false; smt_ok = uu___154_10558.smt_ok; tcenv = uu___154_10558.tcenv}))
in (match (uu____10557) with
| Failed (uu____10562) -> begin
(fallback ())
end
| Success (uu____10565) -> begin
(

let guard = (

let uu____10569 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (

let uu____10572 = (

let uu____10573 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right uu____10573 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj uu____10569 uu____10572)))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (

let wl = (

let uu___155_10580 = wl
in {attempting = uu___155_10580.attempting; wl_deferred = uu___155_10580.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___155_10580.defer_ok; smt_ok = uu___155_10580.smt_ok; tcenv = uu___155_10580.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end)))
end
| uu____10581 -> begin
(fallback ())
end)))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(

let uu____10634 = (destruct_flex_t t1)
in (

let uu____10635 = (destruct_flex_t t2)
in (flex_flex orig uu____10634 uu____10635)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(

let uu____10651 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____10651 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_arrow (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
(solve_t' env (

let uu___156_10700 = problem
in {FStar_TypeChecker_Common.pid = uu___156_10700.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___156_10700.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___156_10700.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___156_10700.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___156_10700.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___156_10700.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___156_10700.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___156_10700.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___156_10700.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____10716 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____10718 = (

let uu____10719 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____10719))
in (match (uu____10718) with
| true -> begin
(

let uu____10720 = (FStar_All.pipe_left (fun _0_61 -> FStar_TypeChecker_Common.TProb (_0_61)) (

let uu___157_10723 = problem
in {FStar_TypeChecker_Common.pid = uu___157_10723.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___157_10723.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___157_10723.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___157_10723.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___157_10723.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___157_10723.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___157_10723.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___157_10723.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___157_10723.FStar_TypeChecker_Common.rank}))
in (

let uu____10724 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____10720 uu____10724 t2 wl)))
end
| uu____10728 -> begin
(

let uu____10729 = (base_and_refinement env wl t2)
in (match (uu____10729) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(

let uu____10759 = (FStar_All.pipe_left (fun _0_62 -> FStar_TypeChecker_Common.TProb (_0_62)) (

let uu___158_10762 = problem
in {FStar_TypeChecker_Common.pid = uu___158_10762.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___158_10762.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___158_10762.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___158_10762.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___158_10762.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___158_10762.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___158_10762.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___158_10762.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___158_10762.FStar_TypeChecker_Common.rank}))
in (

let uu____10763 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____10759 uu____10763 t_base wl)))
end
| Some (y, phi) -> begin
(

let y' = (

let uu___159_10778 = y
in {FStar_Syntax_Syntax.ppname = uu___159_10778.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___159_10778.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element problem y' phi)
in (

let base_prob = (

let uu____10781 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_63 -> FStar_TypeChecker_Common.TProb (_0_63)) uu____10781))
in (

let guard = (

let uu____10789 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____10789 impl))
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
| uu____10810 -> begin
(

let uu____10811 = (base_and_refinement env wl t1)
in (match (uu____10811) with
| (t_base, uu____10822) -> begin
(solve_t env (

let uu___160_10837 = problem
in {FStar_TypeChecker_Common.pid = uu___160_10837.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___160_10837.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___160_10837.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___160_10837.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___160_10837.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___160_10837.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___160_10837.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___160_10837.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (FStar_Syntax_Syntax.Tm_refine (uu____10840), uu____10841) -> begin
(

let t2 = (

let uu____10849 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement uu____10849))
in (solve_t env (

let uu___161_10862 = problem
in {FStar_TypeChecker_Common.pid = uu___161_10862.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___161_10862.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___161_10862.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___161_10862.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___161_10862.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___161_10862.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___161_10862.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___161_10862.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___161_10862.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____10863, FStar_Syntax_Syntax.Tm_refine (uu____10864)) -> begin
(

let t1 = (

let uu____10872 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement uu____10872))
in (solve_t env (

let uu___162_10885 = problem
in {FStar_TypeChecker_Common.pid = uu___162_10885.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___162_10885.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___162_10885.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___162_10885.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_10885.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_10885.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_10885.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_10885.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_10885.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(

let head1 = (

let uu____10915 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____10915 Prims.fst))
in (

let head2 = (

let uu____10946 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____10946 Prims.fst))
in (

let uu____10974 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____10974) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____10983 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____10983) with
| true -> begin
(

let guard = (

let uu____10992 = (

let uu____10993 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____10993 = FStar_Syntax_Util.Equal))
in (match (uu____10992) with
| true -> begin
None
end
| uu____10999 -> begin
(

let uu____11000 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _0_64 -> Some (_0_64)) uu____11000))
end))
in (

let uu____11010 = (solve_prob orig guard [] wl)
in (solve env uu____11010)))
end
| uu____11011 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____11012 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, uu____11014, uu____11015), uu____11016) -> begin
(solve_t' env (

let uu___163_11035 = problem
in {FStar_TypeChecker_Common.pid = uu___163_11035.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___163_11035.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___163_11035.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___163_11035.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___163_11035.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___163_11035.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___163_11035.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___163_11035.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___163_11035.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____11038, FStar_Syntax_Syntax.Tm_ascribed (t2, uu____11040, uu____11041)) -> begin
(solve_t' env (

let uu___164_11060 = problem
in {FStar_TypeChecker_Common.pid = uu___164_11060.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___164_11060.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___164_11060.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___164_11060.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_11060.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_11060.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_11060.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_11060.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_11060.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(

let uu____11073 = (

let uu____11074 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____11075 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____11074 uu____11075)))
in (failwith uu____11073))
end
| uu____11076 -> begin
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

let uu____11108 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____11108) with
| true -> begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end
| uu____11109 -> begin
()
end));
(

let sub_probs = (FStar_List.map2 (fun uu____11116 uu____11117 -> (match (((uu____11116), (uu____11117))) with
| ((a1, uu____11127), (a2, uu____11129)) -> begin
(

let uu____11134 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _0_65 -> FStar_TypeChecker_Common.TProb (_0_65)) uu____11134))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (

let uu____11140 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____11140))
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
| ((wp1, uu____11163))::[] -> begin
wp1
end
| uu____11176 -> begin
(

let uu____11182 = (

let uu____11183 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" uu____11183))
in (failwith uu____11182))
end)
in (

let c1 = (

let uu____11187 = (

let uu____11193 = (

let uu____11194 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____11194))
in (uu____11193)::[])
in {FStar_Syntax_Syntax.comp_univs = c1.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____11187; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2)))
end
| uu____11195 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___126_11198 -> (match (uu___126_11198) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| uu____11199 -> begin
false
end))))
in (

let uu____11200 = (match (((c1.FStar_Syntax_Syntax.effect_args), (c2.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____11224))::uu____11225, ((wp2, uu____11227))::uu____11228) -> begin
((wp1), (wp2))
end
| uu____11269 -> begin
(

let uu____11282 = (

let uu____11283 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____11284 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____11283 uu____11284)))
in (failwith uu____11282))
end)
in (match (uu____11200) with
| (wpc1, wpc2) -> begin
(

let uu____11301 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____11301) with
| true -> begin
(

let uu____11304 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env uu____11304 wl))
end
| uu____11307 -> begin
(

let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____11310 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____11312 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11312) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____11313 -> begin
()
end));
(

let uu____11314 = (

let uu____11317 = (

let uu____11318 = (

let uu____11328 = (

let uu____11329 = (

let uu____11330 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (uu____11330)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____11329 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (

let uu____11331 = (

let uu____11333 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____11334 = (

let uu____11336 = (

let uu____11337 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11337))
in (uu____11336)::[])
in (uu____11333)::uu____11334))
in ((uu____11328), (uu____11331))))
in FStar_Syntax_Syntax.Tm_app (uu____11318))
in (FStar_Syntax_Syntax.mk uu____11317))
in (uu____11314 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r));
)
end
| uu____11347 -> begin
(

let uu____11348 = (

let uu____11351 = (

let uu____11352 = (

let uu____11362 = (

let uu____11363 = (

let uu____11364 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (uu____11364)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____11363 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (

let uu____11365 = (

let uu____11367 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (

let uu____11368 = (

let uu____11370 = (FStar_Syntax_Syntax.as_arg wpc2)
in (

let uu____11371 = (

let uu____11373 = (

let uu____11374 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11374))
in (uu____11373)::[])
in (uu____11370)::uu____11371))
in (uu____11367)::uu____11368))
in ((uu____11362), (uu____11365))))
in FStar_Syntax_Syntax.Tm_app (uu____11352))
in (FStar_Syntax_Syntax.mk uu____11351))
in (uu____11348 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r))
end)
end)
in (

let base_prob = (

let uu____11385 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _0_66 -> FStar_TypeChecker_Common.TProb (_0_66)) uu____11385))
in (

let wl = (

let uu____11391 = (

let uu____11393 = (

let uu____11396 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____11396 g))
in (FStar_All.pipe_left (fun _0_67 -> Some (_0_67)) uu____11393))
in (solve_prob orig uu____11391 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end))
end)))
end)))
in (

let uu____11406 = (FStar_Util.physical_equality c1 c2)
in (match (uu____11406) with
| true -> begin
(

let uu____11407 = (solve_prob orig None [] wl)
in (solve env uu____11407))
end
| uu____11408 -> begin
((

let uu____11410 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11410) with
| true -> begin
(

let uu____11411 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____11412 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____11411 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____11412)))
end
| uu____11413 -> begin
()
end));
(

let uu____11414 = (

let uu____11417 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____11418 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____11417), (uu____11418))))
in (match (uu____11414) with
| (c1, c2) -> begin
(match (((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____11422), FStar_Syntax_Syntax.Total (t2, uu____11424)) when (FStar_Syntax_Util.non_informative t2) -> begin
(

let uu____11437 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env uu____11437 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____11440), FStar_Syntax_Syntax.Total (uu____11441)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.Total (t2, _))) | ((FStar_Syntax_Syntax.GTotal (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) | ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) -> begin
(

let uu____11490 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env uu____11490 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(

let uu____11497 = (

let uu___165_11500 = problem
in (

let uu____11503 = (

let uu____11504 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____11504))
in {FStar_TypeChecker_Common.pid = uu___165_11500.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____11503; FStar_TypeChecker_Common.relation = uu___165_11500.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___165_11500.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___165_11500.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___165_11500.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___165_11500.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___165_11500.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___165_11500.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___165_11500.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____11497 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(

let uu____11509 = (

let uu___166_11512 = problem
in (

let uu____11515 = (

let uu____11516 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c2)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____11516))
in {FStar_TypeChecker_Common.pid = uu___166_11512.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___166_11512.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___166_11512.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____11515; FStar_TypeChecker_Common.element = uu___166_11512.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_11512.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___166_11512.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___166_11512.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_11512.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_11512.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____11509 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____11517), FStar_Syntax_Syntax.Comp (uu____11518)) -> begin
(

let uu____11519 = (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2))))
in (match (uu____11519) with
| true -> begin
(

let uu____11520 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env uu____11520 wl))
end
| uu____11523 -> begin
(

let c1_comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c1)
in (

let c2_comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c2)
in (match (((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name))) with
| true -> begin
(solve_eq c1_comp c2_comp)
end
| uu____11526 -> begin
(

let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (

let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in ((

let uu____11530 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11530) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____11531 -> begin
()
end));
(

let uu____11532 = (FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (uu____11532) with
| None -> begin
(

let uu____11534 = (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (

let uu____11535 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative uu____11535)))
in (match (uu____11534) with
| true -> begin
(

let edge = {FStar_TypeChecker_Env.msource = c1.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c2.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = (fun r t -> t)}
in (solve_sub c1 edge c2))
end
| uu____11539 -> begin
(

let uu____11540 = (

let uu____11541 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____11542 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____11541 uu____11542)))
in (giveup env uu____11540 orig))
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

let uu____11547 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____11567 -> (match (uu____11567) with
| (uu____11578, uu____11579, u, uu____11581, uu____11582, uu____11583) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____11547 (FStar_String.concat ", "))))


let ineqs_to_string : (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.string = (fun ineqs -> (

let vars = (

let uu____11612 = (FStar_All.pipe_right (Prims.fst ineqs) (FStar_List.map FStar_Syntax_Print.univ_to_string))
in (FStar_All.pipe_right uu____11612 (FStar_String.concat ", ")))
in (

let ineqs = (

let uu____11622 = (FStar_All.pipe_right (Prims.snd ineqs) (FStar_List.map (fun uu____11634 -> (match (uu____11634) with
| (u1, u2) -> begin
(

let uu____11639 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____11640 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "%s < %s" uu____11639 uu____11640)))
end))))
in (FStar_All.pipe_right uu____11622 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred), (g.FStar_TypeChecker_Env.univ_ineqs))) with
| (FStar_TypeChecker_Common.Trivial, [], (uu____11652, [])) -> begin
"{}"
end
| uu____11665 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____11675 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____11675) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____11676 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____11678 = (FStar_List.map (fun uu____11682 -> (match (uu____11682) with
| (uu____11685, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right uu____11678 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (

let uu____11689 = (ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs)
in (FStar_Util.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n" form carry uu____11689 imps)))))
end))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu____11709; FStar_TypeChecker_Env.implicits = uu____11710} -> begin
true
end
| uu____11724 -> begin
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
| uu____11751 -> begin
(failwith "impossible")
end)
in (

let uu____11752 = (

let uu___167_11753 = g
in (

let uu____11754 = (

let uu____11755 = (

let uu____11756 = (

let uu____11760 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____11760)::[])
in (

let uu____11761 = (

let uu____11768 = (

let uu____11774 = (

let uu____11775 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____11775 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____11774 (fun _0_68 -> FStar_Util.Inl (_0_68))))
in Some (uu____11768))
in (FStar_Syntax_Util.abs uu____11756 f uu____11761)))
in (FStar_All.pipe_left (fun _0_69 -> FStar_TypeChecker_Common.NonTrivial (_0_69)) uu____11755))
in {FStar_TypeChecker_Env.guard_f = uu____11754; FStar_TypeChecker_Env.deferred = uu___167_11753.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___167_11753.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___167_11753.FStar_TypeChecker_Env.implicits}))
in Some (uu____11752)))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___168_11796 = g
in (

let uu____11797 = (

let uu____11798 = (

let uu____11799 = (

let uu____11802 = (

let uu____11803 = (

let uu____11813 = (

let uu____11815 = (FStar_Syntax_Syntax.as_arg e)
in (uu____11815)::[])
in ((f), (uu____11813)))
in FStar_Syntax_Syntax.Tm_app (uu____11803))
in (FStar_Syntax_Syntax.mk uu____11802))
in (uu____11799 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _0_70 -> FStar_TypeChecker_Common.NonTrivial (_0_70)) uu____11798))
in {FStar_TypeChecker_Env.guard_f = uu____11797; FStar_TypeChecker_Env.deferred = uu___168_11796.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___168_11796.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___168_11796.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____11828) -> begin
(failwith "impossible")
end))


let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let uu____11838 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (uu____11838))
end))


let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____11847 -> begin
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

let uu____11878 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = uu____11878; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (((FStar_List.append (Prims.fst g1.FStar_TypeChecker_Env.univ_ineqs) (Prims.fst g2.FStar_TypeChecker_Env.univ_ineqs))), ((FStar_List.append (Prims.snd g1.FStar_TypeChecker_Env.univ_ineqs) (Prims.snd g2.FStar_TypeChecker_Env.univ_ineqs)))); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___169_11916 = g
in (

let uu____11917 = (

let uu____11918 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right uu____11918 (fun _0_71 -> FStar_TypeChecker_Common.NonTrivial (_0_71))))
in {FStar_TypeChecker_Env.guard_f = uu____11917; FStar_TypeChecker_Env.deferred = uu___169_11916.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___169_11916.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___169_11916.FStar_TypeChecker_Env.implicits}))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = (

let uu____11956 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____11956) with
| true -> begin
(

let uu____11957 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____11958 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____11957 (rel_to_string rel) uu____11958)))
end
| uu____11959 -> begin
"TOP"
end))
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (

let uu____11978 = (

let uu____11980 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_72 -> Some (_0_72)) uu____11980))
in (FStar_Syntax_Syntax.new_bv uu____11978 t1))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (

let uu____11986 = (

let uu____11988 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _0_73 -> Some (_0_73)) uu____11988))
in (

let uu____11990 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 uu____11986 uu____11990)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (

let probs = (

let uu____12013 = (FStar_Options.eager_inference ())
in (match (uu____12013) with
| true -> begin
(

let uu___170_12014 = probs
in {attempting = uu___170_12014.attempting; wl_deferred = uu___170_12014.wl_deferred; ctr = uu___170_12014.ctr; defer_ok = false; smt_ok = uu___170_12014.smt_ok; tcenv = uu___170_12014.tcenv})
end
| uu____12015 -> begin
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

let uu____12025 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____12025) with
| true -> begin
(

let uu____12026 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____12026))
end
| uu____12027 -> begin
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

let uu____12036 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____12036) with
| true -> begin
(

let uu____12037 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____12037))
end
| uu____12038 -> begin
()
end));
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in ((

let uu____12041 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____12041) with
| true -> begin
(

let uu____12042 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____12042))
end
| uu____12043 -> begin
()
end));
(

let f = (

let uu____12045 = (

let uu____12046 = (FStar_Syntax_Util.unmeta f)
in uu____12046.FStar_Syntax_Syntax.n)
in (match (uu____12045) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____12050 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end))
in (

let uu___171_12051 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = uu___171_12051.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___171_12051.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___171_12051.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(

let uu____12066 = (

let uu____12067 = (

let uu____12068 = (

let uu____12069 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right uu____12069 (fun _0_74 -> FStar_TypeChecker_Common.NonTrivial (_0_74))))
in {FStar_TypeChecker_Env.guard_f = uu____12068; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env uu____12067))
in (FStar_All.pipe_left (fun _0_75 -> Some (_0_75)) uu____12066))
end))


let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> ((

let uu____12093 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12093) with
| true -> begin
(

let uu____12094 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12095 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" uu____12094 uu____12095)))
end
| uu____12096 -> begin
()
end));
(

let prob = (

let uu____12098 = (

let uu____12101 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None uu____12101))
in (FStar_All.pipe_left (fun _0_76 -> FStar_TypeChecker_Common.TProb (_0_76)) uu____12098))
in (

let g = (

let uu____12106 = (

let uu____12108 = (singleton env prob)
in (solve_and_commit env uu____12108 (fun uu____12109 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12106))
in g));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____12123 = (try_teq env t1 t2)
in (match (uu____12123) with
| None -> begin
(

let uu____12125 = (

let uu____12126 = (

let uu____12129 = (FStar_TypeChecker_Err.basic_type_error env None t2 t1)
in (

let uu____12130 = (FStar_TypeChecker_Env.get_range env)
in ((uu____12129), (uu____12130))))
in FStar_Errors.Error (uu____12126))
in (Prims.raise uu____12125))
end
| Some (g) -> begin
((

let uu____12133 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12133) with
| true -> begin
(

let uu____12134 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12135 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____12136 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____12134 uu____12135 uu____12136))))
end
| uu____12137 -> begin
()
end));
g;
)
end)))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 smt_ok -> ((

let uu____12152 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12152) with
| true -> begin
(

let uu____12153 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____12154 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" uu____12153 uu____12154)))
end
| uu____12155 -> begin
()
end));
(

let uu____12156 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____12156) with
| (prob, x) -> begin
(

let g = (

let uu____12164 = (

let uu____12166 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____12166 (fun uu____12167 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12164))
in ((

let uu____12173 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____12173) with
| true -> begin
(

let uu____12174 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____12175 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____12176 = (

let uu____12177 = (FStar_Util.must g)
in (guard_to_string env uu____12177))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" uu____12174 uu____12175 uu____12176))))
end
| uu____12178 -> begin
()
end));
(abstract_guard x g);
))
end));
))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env e t1 t2 -> (

let uu____12201 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12202 = (FStar_TypeChecker_Err.basic_type_error env (Some (e)) t2 t1)
in (FStar_Errors.report uu____12201 uu____12202))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> ((

let uu____12214 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12214) with
| true -> begin
(

let uu____12215 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____12216 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" uu____12215 uu____12216)))
end
| uu____12217 -> begin
()
end));
(

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____12219 -> begin
FStar_TypeChecker_Common.SUB
end)
in (

let prob = (

let uu____12221 = (

let uu____12224 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None uu____12224 "sub_comp"))
in (FStar_All.pipe_left (fun _0_77 -> FStar_TypeChecker_Common.CProb (_0_77)) uu____12221))
in (

let uu____12227 = (

let uu____12229 = (singleton env prob)
in (solve_and_commit env uu____12229 (fun uu____12230 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12227))));
))


let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun tx env uu____12249 -> (match (uu____12249) with
| (variables, ineqs) -> begin
(

let fail = (fun u1 u2 -> ((FStar_Unionfind.rollback tx);
(

let uu____12274 = (

let uu____12275 = (

let uu____12278 = (

let uu____12279 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____12280 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Universe %s and %s are incompatible" uu____12279 uu____12280)))
in (

let uu____12281 = (FStar_TypeChecker_Env.get_range env)
in ((uu____12278), (uu____12281))))
in FStar_Errors.Error (uu____12275))
in (Prims.raise uu____12274));
))
in (

let equiv = (fun v v' -> (

let uu____12289 = (

let uu____12292 = (FStar_Syntax_Subst.compress_univ v)
in (

let uu____12293 = (FStar_Syntax_Subst.compress_univ v')
in ((uu____12292), (uu____12293))))
in (match (uu____12289) with
| (FStar_Syntax_Syntax.U_unif (v0), FStar_Syntax_Syntax.U_unif (v0')) -> begin
(FStar_Unionfind.equivalent v0 v0')
end
| uu____12301 -> begin
false
end)))
in (

let sols = (FStar_All.pipe_right variables (FStar_List.collect (fun v -> (

let uu____12315 = (FStar_Syntax_Subst.compress_univ v)
in (match (uu____12315) with
| FStar_Syntax_Syntax.U_unif (uu____12319) -> begin
(

let lower_bounds_of_v = (FStar_All.pipe_right ineqs (FStar_List.collect (fun uu____12330 -> (match (uu____12330) with
| (u, v') -> begin
(

let uu____12336 = (equiv v v')
in (match (uu____12336) with
| true -> begin
(

let uu____12338 = (FStar_All.pipe_right variables (FStar_Util.for_some (equiv u)))
in (match (uu____12338) with
| true -> begin
[]
end
| uu____12341 -> begin
(u)::[]
end))
end
| uu____12342 -> begin
[]
end))
end))))
in (

let lb = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max (lower_bounds_of_v)))
in (((lb), (v)))::[]))
end
| uu____12348 -> begin
[]
end)))))
in (

let uu____12351 = (

let wl = (

let uu___172_12354 = (empty_worklist env)
in {attempting = uu___172_12354.attempting; wl_deferred = uu___172_12354.wl_deferred; ctr = uu___172_12354.ctr; defer_ok = false; smt_ok = uu___172_12354.smt_ok; tcenv = uu___172_12354.tcenv})
in (FStar_All.pipe_right sols (FStar_List.map (fun uu____12361 -> (match (uu____12361) with
| (lb, v) -> begin
(

let uu____12366 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl lb v)
in (match (uu____12366) with
| USolved (wl) -> begin
()
end
| uu____12368 -> begin
(fail lb v)
end))
end)))))
in (

let rec check_ineq = (fun uu____12374 -> (match (uu____12374) with
| (u, v) -> begin
(

let u = (FStar_TypeChecker_Normalize.normalize_universe env u)
in (

let v = (FStar_TypeChecker_Normalize.normalize_universe env v)
in (match (((u), (v))) with
| (FStar_Syntax_Syntax.U_zero, uu____12381) -> begin
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
| (FStar_Syntax_Syntax.U_max (us), uu____12397) -> begin
(FStar_All.pipe_right us (FStar_Util.for_all (fun u -> (check_ineq ((u), (v))))))
end
| (uu____12401, FStar_Syntax_Syntax.U_max (vs)) -> begin
(FStar_All.pipe_right vs (FStar_Util.for_some (fun v -> (check_ineq ((u), (v))))))
end
| uu____12406 -> begin
false
end)))
end))
in (

let uu____12409 = (FStar_All.pipe_right ineqs (FStar_Util.for_all (fun uu____12415 -> (match (uu____12415) with
| (u, v) -> begin
(

let uu____12420 = (check_ineq ((u), (v)))
in (match (uu____12420) with
| true -> begin
true
end
| uu____12421 -> begin
((

let uu____12423 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____12423) with
| true -> begin
(

let uu____12424 = (FStar_Syntax_Print.univ_to_string u)
in (

let uu____12425 = (FStar_Syntax_Print.univ_to_string v)
in (FStar_Util.print2 "%s </= %s" uu____12424 uu____12425)))
end
| uu____12426 -> begin
()
end));
false;
)
end))
end))))
in (match (uu____12409) with
| true -> begin
()
end
| uu____12427 -> begin
((

let uu____12429 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____12429) with
| true -> begin
((

let uu____12431 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Partially solved inequality constraints are: %s\n" uu____12431));
(FStar_Unionfind.rollback tx);
(

let uu____12437 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Original solved inequality constraints are: %s\n" uu____12437));
)
end
| uu____12442 -> begin
()
end));
(

let uu____12443 = (

let uu____12444 = (

let uu____12447 = (FStar_TypeChecker_Env.get_range env)
in (("Failed to solve universe inequalities for inductives"), (uu____12447)))
in FStar_Errors.Error (uu____12444))
in (Prims.raise uu____12443));
)
end)))))))
end))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun env ineqs -> (

let tx = (FStar_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Unionfind.commit tx);
)))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail = (fun uu____12480 -> (match (uu____12480) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Errors.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in ((

let uu____12490 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____12490) with
| true -> begin
(

let uu____12491 = (wl_to_string wl)
in (

let uu____12492 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" uu____12491 uu____12492)))
end
| uu____12502 -> begin
()
end));
(

let g = (

let uu____12504 = (solve_and_commit env wl fail)
in (match (uu____12504) with
| Some ([]) -> begin
(

let uu___173_12511 = g
in {FStar_TypeChecker_Env.guard_f = uu___173_12511.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu___173_12511.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___173_12511.FStar_TypeChecker_Env.implicits})
end
| uu____12514 -> begin
(failwith "impossible: Unexpected deferred constraints remain")
end))
in ((solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___174_12517 = g
in {FStar_TypeChecker_Env.guard_f = uu___174_12517.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___174_12517.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = uu___174_12517.FStar_TypeChecker_Env.implicits});
));
))))


let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun use_env_range_msg env g use_smt -> (

let g = (solve_deferred_constraints env g)
in (

let ret_g = (

let uu___175_12543 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___175_12543.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___175_12543.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___175_12543.FStar_TypeChecker_Env.implicits})
in (

let uu____12544 = (

let uu____12545 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12545)))
in (match (uu____12544) with
| true -> begin
Some (ret_g)
end
| uu____12547 -> begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((

let uu____12551 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Norm")))
in (match (uu____12551) with
| true -> begin
(

let uu____12552 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12553 = (

let uu____12554 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____12554))
in (FStar_Errors.diag uu____12552 uu____12553)))
end
| uu____12555 -> begin
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
| uu____12560 -> begin
((

let uu____12563 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12563) with
| true -> begin
(

let uu____12564 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12565 = (

let uu____12566 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____12566))
in (FStar_Errors.diag uu____12564 uu____12565)))
end
| uu____12567 -> begin
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

let uu____12574 = (discharge_guard' None env g true)
in (match (uu____12574) with
| Some (g) -> begin
g
end
| None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end)))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (

let uu____12594 = (FStar_Unionfind.find u)
in (match (uu____12594) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| uu____12603 -> begin
false
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____12618 = acc
in (match (uu____12618) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____12629 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd)::tl -> begin
(

let uu____12664 = hd
in (match (uu____12664) with
| (uu____12671, env, u, tm, k, r) -> begin
(

let uu____12677 = (unresolved u)
in (match (uu____12677) with
| true -> begin
(until_fixpoint (((hd)::out), (changed)) tl)
end
| uu____12691 -> begin
(

let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in ((

let uu____12695 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____12695) with
| true -> begin
(

let uu____12696 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____12700 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____12701 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" uu____12696 uu____12700 uu____12701))))
end
| uu____12702 -> begin
()
end));
(

let uu____12703 = (env.FStar_TypeChecker_Env.type_of (

let uu___176_12707 = env
in {FStar_TypeChecker_Env.solver = uu___176_12707.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___176_12707.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___176_12707.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___176_12707.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___176_12707.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___176_12707.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___176_12707.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___176_12707.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___176_12707.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___176_12707.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___176_12707.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___176_12707.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___176_12707.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___176_12707.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___176_12707.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___176_12707.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___176_12707.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___176_12707.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___176_12707.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___176_12707.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___176_12707.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___176_12707.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___176_12707.FStar_TypeChecker_Env.qname_and_index}) tm)
in (match (uu____12703) with
| (uu____12708, uu____12709, g) -> begin
(

let g = (match (env.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___177_12712 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___177_12712.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___177_12712.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___177_12712.FStar_TypeChecker_Env.implicits})
end
| uu____12713 -> begin
g
end)
in (

let g' = (

let uu____12715 = (discharge_guard' (Some ((fun uu____12719 -> (FStar_Syntax_Print.term_to_string tm)))) env g true)
in (match (uu____12715) with
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

let uu___178_12734 = g
in (

let uu____12735 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___178_12734.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___178_12734.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___178_12734.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____12735})))))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g = (

let uu____12763 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____12763 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(

let uu____12770 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore uu____12770))
end
| ((reason, uu____12772, uu____12773, e, t, r))::uu____12777 -> begin
(

let uu____12791 = (

let uu____12792 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____12793 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" uu____12792 uu____12793 reason)))
in (FStar_Errors.report r uu____12791))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___179_12800 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___179_12800.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___179_12800.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ((((u1), (u2)))::[])); FStar_TypeChecker_Env.implicits = uu___179_12800.FStar_TypeChecker_Env.implicits}))


let teq_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____12818 = (try_teq env t1 t2)
in (match (uu____12818) with
| None -> begin
false
end
| Some (g) -> begin
(

let uu____12821 = (discharge_guard' None env g false)
in (match (uu____12821) with
| Some (uu____12825) -> begin
true
end
| None -> begin
false
end))
end)))





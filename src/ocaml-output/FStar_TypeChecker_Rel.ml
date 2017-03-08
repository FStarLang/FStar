
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


let mk_eq2 : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t1 t2 -> (

let uu____113 = (FStar_Syntax_Util.type_u ())
in (match (uu____113) with
| (t_type, u) -> begin
(

let uu____118 = (

let uu____121 = (FStar_TypeChecker_Env.all_binders env)
in (new_uvar t1.FStar_Syntax_Syntax.pos uu____121 t_type))
in (match (uu____118) with
| (tt, uu____123) -> begin
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
| uu____144 -> begin
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
| uu____170 -> begin
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
| uu____250 -> begin
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
| uu____264 -> begin
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
| uu____281 -> begin
false
end))


let uu___is_CONTRAVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CONTRAVARIANT -> begin
true
end
| uu____285 -> begin
false
end))


let uu___is_INVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| INVARIANT -> begin
true
end
| uu____289 -> begin
false
end))


type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem


type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem


type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun uu___99_300 -> (match (uu___99_300) with
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

let uu____313 = (

let uu____314 = (FStar_Syntax_Subst.compress t)
in uu____314.FStar_Syntax_Syntax.n)
in (match (uu____313) with
| FStar_Syntax_Syntax.Tm_uvar (u, t) -> begin
(

let uu____331 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____335 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "(%s:%s)" uu____331 uu____335)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty); FStar_Syntax_Syntax.tk = uu____338; FStar_Syntax_Syntax.pos = uu____339; FStar_Syntax_Syntax.vars = uu____340}, args) -> begin
(

let uu____368 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____372 = (FStar_Syntax_Print.term_to_string ty)
in (

let uu____373 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "(%s:%s) %s" uu____368 uu____372 uu____373))))
end
| uu____374 -> begin
(FStar_Syntax_Print.term_to_string t)
end)))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env uu___100_380 -> (match (uu___100_380) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____384 = (

let uu____386 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____387 = (

let uu____389 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____390 = (

let uu____392 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (

let uu____393 = (

let uu____395 = (

let uu____397 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (

let uu____398 = (

let uu____400 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (

let uu____401 = (

let uu____403 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (

let uu____404 = (

let uu____406 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (uu____406)::[])
in (uu____403)::uu____404))
in (uu____400)::uu____401))
in (uu____397)::uu____398))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::uu____395)
in (uu____392)::uu____393))
in (uu____389)::uu____390))
in (uu____386)::uu____387))
in (FStar_Util.format "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" uu____384))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____411 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (

let uu____412 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____411 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____412)))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env uu___101_418 -> (match (uu___101_418) with
| UNIV (u, t) -> begin
(

let x = (

let uu____422 = (FStar_Options.hide_uvar_nums ())
in (match (uu____422) with
| true -> begin
"?"
end
| uu____423 -> begin
(

let uu____424 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____424 FStar_Util.string_of_int))
end))
in (

let uu____426 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x uu____426)))
end
| TERM ((u, uu____428), t) -> begin
(

let x = (

let uu____433 = (FStar_Options.hide_uvar_nums ())
in (match (uu____433) with
| true -> begin
"?"
end
| uu____434 -> begin
(

let uu____435 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____435 FStar_Util.string_of_int))
end))
in (

let uu____439 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x uu____439)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (

let uu____448 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right uu____448 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (

let uu____456 = (

let uu____458 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right uu____458 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right uu____456 (FStar_String.concat ", "))))


let args_to_string = (fun args -> (

let uu____476 = (FStar_All.pipe_right args (FStar_List.map (fun uu____484 -> (match (uu____484) with
| (x, uu____488) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____476 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> (

let uu____493 = (

let uu____494 = (FStar_Options.eager_inference ())
in (not (uu____494)))
in {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = uu____493; smt_ok = true; tcenv = env}))


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let uu___127_507 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = uu___127_507.wl_deferred; ctr = uu___127_507.ctr; defer_ok = uu___127_507.defer_ok; smt_ok = smt_ok; tcenv = uu___127_507.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard = (fun env g -> (

let uu___128_532 = (empty_worklist env)
in (

let uu____533 = (FStar_List.map Prims.snd g)
in {attempting = uu____533; wl_deferred = uu___128_532.wl_deferred; ctr = uu___128_532.ctr; defer_ok = false; smt_ok = uu___128_532.smt_ok; tcenv = uu___128_532.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu___129_545 = wl
in {attempting = uu___129_545.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = uu___129_545.ctr; defer_ok = uu___129_545.defer_ok; smt_ok = uu___129_545.smt_ok; tcenv = uu___129_545.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let uu___130_557 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = uu___130_557.wl_deferred; ctr = uu___130_557.ctr; defer_ok = uu___130_557.defer_ok; smt_ok = uu___130_557.smt_ok; tcenv = uu___130_557.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> ((

let uu____568 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____568) with
| true -> begin
(

let uu____569 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason uu____569))
end
| uu____570 -> begin
()
end));
Failed (((prob), (reason)));
))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun uu___102_573 -> (match (uu___102_573) with
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

let uu___131_589 = p
in {FStar_TypeChecker_Common.pid = uu___131_589.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = uu___131_589.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___131_589.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___131_589.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___131_589.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___131_589.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___131_589.FStar_TypeChecker_Common.rank}))


let maybe_invert = (fun p -> (match ((p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV)) with
| true -> begin
(invert p)
end
| uu____607 -> begin
p
end))


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___103_610 -> (match (uu___103_610) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_28 -> FStar_TypeChecker_Common.TProb (_0_28)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_29 -> FStar_TypeChecker_Common.CProb (_0_29)))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel uu___104_626 -> (match (uu___104_626) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun uu___105_629 -> (match (uu___105_629) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun uu___106_638 -> (match (uu___106_638) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun uu___107_648 -> (match (uu___107_648) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun uu___108_658 -> (match (uu___108_658) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun uu___109_669 -> (match (uu___109_669) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun uu___110_680 -> (match (uu___110_680) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___111_689 -> (match (uu___111_689) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _0_30 -> FStar_TypeChecker_Common.TProb (_0_30)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _0_31 -> FStar_TypeChecker_Common.CProb (_0_31)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> (

let uu____703 = (FStar_All.pipe_right (p_reason p) FStar_List.length)
in (uu____703 = (Prims.parse_int "1"))))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____714 -> ((FStar_Util.incr ctr);
(FStar_ST.read ctr);
)))


let mk_problem = (fun scope orig lhs rel rhs elt reason -> (

let uu____764 = (next_pid ())
in (

let uu____765 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____764; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____765; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))


let new_problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (

let uu____812 = (next_pid ())
in (

let uu____813 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = uu____812; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = uu____813; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (

let uu____854 = (next_pid ())
in {FStar_TypeChecker_Common.pid = uu____854; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))


let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (

let uu____900 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____900) with
| true -> begin
(

let uu____901 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (

let uu____902 = (prob_to_string env d)
in (

let uu____903 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" uu____901 uu____902 uu____903 s))))
end
| uu____905 -> begin
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
| uu____908 -> begin
(failwith "impossible")
end)
in (

let uu____909 = (match (d) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____917 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (

let uu____918 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((uu____917), (uu____918))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____922 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (

let uu____923 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((uu____922), (uu____923))))
end)
in (match (uu____909) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___112_932 -> (match (uu___112_932) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| uu____939 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, uu____942), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun uu___113_965 -> (match (uu___113_965) with
| UNIV (uu____967) -> begin
None
end
| TERM ((u, uu____971), t) -> begin
(

let uu____975 = (FStar_Unionfind.equivalent uv u)
in (match (uu____975) with
| true -> begin
Some (t)
end
| uu____980 -> begin
None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun uu___114_994 -> (match (uu___114_994) with
| UNIV (u', t) -> begin
(

let uu____998 = (FStar_Unionfind.equivalent u u')
in (match (uu____998) with
| true -> begin
Some (t)
end
| uu____1001 -> begin
None
end))
end
| uu____1002 -> begin
None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1009 = (

let uu____1010 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____1010))
in (FStar_Syntax_Subst.compress uu____1009)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1017 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress uu____1017)))


let norm_arg = (fun env t -> (

let uu____1036 = (sn env (Prims.fst t))
in ((uu____1036), ((Prims.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____1053 -> (match (uu____1053) with
| (x, imp) -> begin
(

let uu____1060 = (

let uu___132_1061 = x
in (

let uu____1062 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___132_1061.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___132_1061.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1062}))
in ((uu____1060), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(

let uu____1077 = (aux u)
in FStar_Syntax_Syntax.U_succ (uu____1077))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1080 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____1080))
end
| uu____1082 -> begin
u
end)))
in (

let uu____1083 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1083))))


let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement = (fun env wl t1 -> (

let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(match (norm) with
| true -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| uu____1189 -> begin
(

let uu____1190 = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (match (uu____1190) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = uu____1202; FStar_Syntax_Syntax.pos = uu____1203; FStar_Syntax_Syntax.vars = uu____1204} -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| tt -> begin
(

let uu____1225 = (

let uu____1226 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____1227 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1226 uu____1227)))
in (failwith uu____1225))
end))
end)
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(match (norm) with
| true -> begin
((t1), (None))
end
| uu____1260 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (

let uu____1262 = (

let uu____1263 = (FStar_Syntax_Subst.compress t1')
in uu____1263.FStar_Syntax_Syntax.n)
in (match (uu____1262) with
| FStar_Syntax_Syntax.Tm_refine (uu____1275) -> begin
(aux true t1')
end
| uu____1280 -> begin
((t1), (None))
end)))
end)
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
((t1), (None))
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(

let uu____1315 = (

let uu____1316 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1317 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1316 uu____1317)))
in (failwith uu____1315))
end))
in (

let uu____1327 = (whnf env t1)
in (aux false uu____1327))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____1336 = (

let uu____1346 = (empty_worklist env)
in (base_and_refinement env uu____1346 t))
in (FStar_All.pipe_right uu____1336 Prims.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (

let uu____1370 = (FStar_Syntax_Syntax.null_bv t)
in ((uu____1370), (FStar_Syntax_Util.t_true))))


let as_refinement = (fun env wl t -> (

let uu____1390 = (base_and_refinement env wl t)
in (match (uu____1390) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement = (fun uu____1449 -> (match (uu____1449) with
| (t_base, refopt) -> begin
(

let uu____1463 = (match (refopt) with
| Some (y, phi) -> begin
((y), (phi))
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (uu____1463) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl uu___115_1487 -> (match (uu___115_1487) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____1491 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1492 = (

let uu____1493 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string uu____1493))
in (

let uu____1494 = (

let uu____1495 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string uu____1495))
in (FStar_Util.format4 "%s: %s  (%s)  %s" uu____1491 uu____1492 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1494))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(

let uu____1499 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (

let uu____1500 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____1501 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" uu____1499 uu____1500 (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1501))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (

let uu____1505 = (

let uu____1507 = (

let uu____1509 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____1519 -> (match (uu____1519) with
| (uu____1523, uu____1524, x) -> begin
x
end))))
in (FStar_List.append wl.attempting uu____1509))
in (FStar_List.map (wl_prob_to_string wl) uu____1507))
in (FStar_All.pipe_right uu____1505 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____1542 = (

let uu____1552 = (

let uu____1553 = (FStar_Syntax_Subst.compress k)
in uu____1553.FStar_Syntax_Syntax.n)
in (match (uu____1552) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (((FStar_List.length bs) = (FStar_List.length ys))) with
| true -> begin
(

let uu____1594 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (uu____1594)))
end
| uu____1607 -> begin
(

let uu____1608 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____1608) with
| (ys', t, uu____1629) -> begin
(

let uu____1642 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t))), (uu____1642)))
end))
end)
end
| uu____1663 -> begin
(

let uu____1664 = (

let uu____1670 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____1670)))
in ((((ys), (t))), (uu____1664)))
end))
in (match (uu____1542) with
| ((ys, t), (xs, c)) -> begin
(match (((FStar_List.length xs) <> (FStar_List.length ys))) with
| true -> begin
(FStar_Syntax_Util.abs ys t (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ([]))))))
end
| uu____1723 -> begin
(

let c = (

let uu____1725 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp uu____1725 c))
in (

let uu____1727 = (

let uu____1734 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_32 -> FStar_Util.Inl (_0_32)))
in (FStar_All.pipe_right uu____1734 (fun _0_33 -> Some (_0_33))))
in (FStar_Syntax_Util.abs ys t uu____1727)))
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

let uu____1785 = (p_guard prob)
in (match (uu____1785) with
| (uu____1788, uv) -> begin
((

let uu____1791 = (

let uu____1792 = (FStar_Syntax_Subst.compress uv)
in uu____1792.FStar_Syntax_Syntax.n)
in (match (uu____1791) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi = (u_abs k bs phi)
in ((

let uu____1812 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____1812) with
| true -> begin
(

let uu____1813 = (FStar_Util.string_of_int (p_pid prob))
in (

let uu____1814 = (FStar_Syntax_Print.term_to_string uv)
in (

let uu____1815 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" uu____1813 uu____1814 uu____1815))))
end
| uu____1816 -> begin
()
end));
(FStar_Syntax_Util.set_uvar uvar phi);
)))
end
| uu____1819 -> begin
(match ((not (resolve_ok))) with
| true -> begin
(failwith "Impossible: this instance has already been assigned a solution")
end
| uu____1820 -> begin
()
end)
end));
(commit uvis);
(

let uu___133_1822 = wl
in {attempting = uu___133_1822.attempting; wl_deferred = uu___133_1822.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___133_1822.defer_ok; smt_ok = uu___133_1822.smt_ok; tcenv = uu___133_1822.tcenv});
)
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____1835 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____1835) with
| true -> begin
(

let uu____1836 = (FStar_Util.string_of_int pid)
in (

let uu____1837 = (

let uu____1838 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right uu____1838 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____1836 uu____1837)))
end
| uu____1841 -> begin
()
end));
(commit sol);
(

let uu___134_1843 = wl
in {attempting = uu___134_1843.attempting; wl_deferred = uu___134_1843.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___134_1843.defer_ok; smt_ok = uu___134_1843.smt_ok; tcenv = uu___134_1843.tcenv});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard = (fun t g -> (match (((t), (g))) with
| (uu____1872, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(

let uu____1880 = (FStar_Syntax_Util.mk_conj t f)
in Some (uu____1880))
end))
in ((

let uu____1886 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____1886) with
| true -> begin
(

let uu____1887 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (

let uu____1888 = (

let uu____1889 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right uu____1889 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" uu____1887 uu____1888)))
end
| uu____1892 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
)))


let rec occurs = (fun wl uk t -> (

let uu____1914 = (

let uu____1918 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right uu____1918 FStar_Util.set_elements))
in (FStar_All.pipe_right uu____1914 (FStar_Util.for_some (fun uu____1939 -> (match (uu____1939) with
| (uv, uu____1947) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (

let uu____1991 = (occurs wl uk t)
in (not (uu____1991)))
in (

let msg = (match (occurs_ok) with
| true -> begin
None
end
| uu____1995 -> begin
(

let uu____1996 = (

let uu____1997 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (

let uu____2001 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" uu____1997 uu____2001)))
in Some (uu____1996))
end)
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let uu____2049 = (occurs_check env wl uk t)
in (match (uu____2049) with
| (occurs_ok, msg) -> begin
(

let uu____2066 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (uu____2066), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set v1)
in (

let uu____2130 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____2154 uu____2155 -> (match (((uu____2154), (uu____2155))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____2198 = (

let uu____2199 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation uu____2199))
in (match (uu____2198) with
| true -> begin
((isect), (isect_set))
end
| uu____2210 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____2213 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____2213) with
| true -> begin
(

let uu____2220 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (uu____2220)))
end
| uu____2228 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (uu____2130) with
| (isect, uu____2242) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____2291 uu____2292 -> (match (((uu____2291), (uu____2292))) with
| ((a, uu____2302), (b, uu____2304)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(

let uu____2348 = (FStar_All.pipe_right seen (FStar_Util.for_some (fun uu____2354 -> (match (uu____2354) with
| (b, uu____2358) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end))))
in (match (uu____2348) with
| true -> begin
None
end
| uu____2364 -> begin
Some (((a), ((Prims.snd hd))))
end))
end
| uu____2367 -> begin
None
end)))


let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| (hd)::rest -> begin
(

let uu____2410 = (pat_var_opt env seen hd)
in (match (uu____2410) with
| None -> begin
((

let uu____2418 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____2418) with
| true -> begin
(

let uu____2419 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" uu____2419))
end
| uu____2420 -> begin
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

let uu____2431 = (

let uu____2432 = (FStar_Syntax_Subst.compress t)
in uu____2432.FStar_Syntax_Syntax.n)
in (match (uu____2431) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
true
end
| uu____2448 -> begin
false
end)))


let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = uu____2510; FStar_Syntax_Syntax.pos = uu____2511; FStar_Syntax_Syntax.vars = uu____2512}, args) -> begin
((t), (uv), (k), (args))
end
| uu____2553 -> begin
(failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let uu____2607 = (destruct_flex_t t)
in (match (uu____2607) with
| (t, uv, k, args) -> begin
(

let uu____2675 = (pat_vars env [] args)
in (match (uu____2675) with
| Some (vars) -> begin
((((t), (uv), (k), (args))), (Some (vars)))
end
| uu____2731 -> begin
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
| uu____2779 -> begin
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
| uu____2802 -> begin
false
end))


let uu___is_FullMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullMatch -> begin
true
end
| uu____2806 -> begin
false
end))


let head_match : match_result  ->  match_result = (fun uu___116_2809 -> (match (uu___116_2809) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____2818 -> begin
HeadMatch
end))


let fv_delta_depth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.delta_depth = (fun env fv -> (match (fv.FStar_Syntax_Syntax.fv_delta) with
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(match ((env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)) with
| true -> begin
d
end
| uu____2830 -> begin
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
| uu____2903 -> begin
MisMatch (((None), (None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____2908 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____2908) with
| true -> begin
FullMatch
end
| uu____2909 -> begin
MisMatch (((Some ((fv_delta_depth env f))), (Some ((fv_delta_depth env g)))))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____2913), FStar_Syntax_Syntax.Tm_uinst (g, uu____2915)) -> begin
(

let uu____2924 = (head_matches env f g)
in (FStar_All.pipe_right uu____2924 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(match ((c = d)) with
| true -> begin
FullMatch
end
| uu____2927 -> begin
MisMatch (((None), (None)))
end)
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, uu____2931), FStar_Syntax_Syntax.Tm_uvar (uv', uu____2933)) -> begin
(

let uu____2958 = (FStar_Unionfind.equivalent uv uv')
in (match (uu____2958) with
| true -> begin
FullMatch
end
| uu____2962 -> begin
MisMatch (((None), (None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____2966), FStar_Syntax_Syntax.Tm_refine (y, uu____2968)) -> begin
(

let uu____2977 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____2977 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____2979), uu____2980) -> begin
(

let uu____2985 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right uu____2985 head_match))
end
| (uu____2986, FStar_Syntax_Syntax.Tm_refine (x, uu____2988)) -> begin
(

let uu____2993 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____2993 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, uu____2999), FStar_Syntax_Syntax.Tm_app (head', uu____3001)) -> begin
(

let uu____3030 = (head_matches env head head')
in (FStar_All.pipe_right uu____3030 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head, uu____3032), uu____3033) -> begin
(

let uu____3048 = (head_matches env head t2)
in (FStar_All.pipe_right uu____3048 head_match))
end
| (uu____3049, FStar_Syntax_Syntax.Tm_app (head, uu____3051)) -> begin
(

let uu____3066 = (head_matches env t1 head)
in (FStar_All.pipe_right uu____3066 head_match))
end
| uu____3067 -> begin
(

let uu____3070 = (

let uu____3075 = (delta_depth_of_term env t1)
in (

let uu____3077 = (delta_depth_of_term env t2)
in ((uu____3075), (uu____3077))))
in MisMatch (uu____3070))
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let uu____3113 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____3113) with
| (head, uu____3125) -> begin
(

let uu____3140 = (

let uu____3141 = (FStar_Syntax_Util.un_uinst head)
in uu____3141.FStar_Syntax_Syntax.n)
in (match (uu____3140) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3146 = (

let uu____3147 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3147 FStar_Option.isSome))
in (match (uu____3146) with
| true -> begin
(

let uu____3161 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right uu____3161 (fun _0_34 -> Some (_0_34))))
end
| uu____3163 -> begin
None
end))
end
| uu____3164 -> begin
None
end))
end)))
in (

let success = (fun d r t1 t2 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
Some (((t1), (t2)))
end
| uu____3191 -> begin
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
| uu____3243 -> begin
(

let uu____3244 = (

let uu____3249 = (maybe_inline t1)
in (

let uu____3251 = (maybe_inline t2)
in ((uu____3249), (uu____3251))))
in (match (uu____3244) with
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

let uu____3276 = (FStar_TypeChecker_Common.decr_delta_depth d1)
in (match (uu____3276) with
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

let uu____3291 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in ((t1'), (t2)))
end
| uu____3297 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (

let uu____3299 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in ((t1), (uu____3299))))
end)
in (match (uu____3291) with
| (t1, t2) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t1 t2)
end)))
end
| MisMatch (uu____3307) -> begin
(fail r)
end
| uu____3312 -> begin
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
| uu____3337 -> begin
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
| uu____3367 -> begin
false
end))


let __proj__C__item___0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_0) -> begin
_0
end))


type tcs =
tc Prims.list


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____3382 = (FStar_Syntax_Util.type_u ())
in (match (uu____3382) with
| (t, uu____3386) -> begin
(

let uu____3387 = (new_uvar r binders t)
in (Prims.fst uu____3387))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____3396 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____3396 Prims.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (

let uu____3438 = (head_matches env t t')
in (match (uu____3438) with
| MisMatch (uu____3439) -> begin
false
end
| uu____3444 -> begin
true
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(

let rebuild = (fun args' -> (

let args = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((uu____3504, imp), T (t, uu____3507)) -> begin
((t), (imp))
end
| uu____3524 -> begin
(failwith "Bad reconstruction")
end)) args args')
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), (args))))) None t.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun uu____3568 -> (match (uu____3568) with
| (t, uu____3576) -> begin
((None), (INVARIANT), (T (((t), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let fail = (fun uu____3609 -> (failwith "Bad reconstruction"))
in (

let uu____3610 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3610) with
| (bs, c) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs tcs -> (match (((bs), (tcs))) with
| (((x, imp))::bs, (T (t, uu____3663))::tcs) -> begin
(aux (((((

let uu___135_3685 = x
in {FStar_Syntax_Syntax.ppname = uu___135_3685.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___135_3685.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp)))::out) bs tcs)
end
| ([], (C (c))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| uu____3695 -> begin
(failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (

let rec decompose = (fun out uu___117_3726 -> (match (uu___117_3726) with
| [] -> begin
(FStar_List.rev ((((None), (COVARIANT), (C (c))))::out))
end
| (hd)::rest -> begin
(decompose ((((Some (hd)), (CONTRAVARIANT), (T ((((Prims.fst hd).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (

let uu____3789 = (decompose [] bs)
in ((rebuild), (matches), (uu____3789)))))
end)))
end
| uu____3817 -> begin
(

let rebuild = (fun uu___118_3822 -> (match (uu___118_3822) with
| [] -> begin
t
end
| uu____3824 -> begin
(failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t -> true)), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun uu___119_3843 -> (match (uu___119_3843) with
| T (t, uu____3845) -> begin
t
end
| uu____3854 -> begin
(failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun uu___120_3857 -> (match (uu___120_3857) with
| T (t, uu____3859) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| uu____3868 -> begin
(failwith "Impossible")
end))


let imitation_sub_probs = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope args q -> (match (q) with
| (uu____3949, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope r)
in (

let uu____3968 = (new_uvar r scope k)
in (match (uu____3968) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| uu____3980 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) None r)
end)
in (

let uu____3995 = (

let uu____3996 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _0_35 -> FStar_TypeChecker_Common.TProb (_0_35)) uu____3996))
in ((T (((gi_xs), (mk_kind)))), (uu____3995))))
end)))
end
| (uu____4005, uu____4006, C (uu____4007)) -> begin
(failwith "impos")
end))
in (

let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs -> begin
(

let uu____4094 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.tk = uu____4105; FStar_Syntax_Syntax.pos = uu____4106; FStar_Syntax_Syntax.vars = uu____4107})) -> begin
(

let uu____4122 = (sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____4122) with
| (T (gi_xs, uu____4138), prob) -> begin
(

let uu____4148 = (

let uu____4149 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_36 -> C (_0_36)) uu____4149))
in ((uu____4148), ((prob)::[])))
end
| uu____4151 -> begin
(failwith "impossible")
end))
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.tk = uu____4161; FStar_Syntax_Syntax.pos = uu____4162; FStar_Syntax_Syntax.vars = uu____4163})) -> begin
(

let uu____4178 = (sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____4178) with
| (T (gi_xs, uu____4194), prob) -> begin
(

let uu____4204 = (

let uu____4205 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_37 -> C (_0_37)) uu____4205))
in ((uu____4204), ((prob)::[])))
end
| uu____4207 -> begin
(failwith "impossible")
end))
end
| (uu____4213, uu____4214, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = uu____4216; FStar_Syntax_Syntax.pos = uu____4217; FStar_Syntax_Syntax.vars = uu____4218})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((None), (INVARIANT), (T ((((Prims.fst t)), (generic_kind))))))))
in (

let components = (((None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let uu____4292 = (

let uu____4297 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right uu____4297 FStar_List.unzip))
in (match (uu____4292) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (

let uu____4326 = (

let uu____4327 = (

let uu____4330 = (FStar_List.hd tcs)
in (FStar_All.pipe_right uu____4330 un_T))
in (

let uu____4331 = (

let uu____4337 = (FStar_List.tl tcs)
in (FStar_All.pipe_right uu____4337 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____4327; FStar_Syntax_Syntax.effect_args = uu____4331; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____4326))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| uu____4342 -> begin
(

let uu____4349 = (sub_prob scope args q)
in (match (uu____4349) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (uu____4094) with
| (tc, probs) -> begin
(

let uu____4367 = (match (q) with
| (Some (b), uu____4393, uu____4394) -> begin
(

let uu____4402 = (

let uu____4406 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (uu____4406)::args)
in ((Some (b)), ((b)::scope), (uu____4402)))
end
| uu____4424 -> begin
((None), (scope), (args))
end)
in (match (uu____4367) with
| (bopt, scope, args) -> begin
(

let uu____4467 = (aux scope args qs)
in (match (uu____4467) with
| (sub_probs, tcs, f) -> begin
(

let f = (match (bopt) with
| None -> begin
(

let uu____4488 = (

let uu____4490 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::uu____4490)
in (FStar_Syntax_Util.mk_conj_l uu____4488))
end
| Some (b) -> begin
(

let uu____4502 = (

let uu____4504 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (

let uu____4505 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (uu____4504)::uu____4505))
in (FStar_Syntax_Util.mk_conj_l uu____4502))
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

let uu___136_4558 = p
in (

let uu____4561 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (

let uu____4562 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___136_4558.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____4561; FStar_TypeChecker_Common.relation = uu___136_4558.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____4562; FStar_TypeChecker_Common.element = uu___136_4558.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___136_4558.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___136_4558.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___136_4558.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___136_4558.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___136_4558.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(

let uu____4572 = (compress_tprob wl p)
in (FStar_All.pipe_right uu____4572 (fun _0_38 -> FStar_TypeChecker_Common.TProb (_0_38))))
end
| FStar_TypeChecker_Common.CProb (uu____4577) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (

let uu____4591 = (compress_prob wl pr)
in (FStar_All.pipe_right uu____4591 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____4597 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____4597) with
| (lh, uu____4610) -> begin
(

let uu____4625 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____4625) with
| (rh, uu____4638) -> begin
(

let uu____4653 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____4662), FStar_Syntax_Syntax.Tm_uvar (uu____4663)) -> begin
((flex_flex), (tp))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when ((tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____4688), uu____4689) -> begin
(

let uu____4698 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (uu____4698) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((flex_rigid), (tp))
end
| uu____4738 -> begin
(

let rank = (

let uu____4745 = (is_top_level_prob prob)
in (match (uu____4745) with
| true -> begin
flex_refine
end
| uu____4746 -> begin
flex_refine_inner
end))
in (

let uu____4747 = (

let uu___137_4750 = tp
in (

let uu____4753 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___137_4750.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___137_4750.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___137_4750.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____4753; FStar_TypeChecker_Common.element = uu___137_4750.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___137_4750.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___137_4750.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___137_4750.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___137_4750.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___137_4750.FStar_TypeChecker_Common.rank}))
in ((rank), (uu____4747))))
end)
end))
end
| (uu____4763, FStar_Syntax_Syntax.Tm_uvar (uu____4764)) -> begin
(

let uu____4773 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (uu____4773) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((rigid_flex), (tp))
end
| uu____4813 -> begin
(

let uu____4819 = (

let uu___138_4824 = tp
in (

let uu____4827 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___138_4824.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____4827; FStar_TypeChecker_Common.relation = uu___138_4824.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___138_4824.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___138_4824.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___138_4824.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___138_4824.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___138_4824.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___138_4824.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___138_4824.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (uu____4819)))
end)
end))
end
| (uu____4843, uu____4844) -> begin
((rigid_rigid), (tp))
end)
in (match (uu____4653) with
| (rank, tp) -> begin
(

let uu____4855 = (FStar_All.pipe_right (

let uu___139_4858 = tp
in {FStar_TypeChecker_Common.pid = uu___139_4858.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___139_4858.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___139_4858.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___139_4858.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___139_4858.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___139_4858.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___139_4858.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___139_4858.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___139_4858.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _0_39 -> FStar_TypeChecker_Common.TProb (_0_39)))
in ((rank), (uu____4855)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(

let uu____4864 = (FStar_All.pipe_right (

let uu___140_4867 = cp
in {FStar_TypeChecker_Common.pid = uu___140_4867.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___140_4867.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___140_4867.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___140_4867.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___140_4867.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___140_4867.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___140_4867.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___140_4867.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___140_4867.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _0_40 -> FStar_TypeChecker_Common.CProb (_0_40)))
in ((rigid_rigid), (uu____4864)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun uu____4899 probs -> (match (uu____4899) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
((min), (out), (min_rank))
end
| (hd)::tl -> begin
(

let uu____4929 = (rank wl hd)
in (match (uu____4929) with
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
| uu____4954 -> begin
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
| uu____4970 -> begin
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
| uu____4994 -> begin
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
| uu____5006 -> begin
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
| uu____5018 -> begin
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

let uu____5055 = (FStar_Syntax_Util.univ_kernel u)
in (match (uu____5055) with
| (k, uu____5059) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| uu____5064 -> begin
false
end)
end)))))
end
| uu____5065 -> begin
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

let uu____5108 = (really_solve_universe_eq pid_orig wl u1 u2)
in (match (uu____5108) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed -> begin
failed
end))
end
| uu____5111 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end
| uu____5116 -> begin
(

let uu____5117 = (

let uu____5118 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____5119 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" uu____5118 uu____5119)))
in UFailed (uu____5117))
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

let uu____5136 = (really_solve_universe_eq pid_orig wl u u')
in (match (uu____5136) with
| USolved (wl) -> begin
(aux wl us)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____5139 -> begin
(

let uu____5142 = (

let uu____5143 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____5144 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" uu____5143 uu____5144 msg)))
in UFailed (uu____5142))
end))
in (match (((u1), (u2))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(

let uu____5151 = (

let uu____5152 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____5153 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" uu____5152 uu____5153)))
in (failwith uu____5151))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((x.FStar_Ident.idText = y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____5156 -> begin
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

let uu____5165 = (FStar_Unionfind.equivalent v1 v2)
in (match (uu____5165) with
| true -> begin
USolved (wl)
end
| uu____5167 -> begin
(

let wl = (extend_solution pid_orig ((UNIV (((v1), (u2))))::[]) wl)
in USolved (wl))
end))
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(

let u = (norm_univ wl u)
in (

let uu____5178 = (occurs_univ v1 u)
in (match (uu____5178) with
| true -> begin
(

let uu____5179 = (

let uu____5180 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (

let uu____5181 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" uu____5180 uu____5181)))
in (try_umax_components u1 u2 uu____5179))
end
| uu____5182 -> begin
(

let uu____5183 = (extend_solution pid_orig ((UNIV (((v1), (u))))::[]) wl)
in USolved (uu____5183))
end)))
end
| ((FStar_Syntax_Syntax.U_max (_), _)) | ((_, FStar_Syntax_Syntax.U_max (_))) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____5190 -> begin
(

let u1 = (norm_univ wl u1)
in (

let u2 = (norm_univ wl u2)
in (

let uu____5193 = (FStar_Syntax_Util.eq_univs u1 u2)
in (match (uu____5193) with
| true -> begin
USolved (wl)
end
| uu____5194 -> begin
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
| uu____5215 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders = (fun bc1 bc2 -> (

let uu____5264 = bc1
in (match (uu____5264) with
| (bs1, mk_cod1) -> begin
(

let uu____5289 = bc2
in (match (uu____5289) with
| (bs2, mk_cod2) -> begin
(

let curry = (fun n bs mk_cod -> (

let uu____5336 = (FStar_Util.first_N n bs)
in (match (uu____5336) with
| (bs, rest) -> begin
(

let uu____5350 = (mk_cod rest)
in ((bs), (uu____5350)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(

let uu____5368 = (

let uu____5372 = (mk_cod1 [])
in ((bs1), (uu____5372)))
in (

let uu____5374 = (

let uu____5378 = (mk_cod2 [])
in ((bs2), (uu____5378)))
in ((uu____5368), (uu____5374))))
end
| uu____5386 -> begin
(match ((l1 > l2)) with
| true -> begin
(

let uu____5400 = (curry l2 bs1 mk_cod1)
in (

let uu____5407 = (

let uu____5411 = (mk_cod2 [])
in ((bs2), (uu____5411)))
in ((uu____5400), (uu____5407))))
end
| uu____5419 -> begin
(

let uu____5420 = (

let uu____5424 = (mk_cod1 [])
in ((bs1), (uu____5424)))
in (

let uu____5426 = (curry l1 bs2 mk_cod2)
in ((uu____5420), (uu____5426))))
end)
end))))
end))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____5530 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5530) with
| true -> begin
(

let uu____5531 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" uu____5531))
end
| uu____5532 -> begin
()
end));
(

let uu____5533 = (next_prob probs)
in (match (uu____5533) with
| (Some (hd), tl, rank) -> begin
(

let probs = (

let uu___141_5546 = probs
in {attempting = tl; wl_deferred = uu___141_5546.wl_deferred; ctr = uu___141_5546.ctr; defer_ok = uu___141_5546.defer_ok; smt_ok = uu___141_5546.smt_ok; tcenv = uu___141_5546.tcenv})
in (match (hd) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match ((((not (probs.defer_ok)) && (flex_refine_inner <= rank)) && (rank <= flex_rigid))) with
| true -> begin
(

let uu____5553 = (solve_flex_rigid_join env tp probs)
in (match (uu____5553) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end))
end
| uu____5556 -> begin
(match ((((not (probs.defer_ok)) && (rigid_flex <= rank)) && (rank <= refine_flex))) with
| true -> begin
(

let uu____5557 = (solve_rigid_flex_meet env tp probs)
in (match (uu____5557) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end))
end
| uu____5560 -> begin
(solve_t' env (maybe_invert tp) probs)
end)
end)
end))
end
| (None, uu____5561, uu____5562) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| uu____5571 -> begin
(

let uu____5576 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____5604 -> (match (uu____5604) with
| (c, uu____5609, uu____5610) -> begin
(c < probs.ctr)
end))))
in (match (uu____5576) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(

let uu____5632 = (FStar_List.map (fun uu____5638 -> (match (uu____5638) with
| (uu____5644, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (uu____5632))
end
| uu____5647 -> begin
(

let uu____5652 = (

let uu___142_5653 = probs
in (

let uu____5654 = (FStar_All.pipe_right attempt (FStar_List.map (fun uu____5663 -> (match (uu____5663) with
| (uu____5667, uu____5668, y) -> begin
y
end))))
in {attempting = uu____5654; wl_deferred = rest; ctr = uu___142_5653.ctr; defer_ok = uu___142_5653.defer_ok; smt_ok = uu___142_5653.smt_ok; tcenv = uu___142_5653.tcenv}))
in (solve env uu____5652))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____5675 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____5675) with
| USolved (wl) -> begin
(

let uu____5677 = (solve_prob orig None [] wl)
in (solve env uu____5677))
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

let uu____5711 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____5711) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____5714 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t1 = (whnf env t1)
in (

let t2 = (whnf env t2)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = uu____5722; FStar_Syntax_Syntax.pos = uu____5723; FStar_Syntax_Syntax.vars = uu____5724}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = uu____5727; FStar_Syntax_Syntax.pos = uu____5728; FStar_Syntax_Syntax.vars = uu____5729}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____5745 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____5753 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____5753) with
| true -> begin
(

let uu____5754 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" uu____5754 msg))
end
| uu____5755 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____5756 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> ((

let uu____5762 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5762) with
| true -> begin
(

let uu____5763 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" uu____5763))
end
| uu____5764 -> begin
()
end));
(

let uu____5765 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____5765) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let uu____5807 = (head_matches_delta env () t1 t2)
in (match (uu____5807) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (uu____5829) -> begin
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

let uu____5855 = (match (ts) with
| Some (t1, t2) -> begin
(

let uu____5864 = (FStar_Syntax_Subst.compress t1)
in (

let uu____5865 = (FStar_Syntax_Subst.compress t2)
in ((uu____5864), (uu____5865))))
end
| None -> begin
(

let uu____5868 = (FStar_Syntax_Subst.compress t1)
in (

let uu____5869 = (FStar_Syntax_Subst.compress t2)
in ((uu____5868), (uu____5869))))
end)
in (match (uu____5855) with
| (t1, t2) -> begin
(

let eq_prob = (fun t1 t2 -> (

let uu____5891 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _0_41 -> FStar_TypeChecker_Common.TProb (_0_41)) uu____5891)))
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(

let uu____5914 = (

let uu____5920 = (

let uu____5923 = (

let uu____5926 = (

let uu____5927 = (

let uu____5932 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (uu____5932)))
in FStar_Syntax_Syntax.Tm_refine (uu____5927))
in (FStar_Syntax_Syntax.mk uu____5926))
in (uu____5923 None t1.FStar_Syntax_Syntax.pos))
in (

let uu____5945 = (

let uu____5947 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (uu____5947)::[])
in ((uu____5920), (uu____5945))))
in Some (uu____5914))
end
| (uu____5956, FStar_Syntax_Syntax.Tm_refine (x, uu____5958)) -> begin
(

let uu____5963 = (

let uu____5967 = (

let uu____5969 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (uu____5969)::[])
in ((t1), (uu____5967)))
in Some (uu____5963))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____5975), uu____5976) -> begin
(

let uu____5981 = (

let uu____5985 = (

let uu____5987 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (uu____5987)::[])
in ((t2), (uu____5985)))
in Some (uu____5981))
end
| uu____5992 -> begin
(

let uu____5995 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____5995) with
| (head1, uu____6010) -> begin
(

let uu____6025 = (

let uu____6026 = (FStar_Syntax_Util.un_uinst head1)
in uu____6026.FStar_Syntax_Syntax.n)
in (match (uu____6025) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____6033; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (i); FStar_Syntax_Syntax.fv_qual = uu____6035}) -> begin
(

let prev = (match ((i > (Prims.parse_int "1"))) with
| true -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i - (Prims.parse_int "1")))
end
| uu____6041 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t1)
in (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t2)
in (disjoin t1 t2))))
end
| uu____6044 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____6053) -> begin
(

let uu____6066 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___121_6075 -> (match (uu___121_6075) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(

let uu____6080 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____6080) with
| (u', uu____6091) -> begin
(

let uu____6106 = (

let uu____6107 = (whnf env u')
in uu____6107.FStar_Syntax_Syntax.n)
in (match (uu____6106) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____6111) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____6127 -> begin
false
end))
end))
end
| uu____6128 -> begin
false
end)
end
| uu____6130 -> begin
false
end))))
in (match (uu____6066) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun uu____6151 tps -> (match (uu____6151) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(

let uu____6178 = (

let uu____6183 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound uu____6183))
in (match (uu____6178) with
| Some (bound, sub) -> begin
(make_lower_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end))
end
| uu____6202 -> begin
None
end)
end))
in (

let uu____6207 = (

let uu____6212 = (

let uu____6216 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((uu____6216), ([])))
in (make_lower_bound uu____6212 lower_bounds))
in (match (uu____6207) with
| None -> begin
((

let uu____6223 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6223) with
| true -> begin
(FStar_Util.print_string "No lower bounds\n")
end
| uu____6224 -> begin
()
end));
None;
)
end
| Some (lhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in ((

let uu____6236 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6236) with
| true -> begin
(

let wl' = (

let uu___143_6238 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___143_6238.wl_deferred; ctr = uu___143_6238.ctr; defer_ok = uu___143_6238.defer_ok; smt_ok = uu___143_6238.smt_ok; tcenv = uu___143_6238.tcenv})
in (

let uu____6239 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" uu____6239)))
end
| uu____6240 -> begin
()
end));
(

let uu____6241 = (solve_t env eq_prob (

let uu___144_6242 = wl
in {attempting = sub_probs; wl_deferred = uu___144_6242.wl_deferred; ctr = uu___144_6242.ctr; defer_ok = uu___144_6242.defer_ok; smt_ok = uu___144_6242.smt_ok; tcenv = uu___144_6242.tcenv}))
in (match (uu____6241) with
| Success (uu____6244) -> begin
(

let wl = (

let uu___145_6246 = wl
in {attempting = rest; wl_deferred = uu___145_6246.wl_deferred; ctr = uu___145_6246.ctr; defer_ok = uu___145_6246.defer_ok; smt_ok = uu___145_6246.smt_ok; tcenv = uu___145_6246.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let uu____6248 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| uu____6251 -> begin
None
end));
))
end)))
end))
end
| uu____6252 -> begin
(failwith "Impossible: Not a rigid-flex")
end)))
end));
))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> ((

let uu____6259 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6259) with
| true -> begin
(

let uu____6260 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" uu____6260))
end
| uu____6261 -> begin
()
end));
(

let uu____6262 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____6262) with
| (u, args) -> begin
(

let uu____6289 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (uu____6289) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(

let max = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____6308 -> begin
i
end))
in (

let base_types_match = (fun t1 t2 -> (

let uu____6320 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____6320) with
| (h1, args1) -> begin
(

let uu____6348 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____6348) with
| (h2, uu____6361) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
(

let uu____6380 = (FStar_Syntax_Syntax.fv_eq tc1 tc2)
in (match (uu____6380) with
| true -> begin
(match (((FStar_List.length args1) = (Prims.parse_int "0"))) with
| true -> begin
Some ([])
end
| uu____6392 -> begin
(

let uu____6393 = (

let uu____6395 = (

let uu____6396 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_42 -> FStar_TypeChecker_Common.TProb (_0_42)) uu____6396))
in (uu____6395)::[])
in Some (uu____6393))
end)
end
| uu____6402 -> begin
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
| uu____6417 -> begin
(

let uu____6418 = (

let uu____6420 = (

let uu____6421 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_43 -> FStar_TypeChecker_Common.TProb (_0_43)) uu____6421))
in (uu____6420)::[])
in Some (uu____6418))
end)
end
| uu____6427 -> begin
None
end)
end
| uu____6429 -> begin
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

let uu____6495 = (

let uu____6501 = (

let uu____6504 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x uu____6504))
in ((uu____6501), (m)))
in Some (uu____6495))))))
end))
end
| (uu____6513, FStar_Syntax_Syntax.Tm_refine (y, uu____6515)) -> begin
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
| (FStar_Syntax_Syntax.Tm_refine (x, uu____6547), uu____6548) -> begin
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
| uu____6579 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____6613) -> begin
(

let uu____6626 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___122_6635 -> (match (uu___122_6635) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(

let uu____6640 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____6640) with
| (u', uu____6651) -> begin
(

let uu____6666 = (

let uu____6667 = (whnf env u')
in uu____6667.FStar_Syntax_Syntax.n)
in (match (uu____6666) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____6671) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____6687 -> begin
false
end))
end))
end
| uu____6688 -> begin
false
end)
end
| uu____6690 -> begin
false
end))))
in (match (uu____6626) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun uu____6715 tps -> (match (uu____6715) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(

let uu____6756 = (

let uu____6763 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound uu____6763))
in (match (uu____6756) with
| Some (bound, sub) -> begin
(make_upper_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end))
end
| uu____6798 -> begin
None
end)
end))
in (

let uu____6805 = (

let uu____6812 = (

let uu____6818 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((uu____6818), ([])))
in (make_upper_bound uu____6812 upper_bounds))
in (match (uu____6805) with
| None -> begin
((

let uu____6827 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6827) with
| true -> begin
(FStar_Util.print_string "No upper bounds\n")
end
| uu____6828 -> begin
()
end));
None;
)
end
| Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in ((

let uu____6846 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6846) with
| true -> begin
(

let wl' = (

let uu___146_6848 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___146_6848.wl_deferred; ctr = uu___146_6848.ctr; defer_ok = uu___146_6848.defer_ok; smt_ok = uu___146_6848.smt_ok; tcenv = uu___146_6848.tcenv})
in (

let uu____6849 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" uu____6849)))
end
| uu____6850 -> begin
()
end));
(

let uu____6851 = (solve_t env eq_prob (

let uu___147_6852 = wl
in {attempting = sub_probs; wl_deferred = uu___147_6852.wl_deferred; ctr = uu___147_6852.ctr; defer_ok = uu___147_6852.defer_ok; smt_ok = uu___147_6852.smt_ok; tcenv = uu___147_6852.tcenv}))
in (match (uu____6851) with
| Success (uu____6854) -> begin
(

let wl = (

let uu___148_6856 = wl
in {attempting = rest; wl_deferred = uu___148_6856.wl_deferred; ctr = uu___148_6856.ctr; defer_ok = uu___148_6856.defer_ok; smt_ok = uu___148_6856.smt_ok; tcenv = uu___148_6856.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let uu____6858 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| uu____6861 -> begin
None
end));
))
end)))
end))
end
| uu____6862 -> begin
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

let uu____6927 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6927) with
| true -> begin
(

let uu____6928 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" uu____6928))
end
| uu____6929 -> begin
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

let uu___149_6960 = hd1
in (

let uu____6961 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___149_6960.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___149_6960.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6961}))
in (

let hd2 = (

let uu___150_6965 = hd2
in (

let uu____6966 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___150_6965.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___150_6965.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6966}))
in (

let prob = (

let uu____6970 = (

let uu____6973 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort uu____6973 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _0_44 -> FStar_TypeChecker_Common.TProb (_0_44)) uu____6970))
in (

let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (

let subst = (

let uu____6981 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd1))))::uu____6981)
in (

let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (

let uu____6984 = (aux ((((hd1), (imp)))::scope) env subst xs ys)
in (match (uu____6984) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi = (

let uu____7002 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (

let uu____7005 = (FStar_Syntax_Util.close_forall ((((hd1), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj uu____7002 uu____7005)))
in ((

let uu____7011 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7011) with
| true -> begin
(

let uu____7012 = (FStar_Syntax_Print.term_to_string phi)
in (

let uu____7013 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" uu____7012 uu____7013)))
end
| uu____7014 -> begin
()
end));
FStar_Util.Inl ((((prob)::sub_probs), (phi)));
))
end
| fail -> begin
fail
end))))))))
end
| uu____7028 -> begin
FStar_Util.Inr ("arity or argument-qualifier mismatch")
end))
in (

let scope = (p_scope orig)
in (

let uu____7034 = (aux scope env [] bs1 bs2)
in (match (uu____7034) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end)))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let uu____7050 = (compress_tprob wl problem)
in (solve_t' env uu____7050 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (

let uu____7083 = (head_matches_delta env wl t1 t2)
in (match (uu____7083) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____7100), uu____7101) -> begin
(

let may_relate = (fun head -> (

let uu____7116 = (

let uu____7117 = (FStar_Syntax_Util.un_uinst head)
in uu____7117.FStar_Syntax_Syntax.n)
in (match (uu____7116) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____7123 -> begin
false
end)))
in (

let uu____7124 = (((may_relate head1) || (may_relate head2)) && wl.smt_ok)
in (match (uu____7124) with
| true -> begin
(

let guard = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_eq2 env t1 t2)
end
| uu____7126 -> begin
(

let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(

let x = (FStar_Syntax_Syntax.new_bv None t1)
in (

let uu____7140 = (

let uu____7141 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 uu____7141 t2))
in (FStar_Syntax_Util.mk_forall x uu____7140)))
end))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB)) with
| true -> begin
(has_type_guard t1 t2)
end
| uu____7142 -> begin
(has_type_guard t2 t1)
end))
end)
in (

let uu____7143 = (solve_prob orig (Some (guard)) [] wl)
in (solve env uu____7143)))
end
| uu____7144 -> begin
(giveup env "head mismatch" orig)
end)))
end
| (uu____7145, Some (t1, t2)) -> begin
(solve_t env (

let uu___151_7153 = problem
in {FStar_TypeChecker_Common.pid = uu___151_7153.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___151_7153.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___151_7153.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___151_7153.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___151_7153.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___151_7153.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___151_7153.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___151_7153.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____7154, None) -> begin
((

let uu____7161 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7161) with
| true -> begin
(

let uu____7162 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____7163 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____7164 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____7165 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" uu____7162 uu____7163 uu____7164 uu____7165)))))
end
| uu____7166 -> begin
()
end));
(

let uu____7167 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____7167) with
| (head1, args1) -> begin
(

let uu____7193 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____7193) with
| (head2, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((nargs <> (FStar_List.length args2))) with
| true -> begin
(

let uu____7233 = (

let uu____7234 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____7235 = (args_to_string args1)
in (

let uu____7236 = (FStar_Syntax_Print.term_to_string head2)
in (

let uu____7237 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" uu____7234 uu____7235 uu____7236 uu____7237)))))
in (giveup env uu____7233 orig))
end
| uu____7238 -> begin
(

let uu____7239 = ((nargs = (Prims.parse_int "0")) || (

let uu____7242 = (FStar_Syntax_Util.eq_args args1 args2)
in (uu____7242 = FStar_Syntax_Util.Equal)))
in (match (uu____7239) with
| true -> begin
(

let uu____7243 = (solve_maybe_uinsts env orig head1 head2 wl)
in (match (uu____7243) with
| USolved (wl) -> begin
(

let uu____7245 = (solve_prob orig None [] wl)
in (solve env uu____7245))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end))
end
| uu____7248 -> begin
(

let uu____7249 = (base_and_refinement env wl t1)
in (match (uu____7249) with
| (base1, refinement1) -> begin
(

let uu____7275 = (base_and_refinement env wl t2)
in (match (uu____7275) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (None, None) -> begin
(

let uu____7329 = (solve_maybe_uinsts env orig head1 head2 wl)
in (match (uu____7329) with
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end
| USolved (wl) -> begin
(

let subprobs = (FStar_List.map2 (fun uu____7339 uu____7340 -> (match (((uu____7339), (uu____7340))) with
| ((a, uu____7350), (a', uu____7352)) -> begin
(

let uu____7357 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _0_45 -> FStar_TypeChecker_Common.TProb (_0_45)) uu____7357))
end)) args1 args2)
in (

let formula = (

let uu____7363 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l uu____7363))
in (

let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end))
end
| uu____7367 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env (

let uu___152_7400 = problem
in {FStar_TypeChecker_Common.pid = uu___152_7400.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___152_7400.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___152_7400.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___152_7400.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___152_7400.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___152_7400.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___152_7400.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___152_7400.FStar_TypeChecker_Common.rank}) wl)))
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

let uu____7420 = p
in (match (uu____7420) with
| (((u, k), xs, c), ps, (h, uu____7431, qs)) -> begin
(

let xs = (sn_binders env xs)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____7480 = (imitation_sub_probs orig env xs ps qs)
in (match (uu____7480) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (

let uu____7494 = (h gs_xs)
in (

let uu____7495 = (

let uu____7502 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_46 -> FStar_Util.Inl (_0_46)))
in (FStar_All.pipe_right uu____7502 (fun _0_47 -> Some (_0_47))))
in (FStar_Syntax_Util.abs xs uu____7494 uu____7495)))
in ((

let uu____7533 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7533) with
| true -> begin
(

let uu____7534 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (

let uu____7535 = (FStar_Syntax_Print.comp_to_string c)
in (

let uu____7536 = (FStar_Syntax_Print.term_to_string im)
in (

let uu____7537 = (FStar_Syntax_Print.tag_of_term im)
in (

let uu____7538 = (

let uu____7539 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right uu____7539 (FStar_String.concat ", ")))
in (

let uu____7542 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" uu____7534 uu____7535 uu____7536 uu____7537 uu____7538 uu____7542)))))))
end
| uu____7543 -> begin
()
end));
(

let wl = (solve_prob orig (Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl)
in (solve env (attempt sub_probs wl)));
))
end))))
end)))
in (

let imitate' = (fun orig env wl uu___123_7560 -> (match (uu___123_7560) with
| None -> begin
(giveup env "unable to compute subterms" orig)
end
| Some (p) -> begin
(imitate orig env wl p)
end))
in (

let project = (fun orig env wl i p -> (

let uu____7589 = p
in (match (uu____7589) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____7647 = (FStar_List.nth ps i)
in (match (uu____7647) with
| (pi, uu____7650) -> begin
(

let uu____7655 = (FStar_List.nth xs i)
in (match (uu____7655) with
| (xi, uu____7662) -> begin
(

let rec gs = (fun k -> (

let uu____7671 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____7671) with
| (bs, k) -> begin
(

let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
(([]), ([]))
end
| ((a, uu____7723))::tl -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (

let uu____7731 = (new_uvar r xs k_a)
in (match (uu____7731) with
| (gi_xs, gi) -> begin
(

let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (

let gi_ps = ((FStar_Syntax_Syntax.mk_Tm_app gi ps) (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst = (FStar_Syntax_Syntax.NT (((a), (gi_xs))))::subst
in (

let uu____7750 = (aux subst tl)
in (match (uu____7750) with
| (gi_xs', gi_ps') -> begin
(

let uu____7765 = (

let uu____7767 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (uu____7767)::gi_xs')
in (

let uu____7768 = (

let uu____7770 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (uu____7770)::gi_ps')
in ((uu____7765), (uu____7768))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in (

let uu____7773 = (

let uu____7774 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation uu____7774))
in (match (uu____7773) with
| true -> begin
None
end
| uu____7776 -> begin
(

let uu____7777 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (uu____7777) with
| (g_xs, uu____7784) -> begin
(

let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (

let uu____7791 = ((FStar_Syntax_Syntax.mk_Tm_app xi g_xs) None r)
in (

let uu____7796 = (

let uu____7803 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_48 -> FStar_Util.Inl (_0_48)))
in (FStar_All.pipe_right uu____7803 (fun _0_49 -> Some (_0_49))))
in (FStar_Syntax_Util.abs xs uu____7791 uu____7796)))
in (

let sub = (

let uu____7834 = (

let uu____7837 = ((FStar_Syntax_Syntax.mk_Tm_app proj ps) None r)
in (

let uu____7844 = (

let uu____7847 = (FStar_List.map (fun uu____7853 -> (match (uu____7853) with
| (uu____7858, uu____7859, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h uu____7847))
in (mk_problem (p_scope orig) orig uu____7837 (p_rel orig) uu____7844 None "projection")))
in (FStar_All.pipe_left (fun _0_50 -> FStar_TypeChecker_Common.TProb (_0_50)) uu____7834))
in ((

let uu____7869 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7869) with
| true -> begin
(

let uu____7870 = (FStar_Syntax_Print.term_to_string proj)
in (

let uu____7871 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" uu____7870 uu____7871)))
end
| uu____7872 -> begin
()
end));
(

let wl = (

let uu____7874 = (

let uu____7876 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (uu____7876))
in (solve_prob orig uu____7874 ((TERM (((u), (proj))))::[]) wl))
in (

let uu____7881 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _0_51 -> Some (_0_51)) uu____7881)));
))))
end))
end)))
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl -> (

let uu____7905 = lhs
in (match (uu____7905) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let uu____7928 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (uu____7928) with
| (xs, c) -> begin
(match (((FStar_List.length xs) = (FStar_List.length ps))) with
| true -> begin
(

let uu____7950 = (

let uu____7976 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____7976)))
in Some (uu____7950))
end
| uu____8042 -> begin
(

let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (

let uu____8059 = (

let uu____8063 = (

let uu____8064 = (FStar_Syntax_Subst.compress k)
in uu____8064.FStar_Syntax_Syntax.n)
in ((uu____8063), (args)))
in (match (uu____8059) with
| (uu____8071, []) -> begin
(

let uu____8073 = (

let uu____8079 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____8079)))
in Some (uu____8073))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(

let uu____8096 = (FStar_Syntax_Util.head_and_args k)
in (match (uu____8096) with
| (uv, uv_args) -> begin
(

let uu____8125 = (

let uu____8126 = (FStar_Syntax_Subst.compress uv)
in uu____8126.FStar_Syntax_Syntax.n)
in (match (uu____8125) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____8133) -> begin
(

let uu____8146 = (pat_vars env [] uv_args)
in (match (uu____8146) with
| None -> begin
None
end
| Some (scope) -> begin
(

let xs = (FStar_All.pipe_right args (FStar_List.map (fun uu____8160 -> (

let uu____8161 = (

let uu____8162 = (

let uu____8163 = (

let uu____8166 = (

let uu____8167 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8167 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____8166))
in (Prims.fst uu____8163))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) uu____8162))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____8161)))))
in (

let c = (

let uu____8173 = (

let uu____8174 = (

let uu____8177 = (

let uu____8178 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8178 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope uu____8177))
in (Prims.fst uu____8174))
in (FStar_Syntax_Syntax.mk_Total uu____8173))
in (

let k' = (FStar_Syntax_Util.arrow xs c)
in (

let uv_sol = (

let uu____8187 = (

let uu____8194 = (

let uu____8200 = (

let uu____8201 = (

let uu____8204 = (

let uu____8205 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8205 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total uu____8204))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8201))
in FStar_Util.Inl (uu____8200))
in Some (uu____8194))
in (FStar_Syntax_Util.abs scope k' uu____8187))
in ((FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)));
Some (((xs), (c)));
)))))
end))
end
| uu____8228 -> begin
None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), uu____8233) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs)
in (match ((n_xs = n_args)) with
| true -> begin
(

let uu____8259 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right uu____8259 (fun _0_52 -> Some (_0_52))))
end
| uu____8269 -> begin
(match ((n_xs < n_args)) with
| true -> begin
(

let uu____8278 = (FStar_Util.first_N n_xs args)
in (match (uu____8278) with
| (args, rest) -> begin
(

let uu____8294 = (FStar_Syntax_Subst.open_comp xs c)
in (match (uu____8294) with
| (xs, c) -> begin
(

let uu____8302 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt uu____8302 (fun uu____8313 -> (match (uu____8313) with
| (xs', c) -> begin
Some ((((FStar_List.append xs xs')), (c)))
end))))
end))
end))
end
| uu____8334 -> begin
(

let uu____8335 = (FStar_Util.first_N n_args xs)
in (match (uu____8335) with
| (xs, rest) -> begin
(

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c))))) None k.FStar_Syntax_Syntax.pos)
in (

let uu____8381 = (

let uu____8384 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs uu____8384))
in (FStar_All.pipe_right uu____8381 (fun _0_53 -> Some (_0_53)))))
end))
end)
end)))
end
| uu____8392 -> begin
(

let uu____8396 = (

let uu____8397 = (FStar_Syntax_Print.uvar_to_string uv)
in (

let uu____8401 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____8402 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" uu____8397 uu____8401 uu____8402))))
in (failwith uu____8396))
end)))
in (

let uu____8406 = (elim k_uv ps)
in (FStar_Util.bind_opt uu____8406 (fun uu____8434 -> (match (uu____8434) with
| (xs, c) -> begin
(

let uu____8462 = (

let uu____8485 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (uu____8485)))
in Some (uu____8462))
end))))))
end)
end)))
in (

let rec imitate_or_project = (fun n stopt i -> (match (((i >= n) || (FStar_Option.isNone stopt))) with
| true -> begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end
| uu____8554 -> begin
(

let st = (FStar_Option.get stopt)
in (

let tx = (FStar_Unionfind.new_transaction ())
in (match ((i = (~- ((Prims.parse_int "1"))))) with
| true -> begin
(

let uu____8557 = (imitate orig env wl st)
in (match (uu____8557) with
| Failed (uu____8562) -> begin
((FStar_Unionfind.rollback tx);
(imitate_or_project n stopt (i + (Prims.parse_int "1")));
)
end
| sol -> begin
sol
end))
end
| uu____8567 -> begin
(

let uu____8568 = (project orig env wl i st)
in (match (uu____8568) with
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

let uu____8586 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____8586) with
| (hd, uu____8597) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| uu____8615 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd)
in (

let uu____8618 = (FStar_Util.set_is_subset_of fvs_hd fvs1)
in (match (uu____8618) with
| true -> begin
true
end
| uu____8619 -> begin
((

let uu____8621 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8621) with
| true -> begin
(

let uu____8622 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" uu____8622))
end
| uu____8623 -> begin
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

let uu____8630 = (

let uu____8633 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____8633 Prims.fst))
in (FStar_All.pipe_right uu____8630 FStar_Syntax_Free.names))
in (

let uu____8664 = (FStar_Util.set_is_empty fvs_hd)
in (match (uu____8664) with
| true -> begin
(~- ((Prims.parse_int "1")))
end
| uu____8665 -> begin
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

let uu____8673 = (occurs_check env wl ((uv), (k_uv)) t2)
in (match (uu____8673) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(

let uu____8681 = (

let uu____8682 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " uu____8682))
in (giveup_or_defer orig uu____8681))
end
| uu____8683 -> begin
(

let uu____8684 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____8684) with
| true -> begin
(

let uu____8685 = (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t2)) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))
in (match (uu____8685) with
| true -> begin
(

let uu____8686 = (subterms args_lhs)
in (imitate' orig env wl uu____8686))
end
| uu____8688 -> begin
((

let uu____8690 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8690) with
| true -> begin
(

let uu____8691 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____8692 = (names_to_string fvs1)
in (

let uu____8693 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" uu____8691 uu____8692 uu____8693))))
end
| uu____8694 -> begin
()
end));
(

let sol = (match (vars) with
| [] -> begin
t2
end
| uu____8698 -> begin
(

let uu____8699 = (sn_binders env vars)
in (u_abs k_uv uu____8699 t2))
end)
in (

let wl = (solve_prob orig None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl)
in (solve env wl)));
)
end))
end
| uu____8706 -> begin
(match ((((not (patterns_only)) && wl.defer_ok) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end
| uu____8707 -> begin
(

let uu____8708 = ((not (patterns_only)) && (check_head fvs1 t2))
in (match (uu____8708) with
| true -> begin
((

let uu____8710 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8710) with
| true -> begin
(

let uu____8711 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____8712 = (names_to_string fvs1)
in (

let uu____8713 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" uu____8711 uu____8712 uu____8713))))
end
| uu____8714 -> begin
()
end));
(

let uu____8715 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____8715 (~- ((Prims.parse_int "1")))));
)
end
| uu____8724 -> begin
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
| uu____8725 -> begin
(

let uu____8726 = (

let uu____8727 = (FStar_Syntax_Free.names t1)
in (check_head uu____8727 t2))
in (match (uu____8726) with
| true -> begin
(

let im_ok = (imitate_ok t2)
in ((

let uu____8731 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8731) with
| true -> begin
(

let uu____8732 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" uu____8732 (match ((im_ok < (Prims.parse_int "0"))) with
| true -> begin
"imitating"
end
| uu____8733 -> begin
"projecting"
end)))
end
| uu____8734 -> begin
()
end));
(

let uu____8735 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) uu____8735 im_ok));
))
end
| uu____8744 -> begin
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
| uu____8755 -> begin
(

let force_quasi_pattern = (fun xs_opt uu____8777 -> (match (uu____8777) with
| (t, u, k, args) -> begin
(

let uu____8807 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____8807) with
| (all_formals, uu____8818) -> begin
(

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match (((formals), (args))) with
| ([], []) -> begin
(

let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun uu____8910 -> (match (uu____8910) with
| (x, imp) -> begin
(

let uu____8917 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____8917), (imp)))
end))))
in (

let pattern_vars = (FStar_List.rev pattern_vars)
in (

let kk = (

let uu____8925 = (FStar_Syntax_Util.type_u ())
in (match (uu____8925) with
| (t, uu____8929) -> begin
(

let uu____8930 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst uu____8930))
end))
in (

let uu____8933 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (uu____8933) with
| (t', tm_u1) -> begin
(

let uu____8940 = (destruct_flex_t t')
in (match (uu____8940) with
| (uu____8960, u1, k1, uu____8963) -> begin
(

let sol = (

let uu____8991 = (

let uu____8996 = (u_abs k all_formals t')
in ((((u), (k))), (uu____8996)))
in TERM (uu____8991))
in (

let t_app = ((FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args) None t.FStar_Syntax_Syntax.pos)
in ((sol), (((t_app), (u1), (k1), (pat_args))))))
end))
end)))))
end
| ((formal)::formals, (hd)::tl) -> begin
(

let uu____9056 = (pat_var_opt env pat_args hd)
in (match (uu____9056) with
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun uu____9085 -> (match (uu____9085) with
| (x, uu____9089) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in (match ((not (maybe_pat))) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| uu____9092 -> begin
(

let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____9095 = (

let uu____9096 = (FStar_Util.set_is_subset_of fvs pattern_var_set)
in (not (uu____9096)))
in (match (uu____9095) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| uu____9099 -> begin
(

let uu____9100 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) uu____9100 formals tl))
end)))
end))
end))
end
| uu____9106 -> begin
(failwith "Impossible")
end))
in (

let uu____9117 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] uu____9117 all_formals args)))
end))
end))
in (

let solve_both_pats = (fun wl uu____9165 uu____9166 r -> (match (((uu____9165), (uu____9166))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
(

let uu____9320 = ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys))
in (match (uu____9320) with
| true -> begin
(

let uu____9324 = (solve_prob orig None [] wl)
in (solve env uu____9324))
end
| uu____9325 -> begin
(

let xs = (sn_binders env xs)
in (

let ys = (sn_binders env ys)
in (

let zs = (intersect_vars xs ys)
in ((

let uu____9339 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9339) with
| true -> begin
(

let uu____9340 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (

let uu____9341 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (

let uu____9342 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (

let uu____9343 = (FStar_Syntax_Print.term_to_string k1)
in (

let uu____9344 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" uu____9340 uu____9341 uu____9342 uu____9343 uu____9344))))))
end
| uu____9345 -> begin
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

let uu____9386 = (FStar_Syntax_Util.subst_of_list xs args)
in (FStar_Syntax_Subst.subst uu____9386 k))
end
| uu____9388 -> begin
(match ((args_len < xs_len)) with
| true -> begin
(

let uu____9394 = (FStar_Util.first_N args_len xs)
in (match (uu____9394) with
| (xs, xs_rest) -> begin
(

let k = (

let uu____9424 = (FStar_Syntax_Syntax.mk_GTotal k)
in (FStar_Syntax_Util.arrow xs_rest uu____9424))
in (

let uu____9427 = (FStar_Syntax_Util.subst_of_list xs args)
in (FStar_Syntax_Subst.subst uu____9427 k)))
end))
end
| uu____9429 -> begin
(

let uu____9430 = (

let uu____9431 = (FStar_Syntax_Print.term_to_string k)
in (

let uu____9432 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (

let uu____9433 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" uu____9431 uu____9432 uu____9433))))
in (failwith uu____9430))
end)
end))))
in (

let uu____9434 = (

let uu____9440 = (

let uu____9448 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals uu____9448))
in (match (uu____9440) with
| (bs, k1') -> begin
(

let uu____9466 = (

let uu____9474 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals uu____9474))
in (match (uu____9466) with
| (cs, k2') -> begin
(

let k1'_xs = (subst_k k1' bs args1)
in (

let k2'_ys = (subst_k k2' cs args2)
in (

let sub_prob = (

let uu____9495 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_54 -> FStar_TypeChecker_Common.TProb (_0_54)) uu____9495))
in (

let uu____9500 = (

let uu____9503 = (

let uu____9504 = (FStar_Syntax_Subst.compress k1')
in uu____9504.FStar_Syntax_Syntax.n)
in (

let uu____9507 = (

let uu____9508 = (FStar_Syntax_Subst.compress k2')
in uu____9508.FStar_Syntax_Syntax.n)
in ((uu____9503), (uu____9507))))
in (match (uu____9500) with
| (FStar_Syntax_Syntax.Tm_type (uu____9516), uu____9517) -> begin
((k1'), ((sub_prob)::[]))
end
| (uu____9521, FStar_Syntax_Syntax.Tm_type (uu____9522)) -> begin
((k2'), ((sub_prob)::[]))
end
| uu____9526 -> begin
(

let uu____9529 = (FStar_Syntax_Util.type_u ())
in (match (uu____9529) with
| (t, uu____9538) -> begin
(

let uu____9539 = (new_uvar r zs t)
in (match (uu____9539) with
| (k_zs, uu____9548) -> begin
(

let kprob = (

let uu____9550 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k_zs None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_55 -> FStar_TypeChecker_Common.TProb (_0_55)) uu____9550))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end)))))
end))
end))
in (match (uu____9434) with
| (k_u', sub_probs) -> begin
(

let uu____9564 = (

let uu____9572 = (

let uu____9573 = (new_uvar r zs k_u')
in (FStar_All.pipe_left Prims.fst uu____9573))
in (

let uu____9578 = (

let uu____9581 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs uu____9581))
in (

let uu____9584 = (

let uu____9587 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys uu____9587))
in ((uu____9572), (uu____9578), (uu____9584)))))
in (match (uu____9564) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs u_zs)
in (

let uu____9606 = (occurs_check env wl ((u1), (k1)) sub1)
in (match (uu____9606) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end
| uu____9618 -> begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in (

let uu____9630 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____9630) with
| true -> begin
(

let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end
| uu____9635 -> begin
(

let sub2 = (u_abs knew2 ys u_zs)
in (

let uu____9637 = (occurs_check env wl ((u2), (k2)) sub2)
in (match (uu____9637) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end
| uu____9649 -> begin
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

let solve_one_pat = (fun uu____9689 uu____9690 -> (match (((uu____9689), (uu____9690))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
((

let uu____9794 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9794) with
| true -> begin
(

let uu____9795 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____9796 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" uu____9795 uu____9796)))
end
| uu____9797 -> begin
()
end));
(

let uu____9798 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____9798) with
| true -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____9808 uu____9809 -> (match (((uu____9808), (uu____9809))) with
| ((a, uu____9819), (t2, uu____9821)) -> begin
(

let uu____9826 = (

let uu____9829 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig uu____9829 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right uu____9826 (fun _0_56 -> FStar_TypeChecker_Common.TProb (_0_56))))
end)) xs args2)
in (

let guard = (

let uu____9833 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____9833))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end
| uu____9839 -> begin
(

let t2 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t2)
in (

let uu____9843 = (occurs_check env wl ((u1), (k1)) t2)
in (match (uu____9843) with
| (occurs_ok, uu____9852) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in (

let uu____9857 = (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars))
in (match (uu____9857) with
| true -> begin
(

let sol = (

let uu____9859 = (

let uu____9864 = (u_abs k1 xs t2)
in ((((u1), (k1))), (uu____9864)))
in TERM (uu____9859))
in (

let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end
| uu____9876 -> begin
(

let uu____9877 = (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok))
in (match (uu____9877) with
| true -> begin
(

let uu____9878 = (force_quasi_pattern (Some (xs)) ((t2), (u2), (k2), (args2)))
in (match (uu____9878) with
| (sol, (uu____9892, u2, k2, ys)) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____9902 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____9902) with
| true -> begin
(

let uu____9903 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" uu____9903))
end
| uu____9904 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| uu____9908 -> begin
(giveup env "impossible" orig)
end);
))
end))
end
| uu____9909 -> begin
(giveup_or_defer orig "flex-flex constraint")
end))
end)))
end))))
end));
)
end))
in (

let uu____9910 = lhs
in (match (uu____9910) with
| (t1, u1, k1, args1) -> begin
(

let uu____9915 = rhs
in (match (uu____9915) with
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
| uu____9941 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end
| uu____9946 -> begin
(

let uu____9947 = (force_quasi_pattern None ((t1), (u1), (k1), (args1)))
in (match (uu____9947) with
| (sol, uu____9954) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____9957 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____9957) with
| true -> begin
(

let uu____9958 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" uu____9958))
end
| uu____9959 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| uu____9963 -> begin
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

let uu____9965 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____9965) with
| true -> begin
(

let uu____9966 = (solve_prob orig None [] wl)
in (solve env uu____9966))
end
| uu____9967 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in (

let uu____9970 = (FStar_Util.physical_equality t1 t2)
in (match (uu____9970) with
| true -> begin
(

let uu____9971 = (solve_prob orig None [] wl)
in (solve env uu____9971))
end
| uu____9972 -> begin
((

let uu____9974 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____9974) with
| true -> begin
(

let uu____9975 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" uu____9975))
end
| uu____9976 -> begin
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

let mk_c = (fun c uu___124_10021 -> (match (uu___124_10021) with
| [] -> begin
c
end
| bs -> begin
(

let uu____10035 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c))))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total uu____10035))
end))
in (

let uu____10049 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____10049) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (

let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (

let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (

let rel = (

let uu____10135 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____10135) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____10136 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (

let uu____10137 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _0_57 -> FStar_TypeChecker_Common.CProb (_0_57)) uu____10137)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___125_10214 -> (match (uu___125_10214) with
| [] -> begin
t
end
| bs -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l))))) None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____10253 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____10253) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (

let uu____10336 = (

let uu____10339 = (FStar_Syntax_Subst.subst subst tbody1)
in (

let uu____10340 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig uu____10339 problem.FStar_TypeChecker_Common.relation uu____10340 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _0_58 -> FStar_TypeChecker_Common.TProb (_0_58)) uu____10336))))
end)))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____10355) -> begin
true
end
| uu____10370 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____10389 -> begin
(

let t = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____10395 -> begin
FStar_Util.Inr (t)
end))
end))
in (

let uu____10398 = (

let uu____10409 = (maybe_eta t1)
in (

let uu____10414 = (maybe_eta t2)
in ((uu____10409), (uu____10414))))
in (match (uu____10398) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(solve_t env (

let uu___153_10445 = problem
in {FStar_TypeChecker_Common.pid = uu___153_10445.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___153_10445.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___153_10445.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___153_10445.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___153_10445.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___153_10445.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___153_10445.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___153_10445.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs))) | ((FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs))) -> begin
(

let uu____10478 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____10478) with
| true -> begin
(

let uu____10479 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig uu____10479 t_abs wl))
end
| uu____10483 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| uu____10484 -> begin
(failwith "Impossible: at least one side is an abstraction")
end))))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____10495), FStar_Syntax_Syntax.Tm_refine (uu____10496)) -> begin
(

let uu____10505 = (as_refinement env wl t1)
in (match (uu____10505) with
| (x1, phi1) -> begin
(

let uu____10510 = (as_refinement env wl t2)
in (match (uu____10510) with
| (x2, phi2) -> begin
(

let base_prob = (

let uu____10516 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _0_59 -> FStar_TypeChecker_Common.TProb (_0_59)) uu____10516))
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

let uu____10549 = (imp phi1 phi2)
in (FStar_All.pipe_right uu____10549 (guard_on_element problem x1))))
in (

let fallback = (fun uu____10553 -> (

let impl = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end
| uu____10555 -> begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end)
in (

let guard = (

let uu____10559 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____10559 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl))))))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let ref_prob = (

let uu____10566 = (

let uu____10569 = (

let uu____10570 = (FStar_Syntax_Syntax.mk_binder x1)
in (uu____10570)::(p_scope orig))
in (mk_problem uu____10569 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _0_60 -> FStar_TypeChecker_Common.TProb (_0_60)) uu____10566))
in (

let uu____10573 = (solve env (

let uu___154_10574 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___154_10574.ctr; defer_ok = false; smt_ok = uu___154_10574.smt_ok; tcenv = uu___154_10574.tcenv}))
in (match (uu____10573) with
| Failed (uu____10578) -> begin
(fallback ())
end
| Success (uu____10581) -> begin
(

let guard = (

let uu____10585 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (

let uu____10588 = (

let uu____10589 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right uu____10589 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj uu____10585 uu____10588)))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (

let wl = (

let uu___155_10596 = wl
in {attempting = uu___155_10596.attempting; wl_deferred = uu___155_10596.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___155_10596.defer_ok; smt_ok = uu___155_10596.smt_ok; tcenv = uu___155_10596.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end)))
end
| uu____10597 -> begin
(fallback ())
end)))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(

let uu____10650 = (destruct_flex_t t1)
in (

let uu____10651 = (destruct_flex_t t2)
in (flex_flex orig uu____10650 uu____10651)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(

let uu____10667 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig uu____10667 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_arrow (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
(solve_t' env (

let uu___156_10716 = problem
in {FStar_TypeChecker_Common.pid = uu___156_10716.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___156_10716.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___156_10716.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___156_10716.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___156_10716.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___156_10716.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___156_10716.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___156_10716.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___156_10716.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____10732 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____10734 = (

let uu____10735 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation uu____10735))
in (match (uu____10734) with
| true -> begin
(

let uu____10736 = (FStar_All.pipe_left (fun _0_61 -> FStar_TypeChecker_Common.TProb (_0_61)) (

let uu___157_10739 = problem
in {FStar_TypeChecker_Common.pid = uu___157_10739.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___157_10739.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___157_10739.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___157_10739.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___157_10739.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___157_10739.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___157_10739.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___157_10739.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___157_10739.FStar_TypeChecker_Common.rank}))
in (

let uu____10740 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____10736 uu____10740 t2 wl)))
end
| uu____10744 -> begin
(

let uu____10745 = (base_and_refinement env wl t2)
in (match (uu____10745) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(

let uu____10775 = (FStar_All.pipe_left (fun _0_62 -> FStar_TypeChecker_Common.TProb (_0_62)) (

let uu___158_10778 = problem
in {FStar_TypeChecker_Common.pid = uu___158_10778.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___158_10778.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___158_10778.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___158_10778.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___158_10778.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___158_10778.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___158_10778.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___158_10778.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___158_10778.FStar_TypeChecker_Common.rank}))
in (

let uu____10779 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false uu____10775 uu____10779 t_base wl)))
end
| Some (y, phi) -> begin
(

let y' = (

let uu___159_10794 = y
in {FStar_Syntax_Syntax.ppname = uu___159_10794.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___159_10794.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element problem y' phi)
in (

let base_prob = (

let uu____10797 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_63 -> FStar_TypeChecker_Common.TProb (_0_63)) uu____10797))
in (

let guard = (

let uu____10805 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____10805 impl))
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
| uu____10826 -> begin
(

let uu____10827 = (base_and_refinement env wl t1)
in (match (uu____10827) with
| (t_base, uu____10838) -> begin
(solve_t env (

let uu___160_10853 = problem
in {FStar_TypeChecker_Common.pid = uu___160_10853.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___160_10853.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___160_10853.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___160_10853.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___160_10853.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___160_10853.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___160_10853.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___160_10853.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (FStar_Syntax_Syntax.Tm_refine (uu____10856), uu____10857) -> begin
(

let t2 = (

let uu____10865 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement uu____10865))
in (solve_t env (

let uu___161_10878 = problem
in {FStar_TypeChecker_Common.pid = uu___161_10878.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___161_10878.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___161_10878.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___161_10878.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___161_10878.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___161_10878.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___161_10878.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___161_10878.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___161_10878.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____10879, FStar_Syntax_Syntax.Tm_refine (uu____10880)) -> begin
(

let t1 = (

let uu____10888 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement uu____10888))
in (solve_t env (

let uu___162_10901 = problem
in {FStar_TypeChecker_Common.pid = uu___162_10901.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___162_10901.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___162_10901.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___162_10901.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_10901.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_10901.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_10901.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_10901.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_10901.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(

let head1 = (

let uu____10931 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right uu____10931 Prims.fst))
in (

let head2 = (

let uu____10962 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right uu____10962 Prims.fst))
in (

let uu____10990 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____10990) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____10999 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____10999) with
| true -> begin
(

let guard = (

let uu____11006 = (

let uu____11007 = (FStar_Syntax_Util.eq_tm t1 t2)
in (uu____11007 = FStar_Syntax_Util.Equal))
in (match (uu____11006) with
| true -> begin
None
end
| uu____11009 -> begin
(

let uu____11010 = (mk_eq2 env t1 t2)
in (FStar_All.pipe_left (fun _0_64 -> Some (_0_64)) uu____11010))
end))
in (

let uu____11012 = (solve_prob orig guard [] wl)
in (solve env uu____11012)))
end
| uu____11013 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____11014 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, uu____11016, uu____11017), uu____11018) -> begin
(solve_t' env (

let uu___163_11037 = problem
in {FStar_TypeChecker_Common.pid = uu___163_11037.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___163_11037.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___163_11037.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___163_11037.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___163_11037.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___163_11037.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___163_11037.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___163_11037.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___163_11037.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____11040, FStar_Syntax_Syntax.Tm_ascribed (t2, uu____11042, uu____11043)) -> begin
(solve_t' env (

let uu___164_11062 = problem
in {FStar_TypeChecker_Common.pid = uu___164_11062.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___164_11062.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___164_11062.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___164_11062.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_11062.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_11062.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_11062.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_11062.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_11062.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(

let uu____11075 = (

let uu____11076 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____11077 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" uu____11076 uu____11077)))
in (failwith uu____11075))
end
| uu____11078 -> begin
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

let uu____11110 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____11110) with
| true -> begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end
| uu____11111 -> begin
()
end));
(

let sub_probs = (FStar_List.map2 (fun uu____11118 uu____11119 -> (match (((uu____11118), (uu____11119))) with
| ((a1, uu____11129), (a2, uu____11131)) -> begin
(

let uu____11136 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _0_65 -> FStar_TypeChecker_Common.TProb (_0_65)) uu____11136))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (

let uu____11142 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l uu____11142))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))));
))
in (

let solve_sub = (fun c1 edge c2 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let lift_c1 = (fun uu____11162 -> (

let wp = (match (c1.FStar_Syntax_Syntax.effect_args) with
| ((wp1, uu____11169))::[] -> begin
wp1
end
| uu____11182 -> begin
(

let uu____11188 = (

let uu____11189 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" uu____11189))
in (failwith uu____11188))
end)
in (

let uu____11192 = (

let uu____11198 = (

let uu____11199 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg uu____11199))
in (uu____11198)::[])
in {FStar_Syntax_Syntax.comp_univs = c1.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu____11192; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let uu____11200 = (lift_c1 ())
in (solve_eq uu____11200 c2))
end
| uu____11201 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___126_11204 -> (match (uu___126_11204) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| uu____11205 -> begin
false
end))))
in (

let uu____11206 = (match (((c1.FStar_Syntax_Syntax.effect_args), (c2.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____11230))::uu____11231, ((wp2, uu____11233))::uu____11234) -> begin
((wp1), (wp2))
end
| uu____11275 -> begin
(

let uu____11288 = (

let uu____11289 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____11290 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" uu____11289 uu____11290)))
in (failwith uu____11288))
end)
in (match (uu____11206) with
| (wpc1, wpc2) -> begin
(

let uu____11307 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____11307) with
| true -> begin
(

let uu____11310 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env uu____11310 wl))
end
| uu____11313 -> begin
(

let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let uu____11315 = (FStar_All.pipe_right c2_decl.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____11315) with
| true -> begin
(

let c1_repr = (

let uu____11318 = (

let uu____11319 = (

let uu____11320 = (lift_c1 ())
in (FStar_Syntax_Syntax.mk_Comp uu____11320))
in (

let uu____11321 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____11319 uu____11321)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____11318))
in (

let c2_repr = (

let uu____11323 = (

let uu____11324 = (FStar_Syntax_Syntax.mk_Comp c2)
in (

let uu____11325 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.reify_comp env uu____11324 uu____11325)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.WHNF)::[]) env uu____11323))
in (

let prob = (

let uu____11327 = (

let uu____11330 = (

let uu____11331 = (FStar_Syntax_Print.term_to_string c1_repr)
in (

let uu____11332 = (FStar_Syntax_Print.term_to_string c2_repr)
in (FStar_Util.format2 "sub effect repr: %s <: %s" uu____11331 uu____11332)))
in (sub_prob c1_repr problem.FStar_TypeChecker_Common.relation c2_repr uu____11330))
in FStar_TypeChecker_Common.TProb (uu____11327))
in (

let wl = (

let uu____11334 = (

let uu____11336 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in Some (uu____11336))
in (solve_prob orig uu____11334 [] wl))
in (solve env (attempt ((prob)::[]) wl))))))
end
| uu____11339 -> begin
(

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____11341 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____11343 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11343) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____11344 -> begin
()
end));
(

let uu____11345 = (

let uu____11348 = (

let uu____11349 = (

let uu____11359 = (

let uu____11360 = (

let uu____11361 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (uu____11361)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____11360 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (

let uu____11362 = (

let uu____11364 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____11365 = (

let uu____11367 = (

let uu____11368 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11368))
in (uu____11367)::[])
in (uu____11364)::uu____11365))
in ((uu____11359), (uu____11362))))
in FStar_Syntax_Syntax.Tm_app (uu____11349))
in (FStar_Syntax_Syntax.mk uu____11348))
in (uu____11345 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r));
)
end
| uu____11378 -> begin
(

let uu____11379 = (

let uu____11382 = (

let uu____11383 = (

let uu____11393 = (

let uu____11394 = (

let uu____11395 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (uu____11395)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with uu____11394 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (

let uu____11396 = (

let uu____11398 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (

let uu____11399 = (

let uu____11401 = (FStar_Syntax_Syntax.as_arg wpc2)
in (

let uu____11402 = (

let uu____11404 = (

let uu____11405 = (edge.FStar_TypeChecker_Env.mlift.FStar_TypeChecker_Env.mlift_wp c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11405))
in (uu____11404)::[])
in (uu____11401)::uu____11402))
in (uu____11398)::uu____11399))
in ((uu____11393), (uu____11396))))
in FStar_Syntax_Syntax.Tm_app (uu____11383))
in (FStar_Syntax_Syntax.mk uu____11382))
in (uu____11379 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r))
end)
end)
in (

let base_prob = (

let uu____11416 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _0_66 -> FStar_TypeChecker_Common.TProb (_0_66)) uu____11416))
in (

let wl = (

let uu____11422 = (

let uu____11424 = (

let uu____11427 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj uu____11427 g))
in (FStar_All.pipe_left (fun _0_67 -> Some (_0_67)) uu____11424))
in (solve_prob orig uu____11422 [] wl))
in (solve env (attempt ((base_prob)::[]) wl)))))
end)))
end))
end)))
end))))
in (

let uu____11437 = (FStar_Util.physical_equality c1 c2)
in (match (uu____11437) with
| true -> begin
(

let uu____11438 = (solve_prob orig None [] wl)
in (solve env uu____11438))
end
| uu____11439 -> begin
((

let uu____11441 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11441) with
| true -> begin
(

let uu____11442 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____11443 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" uu____11442 (rel_to_string problem.FStar_TypeChecker_Common.relation) uu____11443)))
end
| uu____11444 -> begin
()
end));
(

let uu____11445 = (

let uu____11448 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (

let uu____11449 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((uu____11448), (uu____11449))))
in (match (uu____11445) with
| (c1, c2) -> begin
(match (((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____11453), FStar_Syntax_Syntax.Total (t2, uu____11455)) when (FStar_Syntax_Util.non_informative t2) -> begin
(

let uu____11468 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env uu____11468 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____11471), FStar_Syntax_Syntax.Total (uu____11472)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.Total (t2, _))) | ((FStar_Syntax_Syntax.GTotal (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) | ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) -> begin
(

let uu____11521 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env uu____11521 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(

let uu____11528 = (

let uu___165_11531 = problem
in (

let uu____11534 = (

let uu____11535 = (FStar_TypeChecker_Env.comp_to_comp_typ env c1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____11535))
in {FStar_TypeChecker_Common.pid = uu___165_11531.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu____11534; FStar_TypeChecker_Common.relation = uu___165_11531.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___165_11531.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___165_11531.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___165_11531.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___165_11531.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___165_11531.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___165_11531.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___165_11531.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____11528 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(

let uu____11540 = (

let uu___166_11543 = problem
in (

let uu____11546 = (

let uu____11547 = (FStar_TypeChecker_Env.comp_to_comp_typ env c2)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp uu____11547))
in {FStar_TypeChecker_Common.pid = uu___166_11543.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___166_11543.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___166_11543.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu____11546; FStar_TypeChecker_Common.element = uu___166_11543.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_11543.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___166_11543.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___166_11543.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_11543.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_11543.FStar_TypeChecker_Common.rank}))
in (solve_c env uu____11540 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____11548), FStar_Syntax_Syntax.Comp (uu____11549)) -> begin
(

let uu____11550 = (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2))))
in (match (uu____11550) with
| true -> begin
(

let uu____11551 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env uu____11551 wl))
end
| uu____11554 -> begin
(

let c1_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c1)
in (

let c2_comp = (FStar_TypeChecker_Env.comp_to_comp_typ env c2)
in (match (((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name))) with
| true -> begin
(solve_eq c1_comp c2_comp)
end
| uu____11557 -> begin
(

let c1 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c1)
in (

let c2 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c2)
in ((

let uu____11561 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11561) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____11562 -> begin
()
end));
(

let uu____11563 = (FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (uu____11563) with
| None -> begin
(

let uu____11565 = (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (

let uu____11566 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative uu____11566)))
in (match (uu____11565) with
| true -> begin
(

let edge = {FStar_TypeChecker_Env.msource = c1.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c2.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = FStar_TypeChecker_Env.identity_mlift}
in (solve_sub c1 edge c2))
end
| uu____11568 -> begin
(

let uu____11569 = (

let uu____11570 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____11571 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" uu____11570 uu____11571)))
in (giveup env uu____11569 orig))
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

let uu____11576 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____11596 -> (match (uu____11596) with
| (uu____11607, uu____11608, u, uu____11610, uu____11611, uu____11612) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____11576 (FStar_String.concat ", "))))


let ineqs_to_string : (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.string = (fun ineqs -> (

let vars = (

let uu____11641 = (FStar_All.pipe_right (Prims.fst ineqs) (FStar_List.map FStar_Syntax_Print.univ_to_string))
in (FStar_All.pipe_right uu____11641 (FStar_String.concat ", ")))
in (

let ineqs = (

let uu____11651 = (FStar_All.pipe_right (Prims.snd ineqs) (FStar_List.map (fun uu____11663 -> (match (uu____11663) with
| (u1, u2) -> begin
(

let uu____11668 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____11669 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "%s < %s" uu____11668 uu____11669)))
end))))
in (FStar_All.pipe_right uu____11651 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred), (g.FStar_TypeChecker_Env.univ_ineqs))) with
| (FStar_TypeChecker_Common.Trivial, [], (uu____11681, [])) -> begin
"{}"
end
| uu____11694 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____11704 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____11704) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____11705 -> begin
"non-trivial"
end))
end)
in (

let carry = (

let uu____11707 = (FStar_List.map (fun uu____11711 -> (match (uu____11711) with
| (uu____11714, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right uu____11707 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (

let uu____11718 = (ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs)
in (FStar_Util.format4 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n" form carry uu____11718 imps)))))
end))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu____11738; FStar_TypeChecker_Env.implicits = uu____11739} -> begin
true
end
| uu____11753 -> begin
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
| uu____11780 -> begin
(failwith "impossible")
end)
in (

let uu____11781 = (

let uu___167_11782 = g
in (

let uu____11783 = (

let uu____11784 = (

let uu____11785 = (

let uu____11789 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____11789)::[])
in (

let uu____11790 = (

let uu____11797 = (

let uu____11803 = (

let uu____11804 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____11804 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right uu____11803 (fun _0_68 -> FStar_Util.Inl (_0_68))))
in Some (uu____11797))
in (FStar_Syntax_Util.abs uu____11785 f uu____11790)))
in (FStar_All.pipe_left (fun _0_69 -> FStar_TypeChecker_Common.NonTrivial (_0_69)) uu____11784))
in {FStar_TypeChecker_Env.guard_f = uu____11783; FStar_TypeChecker_Env.deferred = uu___167_11782.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___167_11782.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___167_11782.FStar_TypeChecker_Env.implicits}))
in Some (uu____11781)))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___168_11825 = g
in (

let uu____11826 = (

let uu____11827 = (

let uu____11828 = (

let uu____11831 = (

let uu____11832 = (

let uu____11842 = (

let uu____11844 = (FStar_Syntax_Syntax.as_arg e)
in (uu____11844)::[])
in ((f), (uu____11842)))
in FStar_Syntax_Syntax.Tm_app (uu____11832))
in (FStar_Syntax_Syntax.mk uu____11831))
in (uu____11828 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _0_70 -> FStar_TypeChecker_Common.NonTrivial (_0_70)) uu____11827))
in {FStar_TypeChecker_Env.guard_f = uu____11826; FStar_TypeChecker_Env.deferred = uu___168_11825.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___168_11825.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___168_11825.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____11857) -> begin
(failwith "impossible")
end))


let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let uu____11867 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (uu____11867))
end))


let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____11876 -> begin
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

let uu____11907 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = uu____11907; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (((FStar_List.append (Prims.fst g1.FStar_TypeChecker_Env.univ_ineqs) (Prims.fst g2.FStar_TypeChecker_Env.univ_ineqs))), ((FStar_List.append (Prims.snd g1.FStar_TypeChecker_Env.univ_ineqs) (Prims.snd g2.FStar_TypeChecker_Env.univ_ineqs)))); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___169_11945 = g
in (

let uu____11946 = (

let uu____11947 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right uu____11947 (fun _0_71 -> FStar_TypeChecker_Common.NonTrivial (_0_71))))
in {FStar_TypeChecker_Env.guard_f = uu____11946; FStar_TypeChecker_Env.deferred = uu___169_11945.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___169_11945.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___169_11945.FStar_TypeChecker_Env.implicits}))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = (

let uu____11985 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____11985) with
| true -> begin
(

let uu____11986 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (

let uu____11987 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____11986 (rel_to_string rel) uu____11987)))
end
| uu____11988 -> begin
"TOP"
end))
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (

let uu____12007 = (

let uu____12009 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_72 -> Some (_0_72)) uu____12009))
in (FStar_Syntax_Syntax.new_bv uu____12007 t1))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (

let uu____12015 = (

let uu____12017 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _0_73 -> Some (_0_73)) uu____12017))
in (

let uu____12019 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 uu____12015 uu____12019)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (

let probs = (

let uu____12042 = (FStar_Options.eager_inference ())
in (match (uu____12042) with
| true -> begin
(

let uu___170_12043 = probs
in {attempting = uu___170_12043.attempting; wl_deferred = uu___170_12043.wl_deferred; ctr = uu___170_12043.ctr; defer_ok = false; smt_ok = uu___170_12043.smt_ok; tcenv = uu___170_12043.tcenv})
end
| uu____12044 -> begin
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

let uu____12054 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____12054) with
| true -> begin
(

let uu____12055 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string uu____12055))
end
| uu____12056 -> begin
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

let uu____12065 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____12065) with
| true -> begin
(

let uu____12066 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" uu____12066))
end
| uu____12067 -> begin
()
end));
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in ((

let uu____12070 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____12070) with
| true -> begin
(

let uu____12071 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" uu____12071))
end
| uu____12072 -> begin
()
end));
(

let f = (

let uu____12074 = (

let uu____12075 = (FStar_Syntax_Util.unmeta f)
in uu____12075.FStar_Syntax_Syntax.n)
in (match (uu____12074) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____12079 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end))
in (

let uu___171_12080 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = uu___171_12080.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___171_12080.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___171_12080.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(

let uu____12095 = (

let uu____12096 = (

let uu____12097 = (

let uu____12098 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right uu____12098 (fun _0_74 -> FStar_TypeChecker_Common.NonTrivial (_0_74))))
in {FStar_TypeChecker_Env.guard_f = uu____12097; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env uu____12096))
in (FStar_All.pipe_left (fun _0_75 -> Some (_0_75)) uu____12095))
end))


let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> ((

let uu____12122 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12122) with
| true -> begin
(

let uu____12123 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12124 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" uu____12123 uu____12124)))
end
| uu____12125 -> begin
()
end));
(

let prob = (

let uu____12127 = (

let uu____12130 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None uu____12130))
in (FStar_All.pipe_left (fun _0_76 -> FStar_TypeChecker_Common.TProb (_0_76)) uu____12127))
in (

let g = (

let uu____12135 = (

let uu____12137 = (singleton env prob)
in (solve_and_commit env uu____12137 (fun uu____12138 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12135))
in g));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____12152 = (try_teq env t1 t2)
in (match (uu____12152) with
| None -> begin
(

let uu____12154 = (

let uu____12155 = (

let uu____12158 = (FStar_TypeChecker_Err.basic_type_error env None t2 t1)
in (

let uu____12159 = (FStar_TypeChecker_Env.get_range env)
in ((uu____12158), (uu____12159))))
in FStar_Errors.Error (uu____12155))
in (Prims.raise uu____12154))
end
| Some (g) -> begin
((

let uu____12162 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12162) with
| true -> begin
(

let uu____12163 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12164 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____12165 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" uu____12163 uu____12164 uu____12165))))
end
| uu____12166 -> begin
()
end));
g;
)
end)))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 smt_ok -> ((

let uu____12181 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12181) with
| true -> begin
(

let uu____12182 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____12183 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" uu____12182 uu____12183)))
end
| uu____12184 -> begin
()
end));
(

let uu____12185 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____12185) with
| (prob, x) -> begin
(

let g = (

let uu____12193 = (

let uu____12195 = (singleton' env prob smt_ok)
in (solve_and_commit env uu____12195 (fun uu____12196 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12193))
in ((

let uu____12202 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____12202) with
| true -> begin
(

let uu____12203 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____12204 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____12205 = (

let uu____12206 = (FStar_Util.must g)
in (guard_to_string env uu____12206))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" uu____12203 uu____12204 uu____12205))))
end
| uu____12207 -> begin
()
end));
(abstract_guard x g);
))
end));
))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env e t1 t2 -> (

let uu____12230 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12231 = (FStar_TypeChecker_Err.basic_type_error env (Some (e)) t2 t1)
in (FStar_Errors.report uu____12230 uu____12231))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> ((

let uu____12243 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12243) with
| true -> begin
(

let uu____12244 = (FStar_Syntax_Print.comp_to_string c1)
in (

let uu____12245 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" uu____12244 uu____12245)))
end
| uu____12246 -> begin
()
end));
(

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____12248 -> begin
FStar_TypeChecker_Common.SUB
end)
in (

let prob = (

let uu____12250 = (

let uu____12253 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None uu____12253 "sub_comp"))
in (FStar_All.pipe_left (fun _0_77 -> FStar_TypeChecker_Common.CProb (_0_77)) uu____12250))
in (

let uu____12256 = (

let uu____12258 = (singleton env prob)
in (solve_and_commit env uu____12258 (fun uu____12259 -> None)))
in (FStar_All.pipe_left (with_guard env prob) uu____12256))));
))


let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun tx env uu____12278 -> (match (uu____12278) with
| (variables, ineqs) -> begin
(

let fail = (fun u1 u2 -> ((FStar_Unionfind.rollback tx);
(

let uu____12303 = (

let uu____12304 = (

let uu____12307 = (

let uu____12308 = (FStar_Syntax_Print.univ_to_string u1)
in (

let uu____12309 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Universe %s and %s are incompatible" uu____12308 uu____12309)))
in (

let uu____12310 = (FStar_TypeChecker_Env.get_range env)
in ((uu____12307), (uu____12310))))
in FStar_Errors.Error (uu____12304))
in (Prims.raise uu____12303));
))
in (

let equiv = (fun v v' -> (

let uu____12318 = (

let uu____12321 = (FStar_Syntax_Subst.compress_univ v)
in (

let uu____12322 = (FStar_Syntax_Subst.compress_univ v')
in ((uu____12321), (uu____12322))))
in (match (uu____12318) with
| (FStar_Syntax_Syntax.U_unif (v0), FStar_Syntax_Syntax.U_unif (v0')) -> begin
(FStar_Unionfind.equivalent v0 v0')
end
| uu____12330 -> begin
false
end)))
in (

let sols = (FStar_All.pipe_right variables (FStar_List.collect (fun v -> (

let uu____12344 = (FStar_Syntax_Subst.compress_univ v)
in (match (uu____12344) with
| FStar_Syntax_Syntax.U_unif (uu____12348) -> begin
(

let lower_bounds_of_v = (FStar_All.pipe_right ineqs (FStar_List.collect (fun uu____12359 -> (match (uu____12359) with
| (u, v') -> begin
(

let uu____12365 = (equiv v v')
in (match (uu____12365) with
| true -> begin
(

let uu____12367 = (FStar_All.pipe_right variables (FStar_Util.for_some (equiv u)))
in (match (uu____12367) with
| true -> begin
[]
end
| uu____12370 -> begin
(u)::[]
end))
end
| uu____12371 -> begin
[]
end))
end))))
in (

let lb = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max (lower_bounds_of_v)))
in (((lb), (v)))::[]))
end
| uu____12377 -> begin
[]
end)))))
in (

let uu____12380 = (

let wl = (

let uu___172_12383 = (empty_worklist env)
in {attempting = uu___172_12383.attempting; wl_deferred = uu___172_12383.wl_deferred; ctr = uu___172_12383.ctr; defer_ok = false; smt_ok = uu___172_12383.smt_ok; tcenv = uu___172_12383.tcenv})
in (FStar_All.pipe_right sols (FStar_List.map (fun uu____12390 -> (match (uu____12390) with
| (lb, v) -> begin
(

let uu____12395 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl lb v)
in (match (uu____12395) with
| USolved (wl) -> begin
()
end
| uu____12397 -> begin
(fail lb v)
end))
end)))))
in (

let rec check_ineq = (fun uu____12403 -> (match (uu____12403) with
| (u, v) -> begin
(

let u = (FStar_TypeChecker_Normalize.normalize_universe env u)
in (

let v = (FStar_TypeChecker_Normalize.normalize_universe env v)
in (match (((u), (v))) with
| (FStar_Syntax_Syntax.U_zero, uu____12410) -> begin
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
| (FStar_Syntax_Syntax.U_max (us), uu____12426) -> begin
(FStar_All.pipe_right us (FStar_Util.for_all (fun u -> (check_ineq ((u), (v))))))
end
| (uu____12430, FStar_Syntax_Syntax.U_max (vs)) -> begin
(FStar_All.pipe_right vs (FStar_Util.for_some (fun v -> (check_ineq ((u), (v))))))
end
| uu____12435 -> begin
false
end)))
end))
in (

let uu____12438 = (FStar_All.pipe_right ineqs (FStar_Util.for_all (fun uu____12444 -> (match (uu____12444) with
| (u, v) -> begin
(

let uu____12449 = (check_ineq ((u), (v)))
in (match (uu____12449) with
| true -> begin
true
end
| uu____12450 -> begin
((

let uu____12452 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____12452) with
| true -> begin
(

let uu____12453 = (FStar_Syntax_Print.univ_to_string u)
in (

let uu____12454 = (FStar_Syntax_Print.univ_to_string v)
in (FStar_Util.print2 "%s </= %s" uu____12453 uu____12454)))
end
| uu____12455 -> begin
()
end));
false;
)
end))
end))))
in (match (uu____12438) with
| true -> begin
()
end
| uu____12456 -> begin
((

let uu____12458 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____12458) with
| true -> begin
((

let uu____12460 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Partially solved inequality constraints are: %s\n" uu____12460));
(FStar_Unionfind.rollback tx);
(

let uu____12466 = (ineqs_to_string ((variables), (ineqs)))
in (FStar_Util.print1 "Original solved inequality constraints are: %s\n" uu____12466));
)
end
| uu____12471 -> begin
()
end));
(

let uu____12472 = (

let uu____12473 = (

let uu____12476 = (FStar_TypeChecker_Env.get_range env)
in (("Failed to solve universe inequalities for inductives"), (uu____12476)))
in FStar_Errors.Error (uu____12473))
in (Prims.raise uu____12472));
)
end)))))))
end))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list)  ->  Prims.unit = (fun env ineqs -> (

let tx = (FStar_Unionfind.new_transaction ())
in ((solve_universe_inequalities' tx env ineqs);
(FStar_Unionfind.commit tx);
)))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail = (fun uu____12509 -> (match (uu____12509) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Errors.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in ((

let uu____12519 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____12519) with
| true -> begin
(

let uu____12520 = (wl_to_string wl)
in (

let uu____12521 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" uu____12520 uu____12521)))
end
| uu____12531 -> begin
()
end));
(

let g = (

let uu____12533 = (solve_and_commit env wl fail)
in (match (uu____12533) with
| Some ([]) -> begin
(

let uu___173_12540 = g
in {FStar_TypeChecker_Env.guard_f = uu___173_12540.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu___173_12540.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___173_12540.FStar_TypeChecker_Env.implicits})
end
| uu____12543 -> begin
(failwith "impossible: Unexpected deferred constraints remain")
end))
in ((solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___174_12546 = g
in {FStar_TypeChecker_Env.guard_f = uu___174_12546.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___174_12546.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = uu___174_12546.FStar_TypeChecker_Env.implicits});
));
))))


let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun use_env_range_msg env g use_smt -> (

let g = (solve_deferred_constraints env g)
in (

let ret_g = (

let uu___175_12572 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___175_12572.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___175_12572.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___175_12572.FStar_TypeChecker_Env.implicits})
in (

let uu____12573 = (

let uu____12574 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____12574)))
in (match (uu____12573) with
| true -> begin
Some (ret_g)
end
| uu____12576 -> begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
Some (ret_g)
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((

let uu____12580 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Norm")))
in (match (uu____12580) with
| true -> begin
(

let uu____12581 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12582 = (

let uu____12583 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" uu____12583))
in (FStar_Errors.diag uu____12581 uu____12582)))
end
| uu____12584 -> begin
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
| uu____12589 -> begin
((

let uu____12592 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____12592) with
| true -> begin
(

let uu____12593 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____12594 = (

let uu____12595 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" uu____12595))
in (FStar_Errors.diag uu____12593 uu____12594)))
end
| uu____12596 -> begin
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

let uu____12603 = (discharge_guard' None env g true)
in (match (uu____12603) with
| Some (g) -> begin
g
end
| None -> begin
(failwith "Impossible, with use_smt = true, discharge_guard\' should never have returned None")
end)))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (

let uu____12623 = (FStar_Unionfind.find u)
in (match (uu____12623) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| uu____12632 -> begin
false
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____12647 = acc
in (match (uu____12647) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____12658 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd)::tl -> begin
(

let uu____12693 = hd
in (match (uu____12693) with
| (uu____12700, env, u, tm, k, r) -> begin
(

let uu____12706 = (unresolved u)
in (match (uu____12706) with
| true -> begin
(until_fixpoint (((hd)::out), (changed)) tl)
end
| uu____12720 -> begin
(

let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in ((

let uu____12724 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____12724) with
| true -> begin
(

let uu____12725 = (FStar_Syntax_Print.uvar_to_string u)
in (

let uu____12729 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____12730 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" uu____12725 uu____12729 uu____12730))))
end
| uu____12731 -> begin
()
end));
(

let uu____12732 = (env.FStar_TypeChecker_Env.type_of (

let uu___176_12736 = env
in {FStar_TypeChecker_Env.solver = uu___176_12736.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___176_12736.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___176_12736.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___176_12736.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___176_12736.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___176_12736.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___176_12736.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___176_12736.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___176_12736.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___176_12736.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___176_12736.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___176_12736.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___176_12736.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___176_12736.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___176_12736.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___176_12736.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___176_12736.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___176_12736.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___176_12736.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___176_12736.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___176_12736.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___176_12736.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___176_12736.FStar_TypeChecker_Env.qname_and_index}) tm)
in (match (uu____12732) with
| (uu____12737, uu____12738, g) -> begin
(

let g = (match (env.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___177_12741 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___177_12741.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___177_12741.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___177_12741.FStar_TypeChecker_Env.implicits})
end
| uu____12742 -> begin
g
end)
in (

let g' = (

let uu____12744 = (discharge_guard' (Some ((fun uu____12748 -> (FStar_Syntax_Print.term_to_string tm)))) env g true)
in (match (uu____12744) with
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

let uu___178_12763 = g
in (

let uu____12764 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___178_12763.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___178_12763.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___178_12763.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____12764})))))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g = (

let uu____12792 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right uu____12792 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(

let uu____12799 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore uu____12799))
end
| ((reason, uu____12801, uu____12802, e, t, r))::uu____12806 -> begin
(

let uu____12820 = (

let uu____12821 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____12822 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" uu____12821 uu____12822 reason)))
in (FStar_Errors.report r uu____12820))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___179_12829 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___179_12829.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___179_12829.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (([]), ((((u1), (u2)))::[])); FStar_TypeChecker_Env.implicits = uu___179_12829.FStar_TypeChecker_Env.implicits}))


let teq_nosmt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun env t1 t2 -> (

let uu____12847 = (try_teq env t1 t2)
in (match (uu____12847) with
| None -> begin
false
end
| Some (g) -> begin
(

let uu____12850 = (discharge_guard' None env g false)
in (match (uu____12850) with
| Some (uu____12854) -> begin
true
end
| None -> begin
false
end))
end)))






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

let k' = (let _0_226 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _0_226))
in (

let uv = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k'))))) None r)
in (let _0_227 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((uv), (args))))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((_0_227), (uv))))))
end)))

type uvi =
| TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)


let uu___is_TERM : uvi  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TERM (_0) -> begin
true
end
| uu____118 -> begin
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
| uu____144 -> begin
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
| uu____224 -> begin
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
| uu____238 -> begin
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
| uu____255 -> begin
false
end))


let uu___is_CONTRAVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CONTRAVARIANT -> begin
true
end
| uu____259 -> begin
false
end))


let uu___is_INVARIANT : variance  ->  Prims.bool = (fun projectee -> (match (projectee) with
| INVARIANT -> begin
true
end
| uu____263 -> begin
false
end))


type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem


type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem


type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun uu___99_274 -> (match (uu___99_274) with
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

let uu____287 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____287) with
| FStar_Syntax_Syntax.Tm_uvar (u, t) -> begin
(let _0_229 = (FStar_Syntax_Print.uvar_to_string u)
in (let _0_228 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "(%s:%s)" _0_229 _0_228)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty); FStar_Syntax_Syntax.tk = uu____307; FStar_Syntax_Syntax.pos = uu____308; FStar_Syntax_Syntax.vars = uu____309}, args) -> begin
(let _0_232 = (FStar_Syntax_Print.uvar_to_string u)
in (let _0_231 = (FStar_Syntax_Print.term_to_string ty)
in (let _0_230 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "(%s:%s) %s" _0_232 _0_231 _0_230))))
end
| uu____340 -> begin
(FStar_Syntax_Print.term_to_string t)
end)))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env uu___100_346 -> (match (uu___100_346) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _0_247 = (let _0_246 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _0_245 = (let _0_244 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _0_243 = (let _0_242 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _0_241 = (let _0_240 = (let _0_239 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _0_238 = (let _0_237 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _0_236 = (let _0_235 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _0_234 = (let _0_233 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_0_233)::[])
in (_0_235)::_0_234))
in (_0_237)::_0_236))
in (_0_239)::_0_238))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_0_240)
in (_0_242)::_0_241))
in (_0_244)::_0_243))
in (_0_246)::_0_245))
in (FStar_Util.format "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _0_247))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _0_249 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _0_248 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _0_249 (rel_to_string p.FStar_TypeChecker_Common.relation) _0_248)))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env uu___101_359 -> (match (uu___101_359) with
| UNIV (u, t) -> begin
(

let x = (

let uu____363 = (FStar_Options.hide_uvar_nums ())
in (match (uu____363) with
| true -> begin
"?"
end
| uu____364 -> begin
(let _0_250 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _0_250 FStar_Util.string_of_int))
end))
in (let _0_251 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _0_251)))
end
| TERM ((u, uu____367), t) -> begin
(

let x = (

let uu____372 = (FStar_Options.hide_uvar_nums ())
in (match (uu____372) with
| true -> begin
"?"
end
| uu____373 -> begin
(let _0_252 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _0_252 FStar_Util.string_of_int))
end))
in (let _0_253 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _0_253)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _0_254 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _0_254 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (let _0_256 = (let _0_255 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _0_255 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _0_256 (FStar_String.concat ", "))))


let args_to_string = (fun args -> (let _0_257 = (FStar_All.pipe_right args (FStar_List.map (fun uu____414 -> (match (uu____414) with
| (x, uu____418) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _0_257 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> (let _0_258 = (not ((FStar_Options.eager_inference ())))
in {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = _0_258; smt_ok = true; tcenv = env}))


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let uu___128_434 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = uu___128_434.wl_deferred; ctr = uu___128_434.ctr; defer_ok = uu___128_434.defer_ok; smt_ok = smt_ok; tcenv = uu___128_434.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard = (fun env g -> (

let uu___129_459 = (empty_worklist env)
in (let _0_259 = (FStar_List.map Prims.snd g)
in {attempting = _0_259; wl_deferred = uu___129_459.wl_deferred; ctr = uu___129_459.ctr; defer_ok = false; smt_ok = uu___129_459.smt_ok; tcenv = uu___129_459.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let uu___130_471 = wl
in {attempting = uu___130_471.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = uu___130_471.ctr; defer_ok = uu___130_471.defer_ok; smt_ok = uu___130_471.smt_ok; tcenv = uu___130_471.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let uu___131_483 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = uu___131_483.wl_deferred; ctr = uu___131_483.ctr; defer_ok = uu___131_483.defer_ok; smt_ok = uu___131_483.smt_ok; tcenv = uu___131_483.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> ((

let uu____494 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____494) with
| true -> begin
(let _0_260 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _0_260))
end
| uu____495 -> begin
()
end));
Failed (((prob), (reason)));
))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun uu___102_498 -> (match (uu___102_498) with
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

let uu___132_514 = p
in {FStar_TypeChecker_Common.pid = uu___132_514.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = uu___132_514.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___132_514.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___132_514.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___132_514.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___132_514.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___132_514.FStar_TypeChecker_Common.rank}))


let maybe_invert = (fun p -> (match ((p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV)) with
| true -> begin
(invert p)
end
| uu____532 -> begin
p
end))


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___103_535 -> (match (uu___103_535) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_261 -> FStar_TypeChecker_Common.TProb (_0_261)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_262 -> FStar_TypeChecker_Common.CProb (_0_262)))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel uu___104_551 -> (match (uu___104_551) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun uu___105_554 -> (match (uu___105_554) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun uu___106_563 -> (match (uu___106_563) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun uu___107_573 -> (match (uu___107_573) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun uu___108_583 -> (match (uu___108_583) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun uu___109_594 -> (match (uu___109_594) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun uu___110_605 -> (match (uu___110_605) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun uu___111_614 -> (match (uu___111_614) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _0_263 -> FStar_TypeChecker_Common.TProb (_0_263)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _0_264 -> FStar_TypeChecker_Common.CProb (_0_264)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> (let _0_265 = (FStar_All.pipe_right (p_reason p) FStar_List.length)
in (_0_265 = (Prims.parse_int "1"))))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____636 -> ((FStar_Util.incr ctr);
(FStar_ST.read ctr);
)))


let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _0_267 = (next_pid ())
in (let _0_266 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _0_267; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _0_266; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))


let new_problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _0_269 = (next_pid ())
in (let _0_268 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _0_269; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _0_268; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _0_270 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _0_270; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))


let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (

let uu____817 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____817) with
| true -> begin
(let _0_273 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _0_272 = (prob_to_string env d)
in (let _0_271 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _0_273 _0_272 _0_271 s))))
end
| uu____819 -> begin
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
| uu____822 -> begin
(failwith "impossible")
end)
in (

let uu____823 = (match (d) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(let _0_275 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (let _0_274 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((_0_275), (_0_274))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _0_277 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (let _0_276 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((_0_277), (_0_276))))
end)
in (match (uu____823) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___112_842 -> (match (uu___112_842) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| uu____849 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, uu____852), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun uu___113_875 -> (match (uu___113_875) with
| UNIV (uu____877) -> begin
None
end
| TERM ((u, uu____881), t) -> begin
(

let uu____885 = (FStar_Unionfind.equivalent uv u)
in (match (uu____885) with
| true -> begin
Some (t)
end
| uu____890 -> begin
None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun uu___114_904 -> (match (uu___114_904) with
| UNIV (u', t) -> begin
(

let uu____908 = (FStar_Unionfind.equivalent u u')
in (match (uu____908) with
| true -> begin
Some (t)
end
| uu____911 -> begin
None
end))
end
| uu____912 -> begin
None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_Syntax_Subst.compress (let _0_278 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _0_278))))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_Syntax_Subst.compress (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)))


let norm_arg = (fun env t -> (let _0_279 = (sn env (Prims.fst t))
in ((_0_279), ((Prims.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____959 -> (match (uu____959) with
| (x, imp) -> begin
(let _0_281 = (

let uu___133_966 = x
in (let _0_280 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___133_966.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___133_966.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_280}))
in ((_0_281), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
FStar_Syntax_Syntax.U_succ ((aux u))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
FStar_Syntax_Syntax.U_max ((FStar_List.map aux us))
end
| uu____981 -> begin
u
end)))
in (let _0_282 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _0_282))))


let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement = (fun env wl t1 -> (

let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(match (norm) with
| true -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| uu____1087 -> begin
(

let uu____1088 = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (match (uu____1088) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = uu____1100; FStar_Syntax_Syntax.pos = uu____1101; FStar_Syntax_Syntax.vars = uu____1102} -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| tt -> begin
(failwith (let _0_284 = (FStar_Syntax_Print.term_to_string tt)
in (let _0_283 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _0_284 _0_283))))
end))
end)
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(match (norm) with
| true -> begin
((t1), (None))
end
| uu____1155 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (

let uu____1157 = (FStar_Syntax_Subst.compress t1').FStar_Syntax_Syntax.n
in (match (uu____1157) with
| FStar_Syntax_Syntax.Tm_refine (uu____1167) -> begin
(aux true t1')
end
| uu____1172 -> begin
((t1), (None))
end)))
end)
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
((t1), (None))
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(failwith (let _0_286 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_285 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _0_286 _0_285))))
end))
in (let _0_287 = (whnf env t1)
in (aux false _0_287))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _0_289 = (let _0_288 = (empty_worklist env)
in (base_and_refinement env _0_288 t))
in (FStar_All.pipe_right _0_289 Prims.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _0_290 = (FStar_Syntax_Syntax.null_bv t)
in ((_0_290), (FStar_Syntax_Util.t_true))))


let as_refinement = (fun env wl t -> (

let uu____1264 = (base_and_refinement env wl t)
in (match (uu____1264) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement = (fun uu____1323 -> (match (uu____1323) with
| (t_base, refopt) -> begin
(

let uu____1339 = (match (refopt) with
| Some (y, phi) -> begin
((y), (phi))
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (uu____1339) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl uu___115_1363 -> (match (uu___115_1363) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _0_293 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _0_292 = (FStar_Syntax_Print.term_to_string (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs))
in (let _0_291 = (FStar_Syntax_Print.term_to_string (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _0_293 _0_292 (rel_to_string p.FStar_TypeChecker_Common.relation) _0_291))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _0_296 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _0_295 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _0_294 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _0_296 _0_295 (rel_to_string p.FStar_TypeChecker_Common.relation) _0_294))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _0_299 = (let _0_298 = (let _0_297 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____1382 -> (match (uu____1382) with
| (uu____1386, uu____1387, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _0_297))
in (FStar_List.map (wl_prob_to_string wl) _0_298))
in (FStar_All.pipe_right _0_299 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____1404 = (

let uu____1414 = (FStar_Syntax_Subst.compress k).FStar_Syntax_Syntax.n
in (match (uu____1414) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (((FStar_List.length bs) = (FStar_List.length ys))) with
| true -> begin
(let _0_300 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (_0_300)))
end
| uu____1463 -> begin
(

let uu____1464 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____1464) with
| (ys', t, uu____1485) -> begin
(let _0_301 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t))), (_0_301)))
end))
end)
end
| uu____1513 -> begin
(let _0_303 = (let _0_302 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_0_302)))
in ((((ys), (t))), (_0_303)))
end))
in (match (uu____1404) with
| ((ys, t), (xs, c)) -> begin
(match (((FStar_List.length xs) <> (FStar_List.length ys))) with
| true -> begin
(FStar_Syntax_Util.abs ys t (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ([]))))))
end
| uu____1566 -> begin
(

let c = (let _0_304 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp _0_304 c))
in (let _0_308 = (let _0_307 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_305 -> FStar_Util.Inl (_0_305)))
in (FStar_All.pipe_right _0_307 (fun _0_306 -> Some (_0_306))))
in (FStar_Syntax_Util.abs ys t _0_308)))
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

let uu____1613 = (p_guard prob)
in (match (uu____1613) with
| (uu____1616, uv) -> begin
((

let uu____1619 = (FStar_Syntax_Subst.compress uv).FStar_Syntax_Syntax.n
in (match (uu____1619) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi = (u_abs k bs phi)
in ((

let uu____1637 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____1637) with
| true -> begin
(let _0_311 = (FStar_Util.string_of_int (p_pid prob))
in (let _0_310 = (FStar_Syntax_Print.term_to_string uv)
in (let _0_309 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _0_311 _0_310 _0_309))))
end
| uu____1638 -> begin
()
end));
(FStar_Syntax_Util.set_uvar uvar phi);
)))
end
| uu____1641 -> begin
(match ((not (resolve_ok))) with
| true -> begin
(failwith "Impossible: this instance has already been assigned a solution")
end
| uu____1642 -> begin
()
end)
end));
(commit uvis);
(

let uu___134_1644 = wl
in {attempting = uu___134_1644.attempting; wl_deferred = uu___134_1644.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___134_1644.defer_ok; smt_ok = uu___134_1644.smt_ok; tcenv = uu___134_1644.tcenv});
)
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____1657 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____1657) with
| true -> begin
(let _0_314 = (FStar_Util.string_of_int pid)
in (let _0_313 = (let _0_312 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _0_312 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _0_314 _0_313)))
end
| uu____1659 -> begin
()
end));
(commit sol);
(

let uu___135_1661 = wl
in {attempting = uu___135_1661.attempting; wl_deferred = uu___135_1661.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___135_1661.defer_ok; smt_ok = uu___135_1661.smt_ok; tcenv = uu___135_1661.tcenv});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard = (fun t g -> (match (((t), (g))) with
| (uu____1690, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some ((FStar_Syntax_Util.mk_conj t f))
end))
in ((

let uu____1701 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____1701) with
| true -> begin
(let _0_317 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _0_316 = (let _0_315 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _0_315 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _0_317 _0_316)))
end
| uu____1703 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
)))


let rec occurs = (fun wl uk t -> (let _0_319 = (let _0_318 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _0_318 FStar_Util.set_elements))
in (FStar_All.pipe_right _0_319 (FStar_Util.for_some (fun uu____1742 -> (match (uu____1742) with
| (uv, uu____1750) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (not ((occurs wl uk t)))
in (

let msg = (match (occurs_ok) with
| true -> begin
None
end
| uu____1797 -> begin
Some ((let _0_321 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _0_320 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _0_321 _0_320))))
end)
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let uu____1848 = (occurs_check env wl uk t)
in (match (uu____1848) with
| (occurs_ok, msg) -> begin
(let _0_322 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (_0_322), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set v1)
in (

let uu____1928 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____1952 uu____1953 -> (match (((uu____1952), (uu____1953))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____1996 = (let _0_323 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _0_323))
in (match (uu____1996) with
| true -> begin
((isect), (isect_set))
end
| uu____2007 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____2010 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____2010) with
| true -> begin
(let _0_324 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (_0_324)))
end
| uu____2023 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (uu____1928) with
| (isect, uu____2037) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____2086 uu____2087 -> (match (((uu____2086), (uu____2087))) with
| ((a, uu____2097), (b, uu____2099)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(

let uu____2143 = (FStar_All.pipe_right seen (FStar_Util.for_some (fun uu____2149 -> (match (uu____2149) with
| (b, uu____2153) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end))))
in (match (uu____2143) with
| true -> begin
None
end
| uu____2159 -> begin
Some (((a), ((Prims.snd hd))))
end))
end
| uu____2162 -> begin
None
end)))


let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| (hd)::rest -> begin
(

let uu____2205 = (pat_var_opt env seen hd)
in (match (uu____2205) with
| None -> begin
((

let uu____2213 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____2213) with
| true -> begin
(let _0_325 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _0_325))
end
| uu____2214 -> begin
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

let uu____2225 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____2225) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
true
end
| uu____2239 -> begin
false
end)))


let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = uu____2318; FStar_Syntax_Syntax.pos = uu____2319; FStar_Syntax_Syntax.vars = uu____2320}, args) -> begin
((t), (uv), (k), (args))
end
| uu____2361 -> begin
(failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let uu____2415 = (destruct_flex_t t)
in (match (uu____2415) with
| (t, uv, k, args) -> begin
(

let uu____2483 = (pat_vars env [] args)
in (match (uu____2483) with
| Some (vars) -> begin
((((t), (uv), (k), (args))), (Some (vars)))
end
| uu____2539 -> begin
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
| uu____2587 -> begin
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
| uu____2610 -> begin
false
end))


let uu___is_FullMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullMatch -> begin
true
end
| uu____2614 -> begin
false
end))


let head_match : match_result  ->  match_result = (fun uu___116_2617 -> (match (uu___116_2617) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____2626 -> begin
HeadMatch
end))


let fv_delta_depth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.delta_depth = (fun env fv -> (match (fv.FStar_Syntax_Syntax.fv_delta) with
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(match ((env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)) with
| true -> begin
d
end
| uu____2638 -> begin
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
| uu____2711 -> begin
MisMatch (((None), (None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____2716 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____2716) with
| true -> begin
FullMatch
end
| uu____2717 -> begin
MisMatch (((Some ((fv_delta_depth env f))), (Some ((fv_delta_depth env g)))))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____2721), FStar_Syntax_Syntax.Tm_uinst (g, uu____2723)) -> begin
(let _0_326 = (head_matches env f g)
in (FStar_All.pipe_right _0_326 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(match ((c = d)) with
| true -> begin
FullMatch
end
| uu____2734 -> begin
MisMatch (((None), (None)))
end)
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, uu____2738), FStar_Syntax_Syntax.Tm_uvar (uv', uu____2740)) -> begin
(

let uu____2765 = (FStar_Unionfind.equivalent uv uv')
in (match (uu____2765) with
| true -> begin
FullMatch
end
| uu____2769 -> begin
MisMatch (((None), (None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____2773), FStar_Syntax_Syntax.Tm_refine (y, uu____2775)) -> begin
(let _0_327 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _0_327 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____2785), uu____2786) -> begin
(let _0_328 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _0_328 head_match))
end
| (uu____2791, FStar_Syntax_Syntax.Tm_refine (x, uu____2793)) -> begin
(let _0_329 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _0_329 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, uu____2803), FStar_Syntax_Syntax.Tm_app (head', uu____2805)) -> begin
(let _0_330 = (head_matches env head head')
in (FStar_All.pipe_right _0_330 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head, uu____2835), uu____2836) -> begin
(let _0_331 = (head_matches env head t2)
in (FStar_All.pipe_right _0_331 head_match))
end
| (uu____2851, FStar_Syntax_Syntax.Tm_app (head, uu____2853)) -> begin
(let _0_332 = (head_matches env t1 head)
in (FStar_All.pipe_right _0_332 head_match))
end
| uu____2868 -> begin
MisMatch ((let _0_334 = (delta_depth_of_term env t1)
in (let _0_333 = (delta_depth_of_term env t2)
in ((_0_334), (_0_333)))))
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let uu____2905 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____2905) with
| (head, uu____2917) -> begin
(

let uu____2932 = (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
in (match (uu____2932) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____2935 = (let _0_335 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _0_335 FStar_Option.isSome))
in (match (uu____2935) with
| true -> begin
(let _0_337 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right _0_337 (fun _0_336 -> Some (_0_336))))
end
| uu____2947 -> begin
None
end))
end
| uu____2948 -> begin
None
end))
end)))
in (

let success = (fun d r t1 t2 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
Some (((t1), (t2)))
end
| uu____2975 -> begin
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
| uu____3027 -> begin
(

let uu____3028 = (let _0_339 = (maybe_inline t1)
in (let _0_338 = (maybe_inline t2)
in ((_0_339), (_0_338))))
in (match (uu____3028) with
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

let uu____3056 = (FStar_TypeChecker_Common.decr_delta_depth d1)
in (match (uu____3056) with
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

let uu____3071 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in ((t1'), (t2)))
end
| uu____3077 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (let _0_340 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in ((t1), (_0_340))))
end)
in (match (uu____3071) with
| (t1, t2) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t1 t2)
end)))
end
| MisMatch (uu____3086) -> begin
(fail r)
end
| uu____3091 -> begin
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
| uu____3116 -> begin
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
| uu____3146 -> begin
false
end))


let __proj__C__item___0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_0) -> begin
_0
end))


type tcs =
tc Prims.list


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____3161 = (FStar_Syntax_Util.type_u ())
in (match (uu____3161) with
| (t, uu____3165) -> begin
(Prims.fst (new_uvar r binders t))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (let _0_341 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_341 Prims.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (

let uu____3211 = (head_matches env t t')
in (match (uu____3211) with
| MisMatch (uu____3212) -> begin
false
end
| uu____3217 -> begin
true
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(

let rebuild = (fun args' -> (

let args = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((uu____3277, imp), T (t, uu____3280)) -> begin
((t), (imp))
end
| uu____3297 -> begin
(failwith "Bad reconstruction")
end)) args args')
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), (args))))) None t.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun uu____3341 -> (match (uu____3341) with
| (t, uu____3349) -> begin
((None), (INVARIANT), (T (((t), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let fail = (fun uu____3382 -> (failwith "Bad reconstruction"))
in (

let uu____3383 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3383) with
| (bs, c) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs tcs -> (match (((bs), (tcs))) with
| (((x, imp))::bs, (T (t, uu____3436))::tcs) -> begin
(aux (((((

let uu___136_3458 = x
in {FStar_Syntax_Syntax.ppname = uu___136_3458.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___136_3458.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp)))::out) bs tcs)
end
| ([], (C (c))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| uu____3468 -> begin
(failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (

let rec decompose = (fun out uu___117_3499 -> (match (uu___117_3499) with
| [] -> begin
(FStar_List.rev ((((None), (COVARIANT), (C (c))))::out))
end
| (hd)::rest -> begin
(decompose ((((Some (hd)), (CONTRAVARIANT), (T ((((Prims.fst hd).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (let _0_342 = (decompose [] bs)
in ((rebuild), (matches), (_0_342)))))
end)))
end
| uu____3582 -> begin
(

let rebuild = (fun uu___118_3587 -> (match (uu___118_3587) with
| [] -> begin
t
end
| uu____3589 -> begin
(failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t -> true)), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun uu___119_3608 -> (match (uu___119_3608) with
| T (t, uu____3610) -> begin
t
end
| uu____3619 -> begin
(failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun uu___120_3622 -> (match (uu___120_3622) with
| T (t, uu____3624) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| uu____3633 -> begin
(failwith "Impossible")
end))


let imitation_sub_probs = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope args q -> (match (q) with
| (uu____3714, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope r)
in (

let uu____3733 = (new_uvar r scope k)
in (match (uu____3733) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| uu____3745 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) None r)
end)
in (let _0_345 = (let _0_344 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _0_343 -> FStar_TypeChecker_Common.TProb (_0_343)) _0_344))
in ((T (((gi_xs), (mk_kind)))), (_0_345))))
end)))
end
| (uu____3766, uu____3767, C (uu____3768)) -> begin
(failwith "impos")
end))
in (

let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs -> begin
(

let uu____3855 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.tk = uu____3866; FStar_Syntax_Syntax.pos = uu____3867; FStar_Syntax_Syntax.vars = uu____3868})) -> begin
(

let uu____3883 = (sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____3883) with
| (T (gi_xs, uu____3899), prob) -> begin
(let _0_348 = (let _0_347 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_346 -> C (_0_346)) _0_347))
in ((_0_348), ((prob)::[])))
end
| uu____3910 -> begin
(failwith "impossible")
end))
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.tk = uu____3920; FStar_Syntax_Syntax.pos = uu____3921; FStar_Syntax_Syntax.vars = uu____3922})) -> begin
(

let uu____3937 = (sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____3937) with
| (T (gi_xs, uu____3953), prob) -> begin
(let _0_351 = (let _0_350 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_349 -> C (_0_349)) _0_350))
in ((_0_351), ((prob)::[])))
end
| uu____3964 -> begin
(failwith "impossible")
end))
end
| (uu____3970, uu____3971, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = uu____3973; FStar_Syntax_Syntax.pos = uu____3974; FStar_Syntax_Syntax.vars = uu____3975})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((None), (INVARIANT), (T ((((Prims.fst t)), (generic_kind))))))))
in (

let components = (((None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let uu____4049 = (let _0_352 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _0_352 FStar_List.unzip))
in (match (uu____4049) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (let _0_357 = (let _0_356 = (let _0_353 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _0_353 un_T))
in (let _0_355 = (let _0_354 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _0_354 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _0_356; FStar_Syntax_Syntax.effect_args = _0_355; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _0_357))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| uu____4082 -> begin
(

let uu____4089 = (sub_prob scope args q)
in (match (uu____4089) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (uu____3855) with
| (tc, probs) -> begin
(

let uu____4107 = (match (q) with
| (Some (b), uu____4133, uu____4134) -> begin
(let _0_359 = (let _0_358 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_0_358)::args)
in ((Some (b)), ((b)::scope), (_0_359)))
end
| uu____4157 -> begin
((None), (scope), (args))
end)
in (match (uu____4107) with
| (bopt, scope, args) -> begin
(

let uu____4200 = (aux scope args qs)
in (match (uu____4200) with
| (sub_probs, tcs, f) -> begin
(

let f = (match (bopt) with
| None -> begin
(FStar_Syntax_Util.mk_conj_l (let _0_360 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_0_360))
end
| Some (b) -> begin
(FStar_Syntax_Util.mk_conj_l (let _0_362 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _0_361 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_0_362)::_0_361)))
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

let uu___137_4284 = p
in (let _0_364 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _0_363 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___137_4284.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _0_364; FStar_TypeChecker_Common.relation = uu___137_4284.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _0_363; FStar_TypeChecker_Common.element = uu___137_4284.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___137_4284.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___137_4284.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___137_4284.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___137_4284.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___137_4284.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _0_366 = (compress_tprob wl p)
in (FStar_All.pipe_right _0_366 (fun _0_365 -> FStar_TypeChecker_Common.TProb (_0_365))))
end
| FStar_TypeChecker_Common.CProb (uu____4298) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (let _0_367 = (compress_prob wl pr)
in (FStar_All.pipe_right _0_367 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____4317 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____4317) with
| (lh, uu____4330) -> begin
(

let uu____4345 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____4345) with
| (rh, uu____4358) -> begin
(

let uu____4373 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____4382), FStar_Syntax_Syntax.Tm_uvar (uu____4383)) -> begin
((flex_flex), (tp))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when ((tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____4408), uu____4409) -> begin
(

let uu____4418 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (uu____4418) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((flex_rigid), (tp))
end
| uu____4458 -> begin
(

let rank = (

let uu____4465 = (is_top_level_prob prob)
in (match (uu____4465) with
| true -> begin
flex_refine
end
| uu____4466 -> begin
flex_refine_inner
end))
in (let _0_369 = (

let uu___138_4469 = tp
in (let _0_368 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___138_4469.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___138_4469.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___138_4469.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _0_368; FStar_TypeChecker_Common.element = uu___138_4469.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___138_4469.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___138_4469.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___138_4469.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___138_4469.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___138_4469.FStar_TypeChecker_Common.rank}))
in ((rank), (_0_369))))
end)
end))
end
| (uu____4479, FStar_Syntax_Syntax.Tm_uvar (uu____4480)) -> begin
(

let uu____4489 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (uu____4489) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((rigid_flex), (tp))
end
| uu____4529 -> begin
(let _0_371 = (

let uu___139_4539 = tp
in (let _0_370 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___139_4539.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _0_370; FStar_TypeChecker_Common.relation = uu___139_4539.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___139_4539.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___139_4539.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___139_4539.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___139_4539.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___139_4539.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___139_4539.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___139_4539.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (_0_371)))
end)
end))
end
| (uu____4551, uu____4552) -> begin
((rigid_rigid), (tp))
end)
in (match (uu____4373) with
| (rank, tp) -> begin
(let _0_373 = (FStar_All.pipe_right (

let uu___140_4565 = tp
in {FStar_TypeChecker_Common.pid = uu___140_4565.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___140_4565.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___140_4565.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___140_4565.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___140_4565.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___140_4565.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___140_4565.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___140_4565.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___140_4565.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _0_372 -> FStar_TypeChecker_Common.TProb (_0_372)))
in ((rank), (_0_373)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _0_375 = (FStar_All.pipe_right (

let uu___141_4573 = cp
in {FStar_TypeChecker_Common.pid = uu___141_4573.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___141_4573.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___141_4573.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___141_4573.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___141_4573.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___141_4573.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___141_4573.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___141_4573.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___141_4573.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _0_374 -> FStar_TypeChecker_Common.CProb (_0_374)))
in ((rigid_rigid), (_0_375)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun uu____4605 probs -> (match (uu____4605) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
((min), (out), (min_rank))
end
| (hd)::tl -> begin
(

let uu____4635 = (rank wl hd)
in (match (uu____4635) with
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
| uu____4660 -> begin
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
| uu____4676 -> begin
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
| uu____4700 -> begin
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
| uu____4712 -> begin
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
| uu____4724 -> begin
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

let uu____4761 = (FStar_Syntax_Util.univ_kernel u)
in (match (uu____4761) with
| (k, uu____4765) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| uu____4770 -> begin
false
end)
end)))))
end
| uu____4771 -> begin
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

let uu____4814 = (really_solve_universe_eq orig wl u1 u2)
in (match (uu____4814) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed -> begin
failed
end))
end
| uu____4817 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end
| uu____4822 -> begin
UFailed ((let _0_377 = (FStar_Syntax_Print.univ_to_string u1)
in (let _0_376 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _0_377 _0_376))))
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

let uu____4839 = (really_solve_universe_eq orig wl u u')
in (match (uu____4839) with
| USolved (wl) -> begin
(aux wl us)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____4842 -> begin
UFailed ((let _0_379 = (FStar_Syntax_Print.univ_to_string u1)
in (let _0_378 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _0_379 _0_378 msg))))
end))
in (match (((u1), (u2))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(failwith (let _0_381 = (FStar_Syntax_Print.univ_to_string u1)
in (let _0_380 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" _0_381 _0_380))))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((x.FStar_Ident.idText = y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____4853 -> begin
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

let uu____4862 = (FStar_Unionfind.equivalent v1 v2)
in (match (uu____4862) with
| true -> begin
USolved (wl)
end
| uu____4864 -> begin
(

let wl = (extend_solution orig ((UNIV (((v1), (u2))))::[]) wl)
in USolved (wl))
end))
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(

let u = (norm_univ wl u)
in (

let uu____4875 = (occurs_univ v1 u)
in (match (uu____4875) with
| true -> begin
(let _0_384 = (let _0_383 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _0_382 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _0_383 _0_382)))
in (try_umax_components u1 u2 _0_384))
end
| uu____4876 -> begin
USolved ((extend_solution orig ((UNIV (((v1), (u))))::[]) wl))
end)))
end
| ((FStar_Syntax_Syntax.U_max (_), _)) | ((_, FStar_Syntax_Syntax.U_max (_))) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____4883 -> begin
(

let u1 = (norm_univ wl u1)
in (

let u2 = (norm_univ wl u2)
in (

let uu____4886 = (FStar_Syntax_Util.eq_univs u1 u2)
in (match (uu____4886) with
| true -> begin
USolved (wl)
end
| uu____4887 -> begin
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
| uu____4908 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders = (fun bc1 bc2 -> (

let uu____4957 = bc1
in (match (uu____4957) with
| (bs1, mk_cod1) -> begin
(

let uu____4982 = bc2
in (match (uu____4982) with
| (bs2, mk_cod2) -> begin
(

let curry = (fun n bs mk_cod -> (

let uu____5029 = (FStar_Util.first_N n bs)
in (match (uu____5029) with
| (bs, rest) -> begin
(let _0_385 = (mk_cod rest)
in ((bs), (_0_385)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(let _0_389 = (let _0_386 = (mk_cod1 [])
in ((bs1), (_0_386)))
in (let _0_388 = (let _0_387 = (mk_cod2 [])
in ((bs2), (_0_387)))
in ((_0_389), (_0_388))))
end
| uu____5068 -> begin
(match ((l1 > l2)) with
| true -> begin
(let _0_392 = (curry l2 bs1 mk_cod1)
in (let _0_391 = (let _0_390 = (mk_cod2 [])
in ((bs2), (_0_390)))
in ((_0_392), (_0_391))))
end
| uu____5092 -> begin
(let _0_395 = (let _0_393 = (mk_cod1 [])
in ((bs1), (_0_393)))
in (let _0_394 = (curry l1 bs2 mk_cod2)
in ((_0_395), (_0_394))))
end)
end))))
end))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____5194 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5194) with
| true -> begin
(let _0_396 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _0_396))
end
| uu____5195 -> begin
()
end));
(

let uu____5196 = (next_prob probs)
in (match (uu____5196) with
| (Some (hd), tl, rank) -> begin
(

let probs = (

let uu___142_5209 = probs
in {attempting = tl; wl_deferred = uu___142_5209.wl_deferred; ctr = uu___142_5209.ctr; defer_ok = uu___142_5209.defer_ok; smt_ok = uu___142_5209.smt_ok; tcenv = uu___142_5209.tcenv})
in (match (hd) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match ((((not (probs.defer_ok)) && (flex_refine_inner <= rank)) && (rank <= flex_rigid))) with
| true -> begin
(

let uu____5216 = (solve_flex_rigid_join env tp probs)
in (match (uu____5216) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end))
end
| uu____5219 -> begin
(match ((((not (probs.defer_ok)) && (rigid_flex <= rank)) && (rank <= refine_flex))) with
| true -> begin
(

let uu____5220 = (solve_rigid_flex_meet env tp probs)
in (match (uu____5220) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end))
end
| uu____5223 -> begin
(solve_t' env (maybe_invert tp) probs)
end)
end)
end))
end
| (None, uu____5224, uu____5225) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| uu____5234 -> begin
(

let uu____5239 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____5267 -> (match (uu____5267) with
| (c, uu____5272, uu____5273) -> begin
(c < probs.ctr)
end))))
in (match (uu____5239) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
Success ((FStar_List.map (fun uu____5300 -> (match (uu____5300) with
| (uu____5306, x, y) -> begin
((x), (y))
end)) probs.wl_deferred))
end
| uu____5309 -> begin
(let _0_398 = (

let uu___143_5314 = probs
in (let _0_397 = (FStar_All.pipe_right attempt (FStar_List.map (fun uu____5323 -> (match (uu____5323) with
| (uu____5327, uu____5328, y) -> begin
y
end))))
in {attempting = _0_397; wl_deferred = rest; ctr = uu___143_5314.ctr; defer_ok = uu___143_5314.defer_ok; smt_ok = uu___143_5314.smt_ok; tcenv = uu___143_5314.tcenv}))
in (solve env _0_398))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____5335 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____5335) with
| USolved (wl) -> begin
(let _0_399 = (solve_prob orig None [] wl)
in (solve env _0_399))
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

let uu____5370 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____5370) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____5373 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t1 = (whnf env t1)
in (

let t2 = (whnf env t2)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = uu____5381; FStar_Syntax_Syntax.pos = uu____5382; FStar_Syntax_Syntax.vars = uu____5383}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = uu____5386; FStar_Syntax_Syntax.pos = uu____5387; FStar_Syntax_Syntax.vars = uu____5388}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____5404 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____5412 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____5412) with
| true -> begin
(let _0_400 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _0_400 msg))
end
| uu____5413 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____5414 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> ((

let uu____5420 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5420) with
| true -> begin
(let _0_401 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" _0_401))
end
| uu____5421 -> begin
()
end));
(

let uu____5422 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____5422) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let uu____5464 = (head_matches_delta env () t1 t2)
in (match (uu____5464) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (uu____5486) -> begin
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

let uu____5512 = (match (ts) with
| Some (t1, t2) -> begin
(let _0_403 = (FStar_Syntax_Subst.compress t1)
in (let _0_402 = (FStar_Syntax_Subst.compress t2)
in ((_0_403), (_0_402))))
end
| None -> begin
(let _0_405 = (FStar_Syntax_Subst.compress t1)
in (let _0_404 = (FStar_Syntax_Subst.compress t2)
in ((_0_405), (_0_404))))
end)
in (match (uu____5512) with
| (t1, t2) -> begin
(

let eq_prob = (fun t1 t2 -> (let _0_407 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _0_406 -> FStar_TypeChecker_Common.TProb (_0_406)) _0_407)))
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
Some ((let _0_411 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((let _0_408 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (_0_408)))))) None t1.FStar_Syntax_Syntax.pos)
in (let _0_410 = (let _0_409 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (_0_409)::[])
in ((_0_411), (_0_410)))))
end
| (uu____5586, FStar_Syntax_Syntax.Tm_refine (x, uu____5588)) -> begin
Some ((let _0_413 = (let _0_412 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (_0_412)::[])
in ((t1), (_0_413))))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____5598), uu____5599) -> begin
Some ((let _0_415 = (let _0_414 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (_0_414)::[])
in ((t2), (_0_415))))
end
| uu____5608 -> begin
(

let uu____5611 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____5611) with
| (head1, uu____5626) -> begin
(

let uu____5641 = (FStar_Syntax_Util.un_uinst head1).FStar_Syntax_Syntax.n
in (match (uu____5641) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____5646; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (i); FStar_Syntax_Syntax.fv_qual = uu____5648}) -> begin
(

let prev = (match ((i > (Prims.parse_int "1"))) with
| true -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i - (Prims.parse_int "1")))
end
| uu____5654 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t1)
in (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t2)
in (disjoin t1 t2))))
end
| uu____5657 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____5666) -> begin
(

let uu____5679 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___121_5688 -> (match (uu___121_5688) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(

let uu____5693 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____5693) with
| (u', uu____5704) -> begin
(

let uu____5719 = (whnf env u').FStar_Syntax_Syntax.n
in (match (uu____5719) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____5721) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____5737 -> begin
false
end))
end))
end
| uu____5738 -> begin
false
end)
end
| uu____5740 -> begin
false
end))))
in (match (uu____5679) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun uu____5761 tps -> (match (uu____5761) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(

let uu____5788 = (let _0_416 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound _0_416))
in (match (uu____5788) with
| Some (bound, sub) -> begin
(make_lower_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end))
end
| uu____5811 -> begin
None
end)
end))
in (

let uu____5816 = (let _0_418 = (let _0_417 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((_0_417), ([])))
in (make_lower_bound _0_418 lower_bounds))
in (match (uu____5816) with
| None -> begin
((

let uu____5827 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5827) with
| true -> begin
(FStar_Util.print_string "No lower bounds\n")
end
| uu____5828 -> begin
()
end));
None;
)
end
| Some (lhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in ((

let uu____5840 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5840) with
| true -> begin
(

let wl' = (

let uu___144_5842 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___144_5842.wl_deferred; ctr = uu___144_5842.ctr; defer_ok = uu___144_5842.defer_ok; smt_ok = uu___144_5842.smt_ok; tcenv = uu___144_5842.tcenv})
in (let _0_419 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" _0_419)))
end
| uu____5843 -> begin
()
end));
(

let uu____5844 = (solve_t env eq_prob (

let uu___145_5845 = wl
in {attempting = sub_probs; wl_deferred = uu___145_5845.wl_deferred; ctr = uu___145_5845.ctr; defer_ok = uu___145_5845.defer_ok; smt_ok = uu___145_5845.smt_ok; tcenv = uu___145_5845.tcenv}))
in (match (uu____5844) with
| Success (uu____5847) -> begin
(

let wl = (

let uu___146_5849 = wl
in {attempting = rest; wl_deferred = uu___146_5849.wl_deferred; ctr = uu___146_5849.ctr; defer_ok = uu___146_5849.defer_ok; smt_ok = uu___146_5849.smt_ok; tcenv = uu___146_5849.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let uu____5851 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| uu____5854 -> begin
None
end));
))
end)))
end))
end
| uu____5855 -> begin
(failwith "Impossible: Not a rigid-flex")
end)))
end));
))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> ((

let uu____5862 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5862) with
| true -> begin
(let _0_420 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _0_420))
end
| uu____5863 -> begin
()
end));
(

let uu____5864 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____5864) with
| (u, args) -> begin
(

let uu____5891 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (uu____5891) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(

let max = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____5910 -> begin
i
end))
in (

let base_types_match = (fun t1 t2 -> (

let uu____5922 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____5922) with
| (h1, args1) -> begin
(

let uu____5950 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____5950) with
| (h2, uu____5963) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
(

let uu____5982 = (FStar_Syntax_Syntax.fv_eq tc1 tc2)
in (match (uu____5982) with
| true -> begin
(match (((FStar_List.length args1) = (Prims.parse_int "0"))) with
| true -> begin
Some ([])
end
| uu____5994 -> begin
Some ((let _0_423 = (let _0_422 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_421 -> FStar_TypeChecker_Common.TProb (_0_421)) _0_422))
in (_0_423)::[]))
end)
end
| uu____5998 -> begin
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
| uu____6013 -> begin
Some ((let _0_426 = (let _0_425 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_424 -> FStar_TypeChecker_Common.TProb (_0_424)) _0_425))
in (_0_426)::[]))
end)
end
| uu____6017 -> begin
None
end)
end
| uu____6019 -> begin
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
in Some ((let _0_428 = (let _0_427 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _0_427))
in ((_0_428), (m))))))))
end))
end
| (uu____6093, FStar_Syntax_Syntax.Tm_refine (y, uu____6095)) -> begin
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
| (FStar_Syntax_Syntax.Tm_refine (x, uu____6127), uu____6128) -> begin
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
| uu____6159 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____6193) -> begin
(

let uu____6206 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___122_6215 -> (match (uu___122_6215) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(

let uu____6220 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____6220) with
| (u', uu____6231) -> begin
(

let uu____6246 = (whnf env u').FStar_Syntax_Syntax.n
in (match (uu____6246) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____6248) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____6264 -> begin
false
end))
end))
end
| uu____6265 -> begin
false
end)
end
| uu____6267 -> begin
false
end))))
in (match (uu____6206) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun uu____6292 tps -> (match (uu____6292) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(

let uu____6333 = (let _0_429 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _0_429))
in (match (uu____6333) with
| Some (bound, sub) -> begin
(make_upper_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end))
end
| uu____6372 -> begin
None
end)
end))
in (

let uu____6379 = (let _0_431 = (let _0_430 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((_0_430), ([])))
in (make_upper_bound _0_431 upper_bounds))
in (match (uu____6379) with
| None -> begin
((

let uu____6394 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6394) with
| true -> begin
(FStar_Util.print_string "No upper bounds\n")
end
| uu____6395 -> begin
()
end));
None;
)
end
| Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in ((

let uu____6413 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6413) with
| true -> begin
(

let wl' = (

let uu___147_6415 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___147_6415.wl_deferred; ctr = uu___147_6415.ctr; defer_ok = uu___147_6415.defer_ok; smt_ok = uu___147_6415.smt_ok; tcenv = uu___147_6415.tcenv})
in (let _0_432 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _0_432)))
end
| uu____6416 -> begin
()
end));
(

let uu____6417 = (solve_t env eq_prob (

let uu___148_6418 = wl
in {attempting = sub_probs; wl_deferred = uu___148_6418.wl_deferred; ctr = uu___148_6418.ctr; defer_ok = uu___148_6418.defer_ok; smt_ok = uu___148_6418.smt_ok; tcenv = uu___148_6418.tcenv}))
in (match (uu____6417) with
| Success (uu____6420) -> begin
(

let wl = (

let uu___149_6422 = wl
in {attempting = rest; wl_deferred = uu___149_6422.wl_deferred; ctr = uu___149_6422.ctr; defer_ok = uu___149_6422.defer_ok; smt_ok = uu___149_6422.smt_ok; tcenv = uu___149_6422.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let uu____6424 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| uu____6427 -> begin
None
end));
))
end)))
end))
end
| uu____6428 -> begin
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

let uu____6493 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6493) with
| true -> begin
(let _0_433 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _0_433))
end
| uu____6494 -> begin
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

let uu___150_6525 = hd1
in (let _0_434 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___150_6525.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___150_6525.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_434}))
in (

let hd2 = (

let uu___151_6527 = hd2
in (let _0_435 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___151_6527.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___151_6527.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_435}))
in (

let prob = (let _0_438 = (let _0_437 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _0_437 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _0_436 -> FStar_TypeChecker_Common.TProb (_0_436)) _0_438))
in (

let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (

let subst = (let _0_439 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd1))))::_0_439)
in (

let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (

let uu____6537 = (aux ((((hd1), (imp)))::scope) env subst xs ys)
in (match (uu____6537) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi = (let _0_441 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _0_440 = (FStar_Syntax_Util.close_forall ((((hd1), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj _0_441 _0_440)))
in ((

let uu____6562 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6562) with
| true -> begin
(let _0_443 = (FStar_Syntax_Print.term_to_string phi)
in (let _0_442 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _0_443 _0_442)))
end
| uu____6563 -> begin
()
end));
FStar_Util.Inl ((((prob)::sub_probs), (phi)));
))
end
| fail -> begin
fail
end))))))))
end
| uu____6577 -> begin
FStar_Util.Inr ("arity or argument-qualifier mismatch")
end))
in (

let scope = (p_scope orig)
in (

let uu____6583 = (aux scope env [] bs1 bs2)
in (match (uu____6583) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end)))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _0_444 = (compress_tprob wl problem)
in (solve_t' env _0_444 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (

let uu____6631 = (head_matches_delta env wl t1 t2)
in (match (uu____6631) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____6648), uu____6649) -> begin
(

let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____6671 -> begin
false
end))
in (match ((((may_relate head1) || (may_relate head2)) && wl.smt_ok)) with
| true -> begin
(

let guard = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end
| uu____6677 -> begin
(

let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(

let x = (FStar_Syntax_Syntax.new_bv None t1)
in (let _0_446 = (let _0_445 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _0_445 t2))
in (FStar_Syntax_Util.mk_forall x _0_446)))
end))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB)) with
| true -> begin
(has_type_guard t1 t2)
end
| uu____6693 -> begin
(has_type_guard t2 t1)
end))
end)
in (let _0_447 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _0_447)))
end
| uu____6696 -> begin
(giveup env "head mismatch" orig)
end))
end
| (uu____6697, Some (t1, t2)) -> begin
(solve_t env (

let uu___152_6705 = problem
in {FStar_TypeChecker_Common.pid = uu___152_6705.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___152_6705.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___152_6705.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___152_6705.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___152_6705.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___152_6705.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___152_6705.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___152_6705.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____6706, None) -> begin
((

let uu____6713 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6713) with
| true -> begin
(let _0_451 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_450 = (FStar_Syntax_Print.tag_of_term t1)
in (let _0_449 = (FStar_Syntax_Print.term_to_string t2)
in (let _0_448 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _0_451 _0_450 _0_449 _0_448)))))
end
| uu____6714 -> begin
()
end));
(

let uu____6715 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____6715) with
| (head1, args1) -> begin
(

let uu____6741 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____6741) with
| (head2, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((nargs <> (FStar_List.length args2))) with
| true -> begin
(let _0_456 = (let _0_455 = (FStar_Syntax_Print.term_to_string head1)
in (let _0_454 = (args_to_string args1)
in (let _0_453 = (FStar_Syntax_Print.term_to_string head2)
in (let _0_452 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _0_455 _0_454 _0_453 _0_452)))))
in (giveup env _0_456 orig))
end
| uu____6781 -> begin
(

let uu____6782 = ((nargs = (Prims.parse_int "0")) || (let _0_457 = (FStar_Syntax_Util.eq_args args1 args2)
in (_0_457 = FStar_Syntax_Util.Equal)))
in (match (uu____6782) with
| true -> begin
(

let uu____6785 = (solve_maybe_uinsts env orig head1 head2 wl)
in (match (uu____6785) with
| USolved (wl) -> begin
(let _0_458 = (solve_prob orig None [] wl)
in (solve env _0_458))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end))
end
| uu____6789 -> begin
(

let uu____6790 = (base_and_refinement env wl t1)
in (match (uu____6790) with
| (base1, refinement1) -> begin
(

let uu____6816 = (base_and_refinement env wl t2)
in (match (uu____6816) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (None, None) -> begin
(

let uu____6870 = (solve_maybe_uinsts env orig head1 head2 wl)
in (match (uu____6870) with
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end
| USolved (wl) -> begin
(

let subprobs = (FStar_List.map2 (fun uu____6880 uu____6881 -> (match (((uu____6880), (uu____6881))) with
| ((a, uu____6891), (a', uu____6893)) -> begin
(let _0_460 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _0_459 -> FStar_TypeChecker_Common.TProb (_0_459)) _0_460))
end)) args1 args2)
in (

let formula = (FStar_Syntax_Util.mk_conj_l (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs))
in (

let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end))
end
| uu____6903 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env (

let uu___153_6936 = problem
in {FStar_TypeChecker_Common.pid = uu___153_6936.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___153_6936.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___153_6936.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___153_6936.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___153_6936.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___153_6936.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___153_6936.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___153_6936.FStar_TypeChecker_Common.rank}) wl)))
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

let uu____6956 = p
in (match (uu____6956) with
| (((u, k), xs, c), ps, (h, uu____6967, qs)) -> begin
(

let xs = (sn_binders env xs)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____7016 = (imitation_sub_probs orig env xs ps qs)
in (match (uu____7016) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (let _0_465 = (h gs_xs)
in (let _0_464 = (let _0_463 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_461 -> FStar_Util.Inl (_0_461)))
in (FStar_All.pipe_right _0_463 (fun _0_462 -> Some (_0_462))))
in (FStar_Syntax_Util.abs xs _0_465 _0_464)))
in ((

let uu____7055 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7055) with
| true -> begin
(let _0_472 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _0_471 = (FStar_Syntax_Print.comp_to_string c)
in (let _0_470 = (FStar_Syntax_Print.term_to_string im)
in (let _0_469 = (FStar_Syntax_Print.tag_of_term im)
in (let _0_468 = (let _0_466 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _0_466 (FStar_String.concat ", ")))
in (let _0_467 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" _0_472 _0_471 _0_470 _0_469 _0_468 _0_467)))))))
end
| uu____7057 -> begin
()
end));
(

let wl = (solve_prob orig (Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl)
in (solve env (attempt sub_probs wl)));
))
end))))
end)))
in (

let imitate' = (fun orig env wl uu___123_7074 -> (match (uu___123_7074) with
| None -> begin
(giveup env "unable to compute subterms" orig)
end
| Some (p) -> begin
(imitate orig env wl p)
end))
in (

let project = (fun orig env wl i p -> (

let uu____7103 = p
in (match (uu____7103) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____7161 = (FStar_List.nth ps i)
in (match (uu____7161) with
| (pi, uu____7164) -> begin
(

let uu____7169 = (FStar_List.nth xs i)
in (match (uu____7169) with
| (xi, uu____7176) -> begin
(

let rec gs = (fun k -> (

let uu____7185 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____7185) with
| (bs, k) -> begin
(

let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
(([]), ([]))
end
| ((a, uu____7237))::tl -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (

let uu____7245 = (new_uvar r xs k_a)
in (match (uu____7245) with
| (gi_xs, gi) -> begin
(

let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (

let gi_ps = ((FStar_Syntax_Syntax.mk_Tm_app gi ps) (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst = (FStar_Syntax_Syntax.NT (((a), (gi_xs))))::subst
in (

let uu____7264 = (aux subst tl)
in (match (uu____7264) with
| (gi_xs', gi_ps') -> begin
(let _0_476 = (let _0_473 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_0_473)::gi_xs')
in (let _0_475 = (let _0_474 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_0_474)::gi_ps')
in ((_0_476), (_0_475))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in (

let uu____7281 = (let _0_477 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _0_477))
in (match (uu____7281) with
| true -> begin
None
end
| uu____7283 -> begin
(

let uu____7284 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (uu____7284) with
| (g_xs, uu____7291) -> begin
(

let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (let _0_482 = ((FStar_Syntax_Syntax.mk_Tm_app xi g_xs) None r)
in (let _0_481 = (let _0_480 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_478 -> FStar_Util.Inl (_0_478)))
in (FStar_All.pipe_right _0_480 (fun _0_479 -> Some (_0_479))))
in (FStar_Syntax_Util.abs xs _0_482 _0_481)))
in (

let sub = (let _0_487 = (let _0_486 = ((FStar_Syntax_Syntax.mk_Tm_app proj ps) None r)
in (let _0_485 = (let _0_484 = (FStar_List.map (fun uu____7344 -> (match (uu____7344) with
| (uu____7349, uu____7350, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _0_484))
in (mk_problem (p_scope orig) orig _0_486 (p_rel orig) _0_485 None "projection")))
in (FStar_All.pipe_left (fun _0_483 -> FStar_TypeChecker_Common.TProb (_0_483)) _0_487))
in ((

let uu____7355 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7355) with
| true -> begin
(let _0_489 = (FStar_Syntax_Print.term_to_string proj)
in (let _0_488 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _0_489 _0_488)))
end
| uu____7356 -> begin
()
end));
(

let wl = (let _0_490 = Some ((FStar_All.pipe_left Prims.fst (p_guard sub)))
in (solve_prob orig _0_490 ((TERM (((u), (proj))))::[]) wl))
in (let _0_492 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _0_491 -> Some (_0_491)) _0_492)));
))))
end))
end)))
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl -> (

let uu____7385 = lhs
in (match (uu____7385) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let uu____7408 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (uu____7408) with
| (xs, c) -> begin
(match (((FStar_List.length xs) = (FStar_List.length ps))) with
| true -> begin
Some ((let _0_493 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (_0_493))))
end
| uu____7482 -> begin
(

let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (

let uu____7499 = (let _0_494 = (FStar_Syntax_Subst.compress k).FStar_Syntax_Syntax.n
in ((_0_494), (args)))
in (match (uu____7499) with
| (uu____7507, []) -> begin
Some ((let _0_495 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_0_495))))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(

let uu____7525 = (FStar_Syntax_Util.head_and_args k)
in (match (uu____7525) with
| (uv, uv_args) -> begin
(

let uu____7554 = (FStar_Syntax_Subst.compress uv).FStar_Syntax_Syntax.n
in (match (uu____7554) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____7559) -> begin
(

let uu____7572 = (pat_vars env [] uv_args)
in (match (uu____7572) with
| None -> begin
None
end
| Some (scope) -> begin
(

let xs = (FStar_All.pipe_right args (FStar_List.map (fun uu____7586 -> (let _0_499 = (let _0_498 = (Prims.fst (let _0_497 = (let _0_496 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_496 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _0_497)))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) _0_498))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _0_499)))))
in (

let c = (FStar_Syntax_Syntax.mk_Total (Prims.fst (let _0_501 = (let _0_500 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_500 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _0_501))))
in (

let k' = (FStar_Syntax_Util.arrow xs c)
in (

let uv_sol = (let _0_504 = Some (FStar_Util.Inl ((let _0_503 = (FStar_Syntax_Syntax.mk_Total (let _0_502 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_502 Prims.fst)))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_503))))
in (FStar_Syntax_Util.abs scope k' _0_504))
in ((FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)));
Some (((xs), (c)));
)))))
end))
end
| uu____7616 -> begin
None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), uu____7621) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs)
in (match ((n_xs = n_args)) with
| true -> begin
(let _0_506 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right _0_506 (fun _0_505 -> Some (_0_505))))
end
| uu____7654 -> begin
(match ((n_xs < n_args)) with
| true -> begin
(

let uu____7663 = (FStar_Util.first_N n_xs args)
in (match (uu____7663) with
| (args, rest) -> begin
(

let uu____7679 = (FStar_Syntax_Subst.open_comp xs c)
in (match (uu____7679) with
| (xs, c) -> begin
(let _0_507 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt _0_507 (fun uu____7694 -> (match (uu____7694) with
| (xs', c) -> begin
Some ((((FStar_List.append xs xs')), (c)))
end))))
end))
end))
end
| uu____7715 -> begin
(

let uu____7716 = (FStar_Util.first_N n_args xs)
in (match (uu____7716) with
| (xs, rest) -> begin
(

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c))))) None k.FStar_Syntax_Syntax.pos)
in (let _0_510 = (let _0_508 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs _0_508))
in (FStar_All.pipe_right _0_510 (fun _0_509 -> Some (_0_509)))))
end))
end)
end)))
end
| uu____7769 -> begin
(failwith (let _0_513 = (FStar_Syntax_Print.uvar_to_string uv)
in (let _0_512 = (FStar_Syntax_Print.term_to_string k)
in (let _0_511 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" _0_513 _0_512 _0_511)))))
end)))
in (let _0_515 = (elim k_uv ps)
in (FStar_Util.bind_opt _0_515 (fun uu____7803 -> (match (uu____7803) with
| (xs, c) -> begin
Some ((let _0_514 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (_0_514))))
end))))))
end)
end)))
in (

let rec imitate_or_project = (fun n stopt i -> (match (((i >= n) || (FStar_Option.isNone stopt))) with
| true -> begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end
| uu____7886 -> begin
(

let st = (FStar_Option.get stopt)
in (

let tx = (FStar_Unionfind.new_transaction ())
in (match ((i = (~- ((Prims.parse_int "1"))))) with
| true -> begin
(

let uu____7889 = (imitate orig env wl st)
in (match (uu____7889) with
| Failed (uu____7894) -> begin
((FStar_Unionfind.rollback tx);
(imitate_or_project n stopt (i + (Prims.parse_int "1")));
)
end
| sol -> begin
sol
end))
end
| uu____7899 -> begin
(

let uu____7900 = (project orig env wl i st)
in (match (uu____7900) with
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

let uu____7918 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____7918) with
| (hd, uu____7929) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| uu____7947 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd)
in (

let uu____7950 = (FStar_Util.set_is_subset_of fvs_hd fvs1)
in (match (uu____7950) with
| true -> begin
true
end
| uu____7951 -> begin
((

let uu____7953 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7953) with
| true -> begin
(let _0_516 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _0_516))
end
| uu____7954 -> begin
()
end));
false;
)
end)))
end)
end)))
in (

let imitate_ok = (fun t2 -> (

let fvs_hd = (let _0_518 = (let _0_517 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _0_517 Prims.fst))
in (FStar_All.pipe_right _0_518 FStar_Syntax_Free.names))
in (

let uu____7982 = (FStar_Util.set_is_empty fvs_hd)
in (match (uu____7982) with
| true -> begin
(~- ((Prims.parse_int "1")))
end
| uu____7983 -> begin
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

let uu____7991 = (occurs_check env wl ((uv), (k_uv)) t2)
in (match (uu____7991) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(let _0_520 = (let _0_519 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _0_519))
in (giveup_or_defer orig _0_520))
end
| uu____7999 -> begin
(

let uu____8000 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____8000) with
| true -> begin
(

let uu____8001 = (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t2)) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))
in (match (uu____8001) with
| true -> begin
(let _0_521 = (subterms args_lhs)
in (imitate' orig env wl _0_521))
end
| uu____8002 -> begin
((

let uu____8004 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8004) with
| true -> begin
(let _0_524 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_523 = (names_to_string fvs1)
in (let _0_522 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _0_524 _0_523 _0_522))))
end
| uu____8005 -> begin
()
end));
(

let sol = (match (vars) with
| [] -> begin
t2
end
| uu____8009 -> begin
(let _0_525 = (sn_binders env vars)
in (u_abs k_uv _0_525 t2))
end)
in (

let wl = (solve_prob orig None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl)
in (solve env wl)));
)
end))
end
| uu____8013 -> begin
(match ((((not (patterns_only)) && wl.defer_ok) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end
| uu____8014 -> begin
(

let uu____8015 = ((not (patterns_only)) && (check_head fvs1 t2))
in (match (uu____8015) with
| true -> begin
((

let uu____8017 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8017) with
| true -> begin
(let _0_528 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_527 = (names_to_string fvs1)
in (let _0_526 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _0_528 _0_527 _0_526))))
end
| uu____8018 -> begin
()
end));
(let _0_529 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _0_529 (~- ((Prims.parse_int "1")))));
)
end
| uu____8026 -> begin
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
| uu____8027 -> begin
(

let uu____8028 = (let _0_530 = (FStar_Syntax_Free.names t1)
in (check_head _0_530 t2))
in (match (uu____8028) with
| true -> begin
(

let im_ok = (imitate_ok t2)
in ((

let uu____8031 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8031) with
| true -> begin
(let _0_531 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _0_531 (match ((im_ok < (Prims.parse_int "0"))) with
| true -> begin
"imitating"
end
| uu____8032 -> begin
"projecting"
end)))
end
| uu____8033 -> begin
()
end));
(let _0_532 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _0_532 im_ok));
))
end
| uu____8041 -> begin
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
| uu____8052 -> begin
(

let force_quasi_pattern = (fun xs_opt uu____8074 -> (match (uu____8074) with
| (t, u, k, args) -> begin
(

let uu____8104 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____8104) with
| (all_formals, uu____8115) -> begin
(

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match (((formals), (args))) with
| ([], []) -> begin
(

let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun uu____8207 -> (match (uu____8207) with
| (x, imp) -> begin
(let _0_533 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_0_533), (imp)))
end))))
in (

let pattern_vars = (FStar_List.rev pattern_vars)
in (

let kk = (

let uu____8221 = (FStar_Syntax_Util.type_u ())
in (match (uu____8221) with
| (t, uu____8225) -> begin
(Prims.fst (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t))
end))
in (

let uu____8226 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (uu____8226) with
| (t', tm_u1) -> begin
(

let uu____8233 = (destruct_flex_t t')
in (match (uu____8233) with
| (uu____8253, u1, k1, uu____8256) -> begin
(

let sol = TERM ((let _0_534 = (u_abs k all_formals t')
in ((((u), (k))), (_0_534))))
in (

let t_app = ((FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args) None t.FStar_Syntax_Syntax.pos)
in ((sol), (((t_app), (u1), (k1), (pat_args))))))
end))
end)))))
end
| ((formal)::formals, (hd)::tl) -> begin
(

let uu____8343 = (pat_var_opt env pat_args hd)
in (match (uu____8343) with
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun uu____8372 -> (match (uu____8372) with
| (x, uu____8376) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in (match ((not (maybe_pat))) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| uu____8379 -> begin
(

let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____8382 = (not ((FStar_Util.set_is_subset_of fvs pattern_var_set)))
in (match (uu____8382) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| uu____8385 -> begin
(let _0_535 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _0_535 formals tl))
end)))
end))
end))
end
| uu____8390 -> begin
(failwith "Impossible")
end))
in (let _0_536 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _0_536 all_formals args)))
end))
end))
in (

let solve_both_pats = (fun wl uu____8447 uu____8448 r -> (match (((uu____8447), (uu____8448))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
(

let uu____8602 = ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys))
in (match (uu____8602) with
| true -> begin
(let _0_537 = (solve_prob orig None [] wl)
in (solve env _0_537))
end
| uu____8606 -> begin
(

let xs = (sn_binders env xs)
in (

let ys = (sn_binders env ys)
in (

let zs = (intersect_vars xs ys)
in ((

let uu____8620 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8620) with
| true -> begin
(let _0_542 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _0_541 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _0_540 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (let _0_539 = (FStar_Syntax_Print.term_to_string k1)
in (let _0_538 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" _0_542 _0_541 _0_540 _0_539 _0_538))))))
end
| uu____8621 -> begin
()
end));
(

let subst_k = (fun k xs args -> (

let xs_len = (FStar_List.length xs)
in (

let args_len = (FStar_List.length args)
in (match ((xs_len = args_len)) with
| true -> begin
(let _0_543 = (FStar_Syntax_Util.subst_of_list xs args)
in (FStar_Syntax_Subst.subst _0_543 k))
end
| uu____8662 -> begin
(match ((args_len < xs_len)) with
| true -> begin
(

let uu____8668 = (FStar_Util.first_N args_len xs)
in (match (uu____8668) with
| (xs, xs_rest) -> begin
(

let k = (let _0_544 = (FStar_Syntax_Syntax.mk_GTotal k)
in (FStar_Syntax_Util.arrow xs_rest _0_544))
in (let _0_545 = (FStar_Syntax_Util.subst_of_list xs args)
in (FStar_Syntax_Subst.subst _0_545 k)))
end))
end
| uu____8698 -> begin
(failwith (let _0_548 = (FStar_Syntax_Print.term_to_string k)
in (let _0_547 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _0_546 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" _0_548 _0_547 _0_546)))))
end)
end))))
in (

let uu____8699 = (

let uu____8705 = (FStar_Syntax_Util.arrow_formals (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1))
in (match (uu____8705) with
| (bs, k1') -> begin
(

let uu____8730 = (FStar_Syntax_Util.arrow_formals (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2))
in (match (uu____8730) with
| (cs, k2') -> begin
(

let k1'_xs = (subst_k k1' bs args1)
in (

let k2'_ys = (subst_k k2' cs args2)
in (

let sub_prob = (let _0_550 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_549 -> FStar_TypeChecker_Common.TProb (_0_549)) _0_550))
in (

let uu____8760 = (let _0_552 = (FStar_Syntax_Subst.compress k1').FStar_Syntax_Syntax.n
in (let _0_551 = (FStar_Syntax_Subst.compress k2').FStar_Syntax_Syntax.n
in ((_0_552), (_0_551))))
in (match (uu____8760) with
| (FStar_Syntax_Syntax.Tm_type (uu____8768), uu____8769) -> begin
((k1'), ((sub_prob)::[]))
end
| (uu____8773, FStar_Syntax_Syntax.Tm_type (uu____8774)) -> begin
((k2'), ((sub_prob)::[]))
end
| uu____8778 -> begin
(

let uu____8781 = (FStar_Syntax_Util.type_u ())
in (match (uu____8781) with
| (t, uu____8790) -> begin
(

let uu____8791 = (new_uvar r zs t)
in (match (uu____8791) with
| (k_zs, uu____8800) -> begin
(

let kprob = (let _0_554 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k_zs None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_553 -> FStar_TypeChecker_Common.TProb (_0_553)) _0_554))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end)))))
end))
end))
in (match (uu____8699) with
| (k_u', sub_probs) -> begin
(

let uu____8813 = (let _0_560 = (let _0_555 = (new_uvar r zs k_u')
in (FStar_All.pipe_left Prims.fst _0_555))
in (let _0_559 = (let _0_556 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs _0_556))
in (let _0_558 = (let _0_557 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys _0_557))
in ((_0_560), (_0_559), (_0_558)))))
in (match (uu____8813) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs u_zs)
in (

let uu____8839 = (occurs_check env wl ((u1), (k1)) sub1)
in (match (uu____8839) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end
| uu____8851 -> begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in (

let uu____8863 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____8863) with
| true -> begin
(

let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end
| uu____8868 -> begin
(

let sub2 = (u_abs knew2 ys u_zs)
in (

let uu____8870 = (occurs_check env wl ((u2), (k2)) sub2)
in (match (uu____8870) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end
| uu____8882 -> begin
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

let solve_one_pat = (fun uu____8922 uu____8923 -> (match (((uu____8922), (uu____8923))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
((

let uu____9027 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9027) with
| true -> begin
(let _0_562 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_561 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _0_562 _0_561)))
end
| uu____9028 -> begin
()
end));
(

let uu____9029 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____9029) with
| true -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____9039 uu____9040 -> (match (((uu____9039), (uu____9040))) with
| ((a, uu____9050), (t2, uu____9052)) -> begin
(let _0_565 = (let _0_563 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _0_563 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _0_565 (fun _0_564 -> FStar_TypeChecker_Common.TProb (_0_564))))
end)) xs args2)
in (

let guard = (FStar_Syntax_Util.mk_conj_l (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end
| uu____9064 -> begin
(

let t2 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t2)
in (

let uu____9068 = (occurs_check env wl ((u1), (k1)) t2)
in (match (uu____9068) with
| (occurs_ok, uu____9077) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in (

let uu____9082 = (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars))
in (match (uu____9082) with
| true -> begin
(

let sol = TERM ((let _0_566 = (u_abs k1 xs t2)
in ((((u1), (k1))), (_0_566))))
in (

let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end
| uu____9095 -> begin
(

let uu____9096 = (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok))
in (match (uu____9096) with
| true -> begin
(

let uu____9097 = (force_quasi_pattern (Some (xs)) ((t2), (u2), (k2), (args2)))
in (match (uu____9097) with
| (sol, (uu____9111, u2, k2, ys)) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____9121 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____9121) with
| true -> begin
(let _0_567 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _0_567))
end
| uu____9122 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| uu____9126 -> begin
(giveup env "impossible" orig)
end);
))
end))
end
| uu____9127 -> begin
(giveup_or_defer orig "flex-flex constraint")
end))
end)))
end))))
end));
)
end))
in (

let uu____9128 = lhs
in (match (uu____9128) with
| (t1, u1, k1, args1) -> begin
(

let uu____9133 = rhs
in (match (uu____9133) with
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
| uu____9159 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end
| uu____9164 -> begin
(

let uu____9165 = (force_quasi_pattern None ((t1), (u1), (k1), (args1)))
in (match (uu____9165) with
| (sol, uu____9172) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____9175 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____9175) with
| true -> begin
(let _0_568 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _0_568))
end
| uu____9176 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| uu____9180 -> begin
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

let uu____9182 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____9182) with
| true -> begin
(let _0_569 = (solve_prob orig None [] wl)
in (solve env _0_569))
end
| uu____9183 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in (

let uu____9186 = (FStar_Util.physical_equality t1 t2)
in (match (uu____9186) with
| true -> begin
(let _0_570 = (solve_prob orig None [] wl)
in (solve env _0_570))
end
| uu____9187 -> begin
((

let uu____9189 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____9189) with
| true -> begin
(let _0_571 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _0_571))
end
| uu____9190 -> begin
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

let mk_c = (fun c uu___124_9235 -> (match (uu___124_9235) with
| [] -> begin
c
end
| bs -> begin
(FStar_Syntax_Syntax.mk_Total ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c))))) None c.FStar_Syntax_Syntax.pos))
end))
in (

let uu____9270 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____9270) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (

let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (

let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (

let rel = (

let uu____9356 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____9356) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____9357 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (let _0_573 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _0_572 -> FStar_TypeChecker_Common.CProb (_0_572)) _0_573)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___125_9432 -> (match (uu___125_9432) with
| [] -> begin
t
end
| bs -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l))))) None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____9471 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____9471) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _0_577 = (let _0_576 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _0_575 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _0_576 problem.FStar_TypeChecker_Common.relation _0_575 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _0_574 -> FStar_TypeChecker_Common.TProb (_0_574)) _0_577))))
end)))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____9568) -> begin
true
end
| uu____9583 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____9602 -> begin
(

let t = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____9608 -> begin
FStar_Util.Inr (t)
end))
end))
in (

let uu____9611 = (let _0_579 = (maybe_eta t1)
in (let _0_578 = (maybe_eta t2)
in ((_0_579), (_0_578))))
in (match (uu____9611) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(solve_t env (

let uu___154_9648 = problem
in {FStar_TypeChecker_Common.pid = uu___154_9648.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___154_9648.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___154_9648.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___154_9648.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___154_9648.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___154_9648.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___154_9648.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___154_9648.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs))) | ((FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs))) -> begin
(

let uu____9681 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____9681) with
| true -> begin
(let _0_580 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig _0_580 t_abs wl))
end
| uu____9682 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| uu____9683 -> begin
(failwith "Impossible: at least one side is an abstraction")
end))))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____9694), FStar_Syntax_Syntax.Tm_refine (uu____9695)) -> begin
(

let uu____9704 = (as_refinement env wl t1)
in (match (uu____9704) with
| (x1, phi1) -> begin
(

let uu____9709 = (as_refinement env wl t2)
in (match (uu____9709) with
| (x2, phi2) -> begin
(

let base_prob = (let _0_582 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _0_581 -> FStar_TypeChecker_Common.TProb (_0_581)) _0_582))
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

let mk_imp = (fun imp phi1 phi2 -> (let _0_583 = (imp phi1 phi2)
in (FStar_All.pipe_right _0_583 (guard_on_element problem x1))))
in (

let fallback = (fun uu____9752 -> (

let impl = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end
| uu____9758 -> begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end)
in (

let guard = (let _0_584 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _0_584 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl))))))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let ref_prob = (let _0_588 = (let _0_587 = (let _0_586 = (FStar_Syntax_Syntax.mk_binder x1)
in (_0_586)::(p_scope orig))
in (mk_problem _0_587 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _0_585 -> FStar_TypeChecker_Common.TProb (_0_585)) _0_588))
in (

let uu____9770 = (solve env (

let uu___155_9771 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___155_9771.ctr; defer_ok = false; smt_ok = uu___155_9771.smt_ok; tcenv = uu___155_9771.tcenv}))
in (match (uu____9770) with
| Failed (uu____9775) -> begin
(fallback ())
end
| Success (uu____9778) -> begin
(

let guard = (let _0_591 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _0_590 = (let _0_589 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _0_589 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _0_591 _0_590)))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (

let wl = (

let uu___156_9792 = wl
in {attempting = uu___156_9792.attempting; wl_deferred = uu___156_9792.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___156_9792.defer_ok; smt_ok = uu___156_9792.smt_ok; tcenv = uu___156_9792.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end)))
end
| uu____9793 -> begin
(fallback ())
end)))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _0_593 = (destruct_flex_t t1)
in (let _0_592 = (destruct_flex_t t2)
in (flex_flex orig _0_593 _0_592)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _0_594 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig _0_594 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_arrow (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
(solve_t' env (

let uu___157_9906 = problem
in {FStar_TypeChecker_Common.pid = uu___157_9906.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___157_9906.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___157_9906.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___157_9906.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___157_9906.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___157_9906.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___157_9906.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___157_9906.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___157_9906.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____9922 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____9924 = (let _0_595 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _0_595))
in (match (uu____9924) with
| true -> begin
(let _0_598 = (FStar_All.pipe_left (fun _0_596 -> FStar_TypeChecker_Common.TProb (_0_596)) (

let uu___158_9927 = problem
in {FStar_TypeChecker_Common.pid = uu___158_9927.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___158_9927.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___158_9927.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___158_9927.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___158_9927.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___158_9927.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___158_9927.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___158_9927.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___158_9927.FStar_TypeChecker_Common.rank}))
in (let _0_597 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false _0_598 _0_597 t2 wl)))
end
| uu____9928 -> begin
(

let uu____9929 = (base_and_refinement env wl t2)
in (match (uu____9929) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _0_601 = (FStar_All.pipe_left (fun _0_599 -> FStar_TypeChecker_Common.TProb (_0_599)) (

let uu___159_9961 = problem
in {FStar_TypeChecker_Common.pid = uu___159_9961.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___159_9961.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___159_9961.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___159_9961.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___159_9961.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___159_9961.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___159_9961.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___159_9961.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___159_9961.FStar_TypeChecker_Common.rank}))
in (let _0_600 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false _0_601 _0_600 t_base wl)))
end
| Some (y, phi) -> begin
(

let y' = (

let uu___160_9973 = y
in {FStar_Syntax_Syntax.ppname = uu___160_9973.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___160_9973.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element problem y' phi)
in (

let base_prob = (let _0_603 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_602 -> FStar_TypeChecker_Common.TProb (_0_602)) _0_603))
in (

let guard = (let _0_604 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _0_604 impl))
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
| uu____10003 -> begin
(

let uu____10004 = (base_and_refinement env wl t1)
in (match (uu____10004) with
| (t_base, uu____10015) -> begin
(solve_t env (

let uu___161_10030 = problem
in {FStar_TypeChecker_Common.pid = uu___161_10030.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___161_10030.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___161_10030.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___161_10030.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___161_10030.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___161_10030.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___161_10030.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___161_10030.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (FStar_Syntax_Syntax.Tm_refine (uu____10033), uu____10034) -> begin
(

let t2 = (let _0_605 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _0_605))
in (solve_t env (

let uu___162_10049 = problem
in {FStar_TypeChecker_Common.pid = uu___162_10049.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___162_10049.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___162_10049.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___162_10049.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_10049.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_10049.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_10049.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_10049.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_10049.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____10050, FStar_Syntax_Syntax.Tm_refine (uu____10051)) -> begin
(

let t1 = (let _0_606 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _0_606))
in (solve_t env (

let uu___163_10066 = problem
in {FStar_TypeChecker_Common.pid = uu___163_10066.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___163_10066.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___163_10066.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___163_10066.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___163_10066.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___163_10066.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___163_10066.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___163_10066.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___163_10066.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(

let head1 = (let _0_607 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _0_607 Prims.fst))
in (

let head2 = (let _0_608 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _0_608 Prims.fst))
in (

let uu____10135 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____10135) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____10144 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____10144) with
| true -> begin
(

let guard = (

let uu____10153 = (let _0_609 = (FStar_Syntax_Util.eq_tm t1 t2)
in (_0_609 = FStar_Syntax_Util.Equal))
in (match (uu____10153) with
| true -> begin
None
end
| uu____10159 -> begin
(let _0_611 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _0_610 -> Some (_0_610)) _0_611))
end))
in (let _0_612 = (solve_prob orig guard [] wl)
in (solve env _0_612)))
end
| uu____10167 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____10168 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, uu____10170, uu____10171), uu____10172) -> begin
(solve_t' env (

let uu___164_10191 = problem
in {FStar_TypeChecker_Common.pid = uu___164_10191.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___164_10191.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___164_10191.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___164_10191.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_10191.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_10191.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_10191.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_10191.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_10191.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____10194, FStar_Syntax_Syntax.Tm_ascribed (t2, uu____10196, uu____10197)) -> begin
(solve_t' env (

let uu___165_10216 = problem
in {FStar_TypeChecker_Common.pid = uu___165_10216.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___165_10216.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___165_10216.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___165_10216.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___165_10216.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___165_10216.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___165_10216.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___165_10216.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___165_10216.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(failwith (let _0_614 = (FStar_Syntax_Print.tag_of_term t1)
in (let _0_613 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _0_614 _0_613))))
end
| uu____10229 -> begin
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

let uu____10261 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____10261) with
| true -> begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end
| uu____10262 -> begin
()
end));
(

let sub_probs = (FStar_List.map2 (fun uu____10269 uu____10270 -> (match (((uu____10269), (uu____10270))) with
| ((a1, uu____10280), (a2, uu____10282)) -> begin
(let _0_616 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _0_615 -> FStar_TypeChecker_Common.TProb (_0_615)) _0_616))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (FStar_Syntax_Util.mk_conj_l (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs))
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
| ((wp1, uu____10311))::[] -> begin
wp1
end
| uu____10324 -> begin
(failwith (let _0_617 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _0_617)))
end)
in (

let c1 = (let _0_619 = (let _0_618 = (FStar_Syntax_Syntax.as_arg (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp))
in (_0_618)::[])
in {FStar_Syntax_Syntax.comp_univs = c1.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _0_619; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2)))
end
| uu____10333 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___126_10336 -> (match (uu___126_10336) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| uu____10337 -> begin
false
end))))
in (

let uu____10338 = (match (((c1.FStar_Syntax_Syntax.effect_args), (c2.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____10362))::uu____10363, ((wp2, uu____10365))::uu____10366) -> begin
((wp1), (wp2))
end
| uu____10407 -> begin
(failwith (let _0_621 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _0_620 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _0_621 _0_620))))
end)
in (match (uu____10338) with
| (wpc1, wpc2) -> begin
(

let uu____10436 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____10436) with
| true -> begin
(let _0_622 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _0_622 wl))
end
| uu____10441 -> begin
(

let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____10444 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____10446 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10446) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____10447 -> begin
()
end));
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_630 = (let _0_624 = (let _0_623 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_0_623)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _0_624 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _0_629 = (let _0_628 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _0_627 = (let _0_626 = (let _0_625 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_625))
in (_0_626)::[])
in (_0_628)::_0_627))
in ((_0_630), (_0_629))))))) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r);
)
end
| uu____10457 -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_640 = (let _0_632 = (let _0_631 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_0_631)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _0_632 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (let _0_639 = (let _0_638 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _0_637 = (let _0_636 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _0_635 = (let _0_634 = (let _0_633 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_633))
in (_0_634)::[])
in (_0_636)::_0_635))
in (_0_638)::_0_637))
in ((_0_640), (_0_639))))))) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)
end)
end)
in (

let base_prob = (let _0_642 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _0_641 -> FStar_TypeChecker_Common.TProb (_0_641)) _0_642))
in (

let wl = (let _0_646 = (let _0_645 = (let _0_644 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _0_644 g))
in (FStar_All.pipe_left (fun _0_643 -> Some (_0_643)) _0_645))
in (solve_prob orig _0_646 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end))
end)))
end)))
in (

let uu____10480 = (FStar_Util.physical_equality c1 c2)
in (match (uu____10480) with
| true -> begin
(let _0_647 = (solve_prob orig None [] wl)
in (solve env _0_647))
end
| uu____10481 -> begin
((

let uu____10483 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10483) with
| true -> begin
(let _0_649 = (FStar_Syntax_Print.comp_to_string c1)
in (let _0_648 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _0_649 (rel_to_string problem.FStar_TypeChecker_Common.relation) _0_648)))
end
| uu____10484 -> begin
()
end));
(

let uu____10485 = (let _0_651 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (let _0_650 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((_0_651), (_0_650))))
in (match (uu____10485) with
| (c1, c2) -> begin
(match (((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____10491), FStar_Syntax_Syntax.Total (t2, uu____10493)) when (FStar_Syntax_Util.non_informative t2) -> begin
(let _0_652 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _0_652 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____10508), FStar_Syntax_Syntax.Total (uu____10509)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.Total (t2, _))) | ((FStar_Syntax_Syntax.GTotal (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) | ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) -> begin
(let _0_653 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _0_653 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _0_656 = (

let uu___166_10564 = problem
in (let _0_655 = (let _0_654 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _0_654))
in {FStar_TypeChecker_Common.pid = uu___166_10564.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _0_655; FStar_TypeChecker_Common.relation = uu___166_10564.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___166_10564.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___166_10564.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_10564.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___166_10564.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___166_10564.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_10564.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_10564.FStar_TypeChecker_Common.rank}))
in (solve_c env _0_656 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _0_659 = (

let uu___167_10571 = problem
in (let _0_658 = (let _0_657 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c2)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _0_657))
in {FStar_TypeChecker_Common.pid = uu___167_10571.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___167_10571.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___167_10571.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _0_658; FStar_TypeChecker_Common.element = uu___167_10571.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___167_10571.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___167_10571.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___167_10571.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___167_10571.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___167_10571.FStar_TypeChecker_Common.rank}))
in (solve_c env _0_659 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____10574), FStar_Syntax_Syntax.Comp (uu____10575)) -> begin
(

let uu____10576 = (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2))))
in (match (uu____10576) with
| true -> begin
(let _0_660 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _0_660 wl))
end
| uu____10579 -> begin
(

let c1_comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c1)
in (

let c2_comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c2)
in (match (((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name))) with
| true -> begin
(solve_eq c1_comp c2_comp)
end
| uu____10582 -> begin
(

let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (

let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in ((

let uu____10586 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10586) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____10587 -> begin
()
end));
(

let uu____10588 = (FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (uu____10588) with
| None -> begin
(

let uu____10590 = (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (FStar_Syntax_Util.non_informative (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)))
in (match (uu____10590) with
| true -> begin
(

let edge = {FStar_TypeChecker_Env.msource = c1.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c2.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = (fun r t -> t)}
in (solve_sub c1 edge c2))
end
| uu____10594 -> begin
(let _0_663 = (let _0_662 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _0_661 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _0_662 _0_661)))
in (giveup env _0_663 orig))
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


let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _0_664 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____10618 -> (match (uu____10618) with
| (uu____10629, uu____10630, u, uu____10632, uu____10633, uu____10634) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _0_664 (FStar_String.concat ", "))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred))) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| uu____10657 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____10662 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____10662) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____10663 -> begin
"non-trivial"
end))
end)
in (

let carry = (let _0_665 = (FStar_List.map (fun uu____10668 -> (match (uu____10668) with
| (uu____10671, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _0_665 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu____10691; FStar_TypeChecker_Env.implicits = uu____10692} -> begin
true
end
| uu____10703 -> begin
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
| uu____10728 -> begin
(failwith "impossible")
end)
in Some ((

let uu___168_10729 = g
in (let _0_674 = (let _0_673 = (let _0_672 = (let _0_667 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_667)::[])
in (let _0_671 = Some ((let _0_670 = (let _0_668 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _0_668 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _0_670 (fun _0_669 -> FStar_Util.Inl (_0_669)))))
in (FStar_Syntax_Util.abs _0_672 f _0_671)))
in (FStar_All.pipe_left (fun _0_666 -> FStar_TypeChecker_Common.NonTrivial (_0_666)) _0_673))
in {FStar_TypeChecker_Env.guard_f = _0_674; FStar_TypeChecker_Env.deferred = uu___168_10729.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___168_10729.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___168_10729.FStar_TypeChecker_Env.implicits}))))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___169_10750 = g
in (let _0_679 = (let _0_678 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_677 = (let _0_676 = (FStar_Syntax_Syntax.as_arg e)
in (_0_676)::[])
in ((f), (_0_677)))))) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left (fun _0_675 -> FStar_TypeChecker_Common.NonTrivial (_0_675)) _0_678))
in {FStar_TypeChecker_Env.guard_f = _0_679; FStar_TypeChecker_Env.deferred = uu___169_10750.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___169_10750.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___169_10750.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____10767) -> begin
(failwith "impossible")
end))


let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
FStar_TypeChecker_Common.NonTrivial ((FStar_Syntax_Util.mk_conj f1 f2))
end))


let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____10785 -> begin
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


let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _0_680 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _0_680; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___170_10843 = g
in (let _0_683 = (let _0_682 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _0_682 (fun _0_681 -> FStar_TypeChecker_Common.NonTrivial (_0_681))))
in {FStar_TypeChecker_Env.guard_f = _0_683; FStar_TypeChecker_Env.deferred = uu___170_10843.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___170_10843.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___170_10843.FStar_TypeChecker_Env.implicits}))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = (

let uu____10881 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____10881) with
| true -> begin
(let _0_685 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _0_684 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _0_685 (rel_to_string rel) _0_684)))
end
| uu____10882 -> begin
"TOP"
end))
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (let _0_688 = (let _0_687 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_686 -> Some (_0_686)) _0_687))
in (FStar_Syntax_Syntax.new_bv _0_688 t1))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (let _0_692 = (let _0_690 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _0_689 -> Some (_0_689)) _0_690))
in (let _0_691 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _0_692 _0_691)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (

let probs = (

let uu____10929 = (FStar_Options.eager_inference ())
in (match (uu____10929) with
| true -> begin
(

let uu___171_10930 = probs
in {attempting = uu___171_10930.attempting; wl_deferred = uu___171_10930.wl_deferred; ctr = uu___171_10930.ctr; defer_ok = false; smt_ok = uu___171_10930.smt_ok; tcenv = uu___171_10930.tcenv})
end
| uu____10931 -> begin
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

let uu____10941 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____10941) with
| true -> begin
(let _0_693 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _0_693))
end
| uu____10942 -> begin
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

let uu____10951 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____10951) with
| true -> begin
(let _0_694 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _0_694))
end
| uu____10952 -> begin
()
end));
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in ((

let uu____10955 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____10955) with
| true -> begin
(let _0_695 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _0_695))
end
| uu____10956 -> begin
()
end));
(

let f = (

let uu____10958 = (FStar_Syntax_Util.unmeta f).FStar_Syntax_Syntax.n
in (match (uu____10958) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____10960 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end))
in (

let uu___172_10961 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = uu___172_10961.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___172_10961.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___172_10961.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _0_701 = (let _0_700 = (let _0_699 = (let _0_698 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _0_698 (fun _0_697 -> FStar_TypeChecker_Common.NonTrivial (_0_697))))
in {FStar_TypeChecker_Env.guard_f = _0_699; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _0_700))
in (FStar_All.pipe_left (fun _0_696 -> Some (_0_696)) _0_701))
end))


let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> ((

let uu____10997 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10997) with
| true -> begin
(let _0_703 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_702 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _0_703 _0_702)))
end
| uu____10998 -> begin
()
end));
(

let prob = (let _0_706 = (let _0_705 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _0_705))
in (FStar_All.pipe_left (fun _0_704 -> FStar_TypeChecker_Common.TProb (_0_704)) _0_706))
in (

let g = (let _0_708 = (let _0_707 = (singleton env prob)
in (solve_and_commit env _0_707 (fun uu____11006 -> None)))
in (FStar_All.pipe_left (with_guard env prob) _0_708))
in g));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____11018 = (try_teq env t1 t2)
in (match (uu____11018) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_710 = (FStar_TypeChecker_Err.basic_type_error env None t2 t1)
in (let _0_709 = (FStar_TypeChecker_Env.get_range env)
in ((_0_710), (_0_709)))))))
end
| Some (g) -> begin
((

let uu____11022 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11022) with
| true -> begin
(let _0_713 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_712 = (FStar_Syntax_Print.term_to_string t2)
in (let _0_711 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _0_713 _0_712 _0_711))))
end
| uu____11023 -> begin
()
end));
g;
)
end)))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 smt_ok -> ((

let uu____11038 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11038) with
| true -> begin
(let _0_715 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _0_714 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _0_715 _0_714)))
end
| uu____11039 -> begin
()
end));
(

let uu____11040 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____11040) with
| (prob, x) -> begin
(

let g = (let _0_717 = (let _0_716 = (singleton' env prob smt_ok)
in (solve_and_commit env _0_716 (fun uu____11050 -> None)))
in (FStar_All.pipe_left (with_guard env prob) _0_717))
in ((

let uu____11054 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____11054) with
| true -> begin
(let _0_721 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _0_720 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _0_719 = (let _0_718 = (FStar_Util.must g)
in (guard_to_string env _0_718))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _0_721 _0_720 _0_719))))
end
| uu____11055 -> begin
()
end));
(abstract_guard x g);
))
end));
))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env e t1 t2 -> (let _0_723 = (FStar_TypeChecker_Env.get_range env)
in (let _0_722 = (FStar_TypeChecker_Err.basic_type_error env (Some (e)) t2 t1)
in (FStar_Errors.report _0_723 _0_722))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> ((

let uu____11089 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11089) with
| true -> begin
(let _0_725 = (FStar_Syntax_Print.comp_to_string c1)
in (let _0_724 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _0_725 _0_724)))
end
| uu____11090 -> begin
()
end));
(

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____11092 -> begin
FStar_TypeChecker_Common.SUB
end)
in (

let prob = (let _0_728 = (let _0_727 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _0_727 "sub_comp"))
in (FStar_All.pipe_left (fun _0_726 -> FStar_TypeChecker_Common.CProb (_0_726)) _0_728))
in (let _0_730 = (let _0_729 = (singleton env prob)
in (solve_and_commit env _0_729 (fun uu____11098 -> None)))
in (FStar_All.pipe_left (with_guard env prob) _0_730))));
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
in (Prims.raise (FStar_Errors.Error ((let _0_734 = (let _0_732 = (FStar_Syntax_Print.univ_to_string u1)
in (let _0_731 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _0_732 _0_731 msg)))
in (let _0_733 = (FStar_TypeChecker_Env.get_range env)
in ((_0_734), (_0_733))))))));
))
in (

let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
(((uv), ((u1)::[])))::[]
end
| (hd)::tl -> begin
(

let uu____11205 = hd
in (match (uu____11205) with
| (uv', lower_bounds) -> begin
(

let uu____11225 = (FStar_Unionfind.equivalent uv uv')
in (match (uu____11225) with
| true -> begin
(((uv'), ((u1)::lower_bounds)))::tl
end
| uu____11241 -> begin
(let _0_735 = (insert uv u1 tl)
in (hd)::_0_735)
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

let uu____11314 = (FStar_Syntax_Util.eq_univs u1 u2)
in (match (uu____11314) with
| true -> begin
(group_by out rest)
end
| uu____11322 -> begin
(let _0_736 = (insert uv u1 out)
in (group_by _0_736 rest))
end)))
end
| uu____11323 -> begin
None
end))
end))
in (

let ad_hoc_fallback = (fun uu____11333 -> (match (ineqs) with
| [] -> begin
()
end
| uu____11336 -> begin
(

let wl = (

let uu___173_11341 = (empty_worklist env)
in {attempting = uu___173_11341.attempting; wl_deferred = uu___173_11341.wl_deferred; ctr = uu___173_11341.ctr; defer_ok = true; smt_ok = uu___173_11341.smt_ok; tcenv = uu___173_11341.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun uu____11347 -> (match (uu____11347) with
| (u1, u2) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| uu____11354 -> begin
(

let uu____11355 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl u1 u2)
in (match (uu____11355) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(

let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| uu____11363 -> begin
(u1)::[]
end)
in (

let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| uu____11369 -> begin
(u2)::[]
end)
in (

let uu____11370 = (FStar_All.pipe_right us1 (FStar_Util.for_all (fun uu___127_11372 -> (match (uu___127_11372) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(

let uu____11374 = (FStar_Syntax_Util.univ_kernel u)
in (match (uu____11374) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (

let uu____11381 = (FStar_Syntax_Util.univ_kernel u')
in (match (uu____11381) with
| (k_u', n') -> begin
((FStar_Syntax_Util.eq_univs k_u k_u') && (n <= n'))
end)))))
end))
end))))
in (match (uu____11370) with
| true -> begin
()
end
| uu____11386 -> begin
(fail None u1 u2)
end))))
end
| USolved (uu____11387) -> begin
()
end))
end)))
end)))))
end))
in (

let uu____11388 = (group_by [] ineqs)
in (match (uu____11388) with
| Some (groups) -> begin
(

let wl = (

let uu___174_11415 = (empty_worklist env)
in {attempting = uu___174_11415.attempting; wl_deferred = uu___174_11415.wl_deferred; ctr = uu___174_11415.ctr; defer_ok = false; smt_ok = uu___174_11415.smt_ok; tcenv = uu___174_11415.tcenv})
in (

let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| ((u, lower_bounds))::groups -> begin
(

let uu____11460 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))
in (match (uu____11460) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| uu____11462 -> begin
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

let fail = (fun uu____11495 -> (match (uu____11495) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Errors.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in ((

let uu____11505 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11505) with
| true -> begin
(let _0_738 = (wl_to_string wl)
in (let _0_737 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _0_738 _0_737)))
end
| uu____11515 -> begin
()
end));
(

let g = (

let uu____11517 = (solve_and_commit env wl fail)
in (match (uu____11517) with
| Some ([]) -> begin
(

let uu___175_11524 = g
in {FStar_TypeChecker_Env.guard_f = uu___175_11524.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu___175_11524.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___175_11524.FStar_TypeChecker_Env.implicits})
end
| uu____11527 -> begin
(failwith "impossible: Unexpected deferred constraints remain")
end))
in ((solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___176_11530 = g
in {FStar_TypeChecker_Env.guard_f = uu___176_11530.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___176_11530.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = uu___176_11530.FStar_TypeChecker_Env.implicits});
));
))))


let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (

let g = (solve_deferred_constraints env g)
in ((

let uu____11549 = (not ((FStar_TypeChecker_Env.should_verify env)))
in (match (uu____11549) with
| true -> begin
()
end
| uu____11550 -> begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((

let uu____11553 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Norm")))
in (match (uu____11553) with
| true -> begin
(let _0_741 = (FStar_TypeChecker_Env.get_range env)
in (let _0_740 = (let _0_739 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" _0_739))
in (FStar_Errors.diag _0_741 _0_740)))
end
| uu____11554 -> begin
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

let uu____11558 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11558) with
| true -> begin
(let _0_744 = (FStar_TypeChecker_Env.get_range env)
in (let _0_743 = (let _0_742 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _0_742))
in (FStar_Errors.diag _0_744 _0_743)))
end
| uu____11559 -> begin
()
end));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc);
)
end));
)
end)
end));
(

let uu___177_11560 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___177_11560.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___177_11560.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___177_11560.FStar_TypeChecker_Env.implicits});
)))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (

let uu____11584 = (FStar_Unionfind.find u)
in (match (uu____11584) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| uu____11593 -> begin
false
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____11608 = acc
in (match (uu____11608) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____11619 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd)::tl -> begin
(

let uu____11654 = hd
in (match (uu____11654) with
| (uu____11661, env, u, tm, k, r) -> begin
(

let uu____11667 = (unresolved u)
in (match (uu____11667) with
| true -> begin
(until_fixpoint (((hd)::out), (changed)) tl)
end
| uu____11681 -> begin
(

let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in ((

let uu____11685 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11685) with
| true -> begin
(let _0_747 = (FStar_Syntax_Print.uvar_to_string u)
in (let _0_746 = (FStar_Syntax_Print.term_to_string tm)
in (let _0_745 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _0_747 _0_746 _0_745))))
end
| uu____11689 -> begin
()
end));
(

let uu____11690 = (env.FStar_TypeChecker_Env.type_of (

let uu___178_11694 = env
in {FStar_TypeChecker_Env.solver = uu___178_11694.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___178_11694.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___178_11694.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___178_11694.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___178_11694.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___178_11694.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___178_11694.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___178_11694.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___178_11694.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___178_11694.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___178_11694.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___178_11694.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___178_11694.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___178_11694.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___178_11694.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___178_11694.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___178_11694.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___178_11694.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___178_11694.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___178_11694.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___178_11694.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___178_11694.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___178_11694.FStar_TypeChecker_Env.qname_and_index}) tm)
in (match (uu____11690) with
| (uu____11695, uu____11696, g) -> begin
(

let g = (match (env.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___179_11699 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___179_11699.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___179_11699.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___179_11699.FStar_TypeChecker_Env.implicits})
end
| uu____11700 -> begin
g
end)
in (

let g' = (discharge_guard' (Some ((fun uu____11704 -> (FStar_Syntax_Print.term_to_string tm)))) env g)
in (until_fixpoint (((FStar_List.append g'.FStar_TypeChecker_Env.implicits out)), (true)) tl)))
end));
)))
end))
end))
end)
end)))
in (

let uu___180_11718 = g
in (let _0_748 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___180_11718.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___180_11718.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___180_11718.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _0_748})))))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g = (let _0_749 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _0_749 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _0_750 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _0_750))
end
| ((reason, uu____11746, uu____11747, e, t, r))::uu____11751 -> begin
(let _0_753 = (let _0_752 = (FStar_Syntax_Print.term_to_string t)
in (let _0_751 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" _0_752 _0_751 reason)))
in (FStar_Errors.report r _0_753))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___181_11771 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___181_11771.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___181_11771.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (((u1), (u2)))::[]; FStar_TypeChecker_Env.implicits = uu___181_11771.FStar_TypeChecker_Env.implicits}))





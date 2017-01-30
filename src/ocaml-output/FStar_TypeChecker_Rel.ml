
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

let k' = (let _0_235 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _0_235))
in (

let uv = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k'))))) None r)
in (let _0_236 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((uv), (args))))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((_0_236), (uv))))))
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
(let _0_238 = (FStar_Syntax_Print.uvar_to_string u)
in (let _0_237 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "(%s:%s)" _0_238 _0_237)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty); FStar_Syntax_Syntax.tk = uu____307; FStar_Syntax_Syntax.pos = uu____308; FStar_Syntax_Syntax.vars = uu____309}, args) -> begin
(let _0_241 = (FStar_Syntax_Print.uvar_to_string u)
in (let _0_240 = (FStar_Syntax_Print.term_to_string ty)
in (let _0_239 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "(%s:%s) %s" _0_241 _0_240 _0_239))))
end
| uu____340 -> begin
(FStar_Syntax_Print.term_to_string t)
end)))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env uu___100_346 -> (match (uu___100_346) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _0_256 = (let _0_255 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _0_254 = (let _0_253 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _0_252 = (let _0_251 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _0_250 = (let _0_249 = (let _0_248 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _0_247 = (let _0_246 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _0_245 = (let _0_244 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _0_243 = (let _0_242 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_0_242)::[])
in (_0_244)::_0_243))
in (_0_246)::_0_245))
in (_0_248)::_0_247))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_0_249)
in (_0_251)::_0_250))
in (_0_253)::_0_252))
in (_0_255)::_0_254))
in (FStar_Util.format "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _0_256))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _0_258 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _0_257 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _0_258 (rel_to_string p.FStar_TypeChecker_Common.relation) _0_257)))
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
(let _0_259 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _0_259 FStar_Util.string_of_int))
end))
in (let _0_260 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _0_260)))
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
(let _0_261 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _0_261 FStar_Util.string_of_int))
end))
in (let _0_262 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _0_262)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _0_263 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _0_263 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (let _0_265 = (let _0_264 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _0_264 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _0_265 (FStar_String.concat ", "))))


let args_to_string = (fun args -> (let _0_266 = (FStar_All.pipe_right args (FStar_List.map (fun uu____414 -> (match (uu____414) with
| (x, uu____418) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _0_266 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> (let _0_267 = (not ((FStar_Options.eager_inference ())))
in {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = _0_267; smt_ok = true; tcenv = env}))


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let uu___128_434 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = uu___128_434.wl_deferred; ctr = uu___128_434.ctr; defer_ok = uu___128_434.defer_ok; smt_ok = smt_ok; tcenv = uu___128_434.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard = (fun env g -> (

let uu___129_459 = (empty_worklist env)
in (let _0_268 = (FStar_List.map Prims.snd g)
in {attempting = _0_268; wl_deferred = uu___129_459.wl_deferred; ctr = uu___129_459.ctr; defer_ok = false; smt_ok = uu___129_459.smt_ok; tcenv = uu___129_459.tcenv})))


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
(let _0_269 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _0_269))
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
(FStar_All.pipe_right (maybe_invert p) (fun _0_270 -> FStar_TypeChecker_Common.TProb (_0_270)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _0_271 -> FStar_TypeChecker_Common.CProb (_0_271)))
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
(FStar_All.pipe_left (fun _0_272 -> FStar_TypeChecker_Common.TProb (_0_272)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _0_273 -> FStar_TypeChecker_Common.CProb (_0_273)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> (let _0_274 = (FStar_All.pipe_right (p_reason p) FStar_List.length)
in (_0_274 = (Prims.parse_int "1"))))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun uu____636 -> ((FStar_Util.incr ctr);
(FStar_ST.read ctr);
)))


let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _0_276 = (next_pid ())
in (let _0_275 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _0_276; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _0_275; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))


let new_problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _0_278 = (next_pid ())
in (let _0_277 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _0_278; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _0_277; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _0_279 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _0_279; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))


let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (

let uu____813 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____813) with
| true -> begin
(let _0_282 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _0_281 = (prob_to_string env d)
in (let _0_280 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _0_282 _0_281 _0_280 s))))
end
| uu____815 -> begin
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
| uu____818 -> begin
(failwith "impossible")
end)
in (

let uu____819 = (match (d) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(let _0_284 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (let _0_283 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((_0_284), (_0_283))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _0_286 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (let _0_285 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((_0_286), (_0_285))))
end)
in (match (uu____819) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)))


let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun uu___112_838 -> (match (uu___112_838) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| uu____845 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, uu____848), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun uu___113_871 -> (match (uu___113_871) with
| UNIV (uu____873) -> begin
None
end
| TERM ((u, uu____877), t) -> begin
(

let uu____881 = (FStar_Unionfind.equivalent uv u)
in (match (uu____881) with
| true -> begin
Some (t)
end
| uu____886 -> begin
None
end))
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun uu___114_900 -> (match (uu___114_900) with
| UNIV (u', t) -> begin
(

let uu____904 = (FStar_Unionfind.equivalent u u')
in (match (uu____904) with
| true -> begin
Some (t)
end
| uu____907 -> begin
None
end))
end
| uu____908 -> begin
None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_Syntax_Subst.compress (let _0_287 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _0_287))))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_Syntax_Subst.compress (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)))


let norm_arg = (fun env t -> (let _0_288 = (sn env (Prims.fst t))
in ((_0_288), ((Prims.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun uu____955 -> (match (uu____955) with
| (x, imp) -> begin
(let _0_290 = (

let uu___133_962 = x
in (let _0_289 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___133_962.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___133_962.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_289}))
in ((_0_290), (imp)))
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
| uu____977 -> begin
u
end)))
in (let _0_291 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _0_291))))


let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement = (fun env wl t1 -> (

let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(match (norm) with
| true -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| uu____1083 -> begin
(

let uu____1084 = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (match (uu____1084) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = uu____1096; FStar_Syntax_Syntax.pos = uu____1097; FStar_Syntax_Syntax.vars = uu____1098} -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| tt -> begin
(failwith (let _0_293 = (FStar_Syntax_Print.term_to_string tt)
in (let _0_292 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _0_293 _0_292))))
end))
end)
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(match (norm) with
| true -> begin
((t1), (None))
end
| uu____1151 -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (

let uu____1153 = (FStar_Syntax_Subst.compress t1').FStar_Syntax_Syntax.n
in (match (uu____1153) with
| FStar_Syntax_Syntax.Tm_refine (uu____1163) -> begin
(aux true t1')
end
| uu____1168 -> begin
((t1), (None))
end)))
end)
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
((t1), (None))
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(failwith (let _0_295 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_294 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _0_295 _0_294))))
end))
in (let _0_296 = (whnf env t1)
in (aux false _0_296))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _0_298 = (let _0_297 = (empty_worklist env)
in (base_and_refinement env _0_297 t))
in (FStar_All.pipe_right _0_298 Prims.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _0_299 = (FStar_Syntax_Syntax.null_bv t)
in ((_0_299), (FStar_Syntax_Util.t_true))))


let as_refinement = (fun env wl t -> (

let uu____1260 = (base_and_refinement env wl t)
in (match (uu____1260) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement = (fun uu____1319 -> (match (uu____1319) with
| (t_base, refopt) -> begin
(

let uu____1333 = (match (refopt) with
| Some (y, phi) -> begin
((y), (phi))
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (uu____1333) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl uu___115_1357 -> (match (uu___115_1357) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _0_302 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _0_301 = (FStar_Syntax_Print.term_to_string (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs))
in (let _0_300 = (FStar_Syntax_Print.term_to_string (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _0_302 _0_301 (rel_to_string p.FStar_TypeChecker_Common.relation) _0_300))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _0_305 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _0_304 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _0_303 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _0_305 _0_304 (rel_to_string p.FStar_TypeChecker_Common.relation) _0_303))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _0_308 = (let _0_307 = (let _0_306 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun uu____1376 -> (match (uu____1376) with
| (uu____1380, uu____1381, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _0_306))
in (FStar_List.map (wl_prob_to_string wl) _0_307))
in (FStar_All.pipe_right _0_308 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let uu____1398 = (

let uu____1408 = (FStar_Syntax_Subst.compress k).FStar_Syntax_Syntax.n
in (match (uu____1408) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (((FStar_List.length bs) = (FStar_List.length ys))) with
| true -> begin
(let _0_309 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (_0_309)))
end
| uu____1457 -> begin
(

let uu____1458 = (FStar_Syntax_Util.abs_formals t)
in (match (uu____1458) with
| (ys', t, uu____1479) -> begin
(let _0_310 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t))), (_0_310)))
end))
end)
end
| uu____1507 -> begin
(let _0_312 = (let _0_311 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_0_311)))
in ((((ys), (t))), (_0_312)))
end))
in (match (uu____1398) with
| ((ys, t), (xs, c)) -> begin
(match (((FStar_List.length xs) <> (FStar_List.length ys))) with
| true -> begin
(FStar_Syntax_Util.abs ys t (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ([]))))))
end
| uu____1560 -> begin
(

let c = (let _0_313 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp _0_313 c))
in (let _0_317 = (let _0_316 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_314 -> FStar_Util.Inl (_0_314)))
in (FStar_All.pipe_right _0_316 (fun _0_315 -> Some (_0_315))))
in (FStar_Syntax_Util.abs ys t _0_317)))
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

let uu____1607 = (p_guard prob)
in (match (uu____1607) with
| (uu____1610, uv) -> begin
((

let uu____1613 = (FStar_Syntax_Subst.compress uv).FStar_Syntax_Syntax.n
in (match (uu____1613) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi = (u_abs k bs phi)
in ((

let uu____1631 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))
in (match (uu____1631) with
| true -> begin
(let _0_320 = (FStar_Util.string_of_int (p_pid prob))
in (let _0_319 = (FStar_Syntax_Print.term_to_string uv)
in (let _0_318 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _0_320 _0_319 _0_318))))
end
| uu____1632 -> begin
()
end));
(FStar_Syntax_Util.set_uvar uvar phi);
)))
end
| uu____1635 -> begin
(match ((not (resolve_ok))) with
| true -> begin
(failwith "Impossible: this instance has already been assigned a solution")
end
| uu____1636 -> begin
()
end)
end));
(commit uvis);
(

let uu___134_1638 = wl
in {attempting = uu___134_1638.attempting; wl_deferred = uu___134_1638.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___134_1638.defer_ok; smt_ok = uu___134_1638.smt_ok; tcenv = uu___134_1638.tcenv});
)
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> ((

let uu____1651 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____1651) with
| true -> begin
(let _0_323 = (FStar_Util.string_of_int pid)
in (let _0_322 = (let _0_321 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _0_321 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _0_323 _0_322)))
end
| uu____1653 -> begin
()
end));
(commit sol);
(

let uu___135_1655 = wl
in {attempting = uu___135_1655.attempting; wl_deferred = uu___135_1655.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___135_1655.defer_ok; smt_ok = uu___135_1655.smt_ok; tcenv = uu___135_1655.tcenv});
))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard = (fun t g -> (match (((t), (g))) with
| (uu____1684, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some ((FStar_Syntax_Util.mk_conj t f))
end))
in ((

let uu____1695 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck")))
in (match (uu____1695) with
| true -> begin
(let _0_326 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _0_325 = (let _0_324 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _0_324 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _0_326 _0_325)))
end
| uu____1697 -> begin
()
end));
(solve_prob' false prob logical_guard uvis wl);
)))


let rec occurs = (fun wl uk t -> (let _0_328 = (let _0_327 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _0_327 FStar_Util.set_elements))
in (FStar_All.pipe_right _0_328 (FStar_Util.for_some (fun uu____1736 -> (match (uu____1736) with
| (uv, uu____1744) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (not ((occurs wl uk t)))
in (

let msg = (match (occurs_ok) with
| true -> begin
None
end
| uu____1791 -> begin
Some ((let _0_330 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _0_329 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _0_330 _0_329))))
end)
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let uu____1842 = (occurs_check env wl uk t)
in (match (uu____1842) with
| (occurs_ok, msg) -> begin
(let _0_331 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (_0_331), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set v1)
in (

let uu____1922 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun uu____1946 uu____1947 -> (match (((uu____1946), (uu____1947))) with
| ((isect, isect_set), (x, imp)) -> begin
(

let uu____1990 = (let _0_332 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _0_332))
in (match (uu____1990) with
| true -> begin
((isect), (isect_set))
end
| uu____2001 -> begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in (

let uu____2004 = (FStar_Util.set_is_subset_of fvs isect_set)
in (match (uu____2004) with
| true -> begin
(let _0_333 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (_0_333)))
end
| uu____2017 -> begin
((isect), (isect_set))
end)))
end))
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (uu____1922) with
| (isect, uu____2031) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun uu____2080 uu____2081 -> (match (((uu____2080), (uu____2081))) with
| ((a, uu____2091), (b, uu____2093)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(

let uu____2137 = (FStar_All.pipe_right seen (FStar_Util.for_some (fun uu____2143 -> (match (uu____2143) with
| (b, uu____2147) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end))))
in (match (uu____2137) with
| true -> begin
None
end
| uu____2153 -> begin
Some (((a), ((Prims.snd hd))))
end))
end
| uu____2156 -> begin
None
end)))


let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| (hd)::rest -> begin
(

let uu____2199 = (pat_var_opt env seen hd)
in (match (uu____2199) with
| None -> begin
((

let uu____2207 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____2207) with
| true -> begin
(let _0_334 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _0_334))
end
| uu____2208 -> begin
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

let uu____2219 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____2219) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
true
end
| uu____2233 -> begin
false
end)))


let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = uu____2295; FStar_Syntax_Syntax.pos = uu____2296; FStar_Syntax_Syntax.vars = uu____2297}, args) -> begin
((t), (uv), (k), (args))
end
| uu____2338 -> begin
(failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let uu____2392 = (destruct_flex_t t)
in (match (uu____2392) with
| (t, uv, k, args) -> begin
(

let uu____2460 = (pat_vars env [] args)
in (match (uu____2460) with
| Some (vars) -> begin
((((t), (uv), (k), (args))), (Some (vars)))
end
| uu____2516 -> begin
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
| uu____2564 -> begin
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
| uu____2587 -> begin
false
end))


let uu___is_FullMatch : match_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullMatch -> begin
true
end
| uu____2591 -> begin
false
end))


let head_match : match_result  ->  match_result = (fun uu___116_2594 -> (match (uu___116_2594) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| uu____2603 -> begin
HeadMatch
end))


let fv_delta_depth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.delta_depth = (fun env fv -> (match (fv.FStar_Syntax_Syntax.fv_delta) with
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(match ((env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)) with
| true -> begin
d
end
| uu____2615 -> begin
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
| uu____2688 -> begin
MisMatch (((None), (None)))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____2693 = (FStar_Syntax_Syntax.fv_eq f g)
in (match (uu____2693) with
| true -> begin
FullMatch
end
| uu____2694 -> begin
MisMatch (((Some ((fv_delta_depth env f))), (Some ((fv_delta_depth env g)))))
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, uu____2698), FStar_Syntax_Syntax.Tm_uinst (g, uu____2700)) -> begin
(let _0_335 = (head_matches env f g)
in (FStar_All.pipe_right _0_335 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(match ((c = d)) with
| true -> begin
FullMatch
end
| uu____2711 -> begin
MisMatch (((None), (None)))
end)
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, uu____2715), FStar_Syntax_Syntax.Tm_uvar (uv', uu____2717)) -> begin
(

let uu____2742 = (FStar_Unionfind.equivalent uv uv')
in (match (uu____2742) with
| true -> begin
FullMatch
end
| uu____2746 -> begin
MisMatch (((None), (None)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____2750), FStar_Syntax_Syntax.Tm_refine (y, uu____2752)) -> begin
(let _0_336 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _0_336 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____2762), uu____2763) -> begin
(let _0_337 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _0_337 head_match))
end
| (uu____2768, FStar_Syntax_Syntax.Tm_refine (x, uu____2770)) -> begin
(let _0_338 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _0_338 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, uu____2780), FStar_Syntax_Syntax.Tm_app (head', uu____2782)) -> begin
(let _0_339 = (head_matches env head head')
in (FStar_All.pipe_right _0_339 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head, uu____2812), uu____2813) -> begin
(let _0_340 = (head_matches env head t2)
in (FStar_All.pipe_right _0_340 head_match))
end
| (uu____2828, FStar_Syntax_Syntax.Tm_app (head, uu____2830)) -> begin
(let _0_341 = (head_matches env t1 head)
in (FStar_All.pipe_right _0_341 head_match))
end
| uu____2845 -> begin
MisMatch ((let _0_343 = (delta_depth_of_term env t1)
in (let _0_342 = (delta_depth_of_term env t2)
in ((_0_343), (_0_342)))))
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let uu____2882 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____2882) with
| (head, uu____2894) -> begin
(

let uu____2909 = (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
in (match (uu____2909) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____2912 = (let _0_344 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _0_344 FStar_Option.isSome))
in (match (uu____2912) with
| true -> begin
(let _0_346 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right _0_346 (fun _0_345 -> Some (_0_345))))
end
| uu____2924 -> begin
None
end))
end
| uu____2925 -> begin
None
end))
end)))
in (

let success = (fun d r t1 t2 -> ((r), ((match ((d > (Prims.parse_int "0"))) with
| true -> begin
Some (((t1), (t2)))
end
| uu____2952 -> begin
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
| uu____3004 -> begin
(

let uu____3005 = (let _0_348 = (maybe_inline t1)
in (let _0_347 = (maybe_inline t2)
in ((_0_348), (_0_347))))
in (match (uu____3005) with
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

let uu____3033 = (FStar_TypeChecker_Common.decr_delta_depth d1)
in (match (uu____3033) with
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

let uu____3048 = (match (d1_greater_than_d2) with
| true -> begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in ((t1'), (t2)))
end
| uu____3054 -> begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (let _0_349 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in ((t1), (_0_349))))
end)
in (match (uu____3048) with
| (t1, t2) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t1 t2)
end)))
end
| MisMatch (uu____3063) -> begin
(fail r)
end
| uu____3068 -> begin
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
| uu____3093 -> begin
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
| uu____3123 -> begin
false
end))


let __proj__C__item___0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_0) -> begin
_0
end))


type tcs =
tc Prims.list


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let uu____3138 = (FStar_Syntax_Util.type_u ())
in (match (uu____3138) with
| (t, uu____3142) -> begin
(Prims.fst (new_uvar r binders t))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (let _0_350 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_350 Prims.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (

let uu____3188 = (head_matches env t t')
in (match (uu____3188) with
| MisMatch (uu____3189) -> begin
false
end
| uu____3194 -> begin
true
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(

let rebuild = (fun args' -> (

let args = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((uu____3254, imp), T (t, uu____3257)) -> begin
((t), (imp))
end
| uu____3274 -> begin
(failwith "Bad reconstruction")
end)) args args')
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), (args))))) None t.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun uu____3318 -> (match (uu____3318) with
| (t, uu____3326) -> begin
((None), (INVARIANT), (T (((t), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let fail = (fun uu____3359 -> (failwith "Bad reconstruction"))
in (

let uu____3360 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3360) with
| (bs, c) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs tcs -> (match (((bs), (tcs))) with
| (((x, imp))::bs, (T (t, uu____3413))::tcs) -> begin
(aux (((((

let uu___136_3435 = x
in {FStar_Syntax_Syntax.ppname = uu___136_3435.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___136_3435.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp)))::out) bs tcs)
end
| ([], (C (c))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| uu____3445 -> begin
(failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (

let rec decompose = (fun out uu___117_3476 -> (match (uu___117_3476) with
| [] -> begin
(FStar_List.rev ((((None), (COVARIANT), (C (c))))::out))
end
| (hd)::rest -> begin
(decompose ((((Some (hd)), (CONTRAVARIANT), (T ((((Prims.fst hd).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (let _0_351 = (decompose [] bs)
in ((rebuild), (matches), (_0_351)))))
end)))
end
| uu____3559 -> begin
(

let rebuild = (fun uu___118_3564 -> (match (uu___118_3564) with
| [] -> begin
t
end
| uu____3566 -> begin
(failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t -> true)), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun uu___119_3585 -> (match (uu___119_3585) with
| T (t, uu____3587) -> begin
t
end
| uu____3596 -> begin
(failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun uu___120_3599 -> (match (uu___120_3599) with
| T (t, uu____3601) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| uu____3610 -> begin
(failwith "Impossible")
end))


let imitation_sub_probs = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope args q -> (match (q) with
| (uu____3691, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope r)
in (

let uu____3710 = (new_uvar r scope k)
in (match (uu____3710) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| uu____3722 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) None r)
end)
in (let _0_354 = (let _0_353 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _0_352 -> FStar_TypeChecker_Common.TProb (_0_352)) _0_353))
in ((T (((gi_xs), (mk_kind)))), (_0_354))))
end)))
end
| (uu____3743, uu____3744, C (uu____3745)) -> begin
(failwith "impos")
end))
in (

let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs -> begin
(

let uu____3832 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.tk = uu____3843; FStar_Syntax_Syntax.pos = uu____3844; FStar_Syntax_Syntax.vars = uu____3845})) -> begin
(

let uu____3860 = (sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____3860) with
| (T (gi_xs, uu____3876), prob) -> begin
(let _0_357 = (let _0_356 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_355 -> C (_0_355)) _0_356))
in ((_0_357), ((prob)::[])))
end
| uu____3887 -> begin
(failwith "impossible")
end))
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.tk = uu____3897; FStar_Syntax_Syntax.pos = uu____3898; FStar_Syntax_Syntax.vars = uu____3899})) -> begin
(

let uu____3914 = (sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))
in (match (uu____3914) with
| (T (gi_xs, uu____3930), prob) -> begin
(let _0_360 = (let _0_359 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _0_358 -> C (_0_358)) _0_359))
in ((_0_360), ((prob)::[])))
end
| uu____3941 -> begin
(failwith "impossible")
end))
end
| (uu____3947, uu____3948, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = uu____3950; FStar_Syntax_Syntax.pos = uu____3951; FStar_Syntax_Syntax.vars = uu____3952})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((None), (INVARIANT), (T ((((Prims.fst t)), (generic_kind))))))))
in (

let components = (((None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let uu____4026 = (let _0_361 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _0_361 FStar_List.unzip))
in (match (uu____4026) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (let _0_366 = (let _0_365 = (let _0_362 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _0_362 un_T))
in (let _0_364 = (let _0_363 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _0_363 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _0_365; FStar_Syntax_Syntax.effect_args = _0_364; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _0_366))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| uu____4059 -> begin
(

let uu____4066 = (sub_prob scope args q)
in (match (uu____4066) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (uu____3832) with
| (tc, probs) -> begin
(

let uu____4084 = (match (q) with
| (Some (b), uu____4110, uu____4111) -> begin
(let _0_368 = (let _0_367 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_0_367)::args)
in ((Some (b)), ((b)::scope), (_0_368)))
end
| uu____4134 -> begin
((None), (scope), (args))
end)
in (match (uu____4084) with
| (bopt, scope, args) -> begin
(

let uu____4177 = (aux scope args qs)
in (match (uu____4177) with
| (sub_probs, tcs, f) -> begin
(

let f = (match (bopt) with
| None -> begin
(FStar_Syntax_Util.mk_conj_l (let _0_369 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_0_369))
end
| Some (b) -> begin
(FStar_Syntax_Util.mk_conj_l (let _0_371 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _0_370 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_0_371)::_0_370)))
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

let uu___137_4259 = p
in (let _0_373 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _0_372 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = uu___137_4259.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _0_373; FStar_TypeChecker_Common.relation = uu___137_4259.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _0_372; FStar_TypeChecker_Common.element = uu___137_4259.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___137_4259.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___137_4259.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___137_4259.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___137_4259.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___137_4259.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _0_375 = (compress_tprob wl p)
in (FStar_All.pipe_right _0_375 (fun _0_374 -> FStar_TypeChecker_Common.TProb (_0_374))))
end
| FStar_TypeChecker_Common.CProb (uu____4273) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (let _0_376 = (compress_prob wl pr)
in (FStar_All.pipe_right _0_376 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let uu____4292 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____4292) with
| (lh, uu____4305) -> begin
(

let uu____4320 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____4320) with
| (rh, uu____4333) -> begin
(

let uu____4348 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____4357), FStar_Syntax_Syntax.Tm_uvar (uu____4358)) -> begin
((flex_flex), (tp))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when ((tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____4383), uu____4384) -> begin
(

let uu____4393 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (uu____4393) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((flex_rigid), (tp))
end
| uu____4433 -> begin
(

let rank = (

let uu____4440 = (is_top_level_prob prob)
in (match (uu____4440) with
| true -> begin
flex_refine
end
| uu____4441 -> begin
flex_refine_inner
end))
in (let _0_378 = (

let uu___138_4444 = tp
in (let _0_377 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___138_4444.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___138_4444.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___138_4444.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _0_377; FStar_TypeChecker_Common.element = uu___138_4444.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___138_4444.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___138_4444.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___138_4444.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___138_4444.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___138_4444.FStar_TypeChecker_Common.rank}))
in ((rank), (_0_378))))
end)
end))
end
| (uu____4454, FStar_Syntax_Syntax.Tm_uvar (uu____4455)) -> begin
(

let uu____4464 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (uu____4464) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((rigid_flex), (tp))
end
| uu____4504 -> begin
(let _0_380 = (

let uu___139_4514 = tp
in (let _0_379 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = uu___139_4514.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _0_379; FStar_TypeChecker_Common.relation = uu___139_4514.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___139_4514.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___139_4514.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___139_4514.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___139_4514.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___139_4514.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___139_4514.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___139_4514.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (_0_380)))
end)
end))
end
| (uu____4526, uu____4527) -> begin
((rigid_rigid), (tp))
end)
in (match (uu____4348) with
| (rank, tp) -> begin
(let _0_382 = (FStar_All.pipe_right (

let uu___140_4540 = tp
in {FStar_TypeChecker_Common.pid = uu___140_4540.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___140_4540.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___140_4540.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___140_4540.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___140_4540.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___140_4540.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___140_4540.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___140_4540.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___140_4540.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _0_381 -> FStar_TypeChecker_Common.TProb (_0_381)))
in ((rank), (_0_382)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _0_384 = (FStar_All.pipe_right (

let uu___141_4548 = cp
in {FStar_TypeChecker_Common.pid = uu___141_4548.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___141_4548.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___141_4548.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___141_4548.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___141_4548.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___141_4548.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___141_4548.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___141_4548.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___141_4548.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _0_383 -> FStar_TypeChecker_Common.CProb (_0_383)))
in ((rigid_rigid), (_0_384)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun uu____4580 probs -> (match (uu____4580) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
((min), (out), (min_rank))
end
| (hd)::tl -> begin
(

let uu____4610 = (rank wl hd)
in (match (uu____4610) with
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
| uu____4635 -> begin
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
| uu____4651 -> begin
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
| uu____4675 -> begin
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
| uu____4687 -> begin
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
| uu____4699 -> begin
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

let uu____4736 = (FStar_Syntax_Util.univ_kernel u)
in (match (uu____4736) with
| (k, uu____4740) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| uu____4745 -> begin
false
end)
end)))))
end
| uu____4746 -> begin
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

let uu____4789 = (really_solve_universe_eq orig wl u1 u2)
in (match (uu____4789) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed -> begin
failed
end))
end
| uu____4792 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end
| uu____4797 -> begin
UFailed ((let _0_386 = (FStar_Syntax_Print.univ_to_string u1)
in (let _0_385 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _0_386 _0_385))))
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

let uu____4814 = (really_solve_universe_eq orig wl u u')
in (match (uu____4814) with
| USolved (wl) -> begin
(aux wl us)
end
| failed -> begin
failed
end))
end))
in (aux wl us))
end
| uu____4817 -> begin
UFailed ((let _0_388 = (FStar_Syntax_Print.univ_to_string u1)
in (let _0_387 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _0_388 _0_387 msg))))
end))
in (match (((u1), (u2))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(failwith (let _0_390 = (FStar_Syntax_Print.univ_to_string u1)
in (let _0_389 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" _0_390 _0_389))))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
(match ((x.FStar_Ident.idText = y.FStar_Ident.idText)) with
| true -> begin
USolved (wl)
end
| uu____4828 -> begin
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

let uu____4837 = (FStar_Unionfind.equivalent v1 v2)
in (match (uu____4837) with
| true -> begin
USolved (wl)
end
| uu____4839 -> begin
(

let wl = (extend_solution orig ((UNIV (((v1), (u2))))::[]) wl)
in USolved (wl))
end))
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(

let u = (norm_univ wl u)
in (

let uu____4850 = (occurs_univ v1 u)
in (match (uu____4850) with
| true -> begin
(let _0_393 = (let _0_392 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _0_391 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _0_392 _0_391)))
in (try_umax_components u1 u2 _0_393))
end
| uu____4851 -> begin
USolved ((extend_solution orig ((UNIV (((v1), (u))))::[]) wl))
end)))
end
| ((FStar_Syntax_Syntax.U_max (_), _)) | ((_, FStar_Syntax_Syntax.U_max (_))) -> begin
(match (wl.defer_ok) with
| true -> begin
UDeferred (wl)
end
| uu____4858 -> begin
(

let u1 = (norm_univ wl u1)
in (

let u2 = (norm_univ wl u2)
in (

let uu____4861 = (FStar_Syntax_Util.eq_univs u1 u2)
in (match (uu____4861) with
| true -> begin
USolved (wl)
end
| uu____4862 -> begin
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
| uu____4883 -> begin
(really_solve_universe_eq orig wl u1 u2)
end))


let match_num_binders = (fun bc1 bc2 -> (

let uu____4932 = bc1
in (match (uu____4932) with
| (bs1, mk_cod1) -> begin
(

let uu____4957 = bc2
in (match (uu____4957) with
| (bs2, mk_cod2) -> begin
(

let curry = (fun n bs mk_cod -> (

let uu____5004 = (FStar_Util.first_N n bs)
in (match (uu____5004) with
| (bs, rest) -> begin
(let _0_394 = (mk_cod rest)
in ((bs), (_0_394)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(let _0_398 = (let _0_395 = (mk_cod1 [])
in ((bs1), (_0_395)))
in (let _0_397 = (let _0_396 = (mk_cod2 [])
in ((bs2), (_0_396)))
in ((_0_398), (_0_397))))
end
| uu____5043 -> begin
(match ((l1 > l2)) with
| true -> begin
(let _0_401 = (curry l2 bs1 mk_cod1)
in (let _0_400 = (let _0_399 = (mk_cod2 [])
in ((bs2), (_0_399)))
in ((_0_401), (_0_400))))
end
| uu____5067 -> begin
(let _0_404 = (let _0_402 = (mk_cod1 [])
in ((bs1), (_0_402)))
in (let _0_403 = (curry l1 bs2 mk_cod2)
in ((_0_404), (_0_403))))
end)
end))))
end))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> ((

let uu____5169 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5169) with
| true -> begin
(let _0_405 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _0_405))
end
| uu____5170 -> begin
()
end));
(

let uu____5171 = (next_prob probs)
in (match (uu____5171) with
| (Some (hd), tl, rank) -> begin
(

let probs = (

let uu___142_5184 = probs
in {attempting = tl; wl_deferred = uu___142_5184.wl_deferred; ctr = uu___142_5184.ctr; defer_ok = uu___142_5184.defer_ok; smt_ok = uu___142_5184.smt_ok; tcenv = uu___142_5184.tcenv})
in (match (hd) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match ((((not (probs.defer_ok)) && (flex_refine_inner <= rank)) && (rank <= flex_rigid))) with
| true -> begin
(

let uu____5191 = (solve_flex_rigid_join env tp probs)
in (match (uu____5191) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end))
end
| uu____5194 -> begin
(match ((((not (probs.defer_ok)) && (rigid_flex <= rank)) && (rank <= refine_flex))) with
| true -> begin
(

let uu____5195 = (solve_rigid_flex_meet env tp probs)
in (match (uu____5195) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end))
end
| uu____5198 -> begin
(solve_t' env (maybe_invert tp) probs)
end)
end)
end))
end
| (None, uu____5199, uu____5200) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| uu____5209 -> begin
(

let uu____5214 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun uu____5242 -> (match (uu____5242) with
| (c, uu____5247, uu____5248) -> begin
(c < probs.ctr)
end))))
in (match (uu____5214) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
Success ((FStar_List.map (fun uu____5275 -> (match (uu____5275) with
| (uu____5281, x, y) -> begin
((x), (y))
end)) probs.wl_deferred))
end
| uu____5284 -> begin
(let _0_407 = (

let uu___143_5289 = probs
in (let _0_406 = (FStar_All.pipe_right attempt (FStar_List.map (fun uu____5298 -> (match (uu____5298) with
| (uu____5302, uu____5303, y) -> begin
y
end))))
in {attempting = _0_406; wl_deferred = rest; ctr = uu___143_5289.ctr; defer_ok = uu___143_5289.defer_ok; smt_ok = uu___143_5289.smt_ok; tcenv = uu___143_5289.tcenv}))
in (solve env _0_407))
end)
end))
end)
end));
))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (

let uu____5310 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____5310) with
| USolved (wl) -> begin
(let _0_408 = (solve_prob orig None [] wl)
in (solve env _0_408))
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

let uu____5345 = (solve_universe_eq (p_pid orig) wl u1 u2)
in (match (uu____5345) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed_or_deferred -> begin
failed_or_deferred
end))
end
| uu____5348 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t1 = (whnf env t1)
in (

let t2 = (whnf env t2)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = uu____5356; FStar_Syntax_Syntax.pos = uu____5357; FStar_Syntax_Syntax.vars = uu____5358}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = uu____5361; FStar_Syntax_Syntax.pos = uu____5362; FStar_Syntax_Syntax.vars = uu____5363}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (aux wl us1 us2))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(failwith "Impossible: expect head symbols to match")
end
| uu____5379 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> (match (wl.defer_ok) with
| true -> begin
((

let uu____5387 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____5387) with
| true -> begin
(let _0_409 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _0_409 msg))
end
| uu____5388 -> begin
()
end));
(solve env (defer msg orig wl));
)
end
| uu____5389 -> begin
(giveup env msg orig)
end))
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> ((

let uu____5395 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5395) with
| true -> begin
(let _0_410 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" _0_410))
end
| uu____5396 -> begin
()
end));
(

let uu____5397 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____5397) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let uu____5439 = (head_matches_delta env () t1 t2)
in (match (uu____5439) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (uu____5461) -> begin
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

let uu____5487 = (match (ts) with
| Some (t1, t2) -> begin
(let _0_412 = (FStar_Syntax_Subst.compress t1)
in (let _0_411 = (FStar_Syntax_Subst.compress t2)
in ((_0_412), (_0_411))))
end
| None -> begin
(let _0_414 = (FStar_Syntax_Subst.compress t1)
in (let _0_413 = (FStar_Syntax_Subst.compress t2)
in ((_0_414), (_0_413))))
end)
in (match (uu____5487) with
| (t1, t2) -> begin
(

let eq_prob = (fun t1 t2 -> (let _0_416 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _0_415 -> FStar_TypeChecker_Common.TProb (_0_415)) _0_416)))
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
Some ((let _0_420 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((let _0_417 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (_0_417)))))) None t1.FStar_Syntax_Syntax.pos)
in (let _0_419 = (let _0_418 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (_0_418)::[])
in ((_0_420), (_0_419)))))
end
| (uu____5561, FStar_Syntax_Syntax.Tm_refine (x, uu____5563)) -> begin
Some ((let _0_422 = (let _0_421 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (_0_421)::[])
in ((t1), (_0_422))))
end
| (FStar_Syntax_Syntax.Tm_refine (x, uu____5573), uu____5574) -> begin
Some ((let _0_424 = (let _0_423 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (_0_423)::[])
in ((t2), (_0_424))))
end
| uu____5583 -> begin
(

let uu____5586 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____5586) with
| (head1, uu____5601) -> begin
(

let uu____5616 = (FStar_Syntax_Util.un_uinst head1).FStar_Syntax_Syntax.n
in (match (uu____5616) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____5621; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (i); FStar_Syntax_Syntax.fv_qual = uu____5623}) -> begin
(

let prev = (match ((i > (Prims.parse_int "1"))) with
| true -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i - (Prims.parse_int "1")))
end
| uu____5629 -> begin
FStar_Syntax_Syntax.Delta_constant
end)
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t1)
in (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t2)
in (disjoin t1 t2))))
end
| uu____5632 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____5641) -> begin
(

let uu____5654 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___121_5663 -> (match (uu___121_5663) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(

let uu____5668 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (uu____5668) with
| (u', uu____5679) -> begin
(

let uu____5694 = (whnf env u').FStar_Syntax_Syntax.n
in (match (uu____5694) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____5696) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____5712 -> begin
false
end))
end))
end
| uu____5713 -> begin
false
end)
end
| uu____5715 -> begin
false
end))))
in (match (uu____5654) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun uu____5736 tps -> (match (uu____5736) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(

let uu____5763 = (let _0_425 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound _0_425))
in (match (uu____5763) with
| Some (bound, sub) -> begin
(make_lower_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end))
end
| uu____5786 -> begin
None
end)
end))
in (

let uu____5791 = (let _0_427 = (let _0_426 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((_0_426), ([])))
in (make_lower_bound _0_427 lower_bounds))
in (match (uu____5791) with
| None -> begin
((

let uu____5802 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5802) with
| true -> begin
(FStar_Util.print_string "No lower bounds\n")
end
| uu____5803 -> begin
()
end));
None;
)
end
| Some (lhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in ((

let uu____5815 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5815) with
| true -> begin
(

let wl' = (

let uu___144_5817 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___144_5817.wl_deferred; ctr = uu___144_5817.ctr; defer_ok = uu___144_5817.defer_ok; smt_ok = uu___144_5817.smt_ok; tcenv = uu___144_5817.tcenv})
in (let _0_428 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" _0_428)))
end
| uu____5818 -> begin
()
end));
(

let uu____5819 = (solve_t env eq_prob (

let uu___145_5820 = wl
in {attempting = sub_probs; wl_deferred = uu___145_5820.wl_deferred; ctr = uu___145_5820.ctr; defer_ok = uu___145_5820.defer_ok; smt_ok = uu___145_5820.smt_ok; tcenv = uu___145_5820.tcenv}))
in (match (uu____5819) with
| Success (uu____5822) -> begin
(

let wl = (

let uu___146_5824 = wl
in {attempting = rest; wl_deferred = uu___146_5824.wl_deferred; ctr = uu___146_5824.ctr; defer_ok = uu___146_5824.defer_ok; smt_ok = uu___146_5824.smt_ok; tcenv = uu___146_5824.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let uu____5826 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| uu____5829 -> begin
None
end));
))
end)))
end))
end
| uu____5830 -> begin
(failwith "Impossible: Not a rigid-flex")
end)))
end));
))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> ((

let uu____5837 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____5837) with
| true -> begin
(let _0_429 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _0_429))
end
| uu____5838 -> begin
()
end));
(

let uu____5839 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____5839) with
| (u, args) -> begin
(

let uu____5866 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (uu____5866) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(

let max = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____5885 -> begin
i
end))
in (

let base_types_match = (fun t1 t2 -> (

let uu____5897 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____5897) with
| (h1, args1) -> begin
(

let uu____5925 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____5925) with
| (h2, uu____5938) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
(

let uu____5957 = (FStar_Syntax_Syntax.fv_eq tc1 tc2)
in (match (uu____5957) with
| true -> begin
(match (((FStar_List.length args1) = (Prims.parse_int "0"))) with
| true -> begin
Some ([])
end
| uu____5969 -> begin
Some ((let _0_432 = (let _0_431 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_430 -> FStar_TypeChecker_Common.TProb (_0_430)) _0_431))
in (_0_432)::[]))
end)
end
| uu____5973 -> begin
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
| uu____5988 -> begin
Some ((let _0_435 = (let _0_434 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _0_433 -> FStar_TypeChecker_Common.TProb (_0_433)) _0_434))
in (_0_435)::[]))
end)
end
| uu____5992 -> begin
None
end)
end
| uu____5994 -> begin
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
in Some ((let _0_437 = (let _0_436 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _0_436))
in ((_0_437), (m))))))))
end))
end
| (uu____6068, FStar_Syntax_Syntax.Tm_refine (y, uu____6070)) -> begin
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
| (FStar_Syntax_Syntax.Tm_refine (x, uu____6102), uu____6103) -> begin
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
| uu____6134 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____6168) -> begin
(

let uu____6181 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun uu___122_6190 -> (match (uu___122_6190) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(

let uu____6195 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (uu____6195) with
| (u', uu____6206) -> begin
(

let uu____6221 = (whnf env u').FStar_Syntax_Syntax.n
in (match (uu____6221) with
| FStar_Syntax_Syntax.Tm_uvar (uv', uu____6223) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| uu____6239 -> begin
false
end))
end))
end
| uu____6240 -> begin
false
end)
end
| uu____6242 -> begin
false
end))))
in (match (uu____6181) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun uu____6267 tps -> (match (uu____6267) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(

let uu____6308 = (let _0_438 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _0_438))
in (match (uu____6308) with
| Some (bound, sub) -> begin
(make_upper_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end))
end
| uu____6347 -> begin
None
end)
end))
in (

let uu____6354 = (let _0_440 = (let _0_439 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((_0_439), ([])))
in (make_upper_bound _0_440 upper_bounds))
in (match (uu____6354) with
| None -> begin
((

let uu____6369 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6369) with
| true -> begin
(FStar_Util.print_string "No upper bounds\n")
end
| uu____6370 -> begin
()
end));
None;
)
end
| Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in ((

let uu____6388 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____6388) with
| true -> begin
(

let wl' = (

let uu___147_6390 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = uu___147_6390.wl_deferred; ctr = uu___147_6390.ctr; defer_ok = uu___147_6390.defer_ok; smt_ok = uu___147_6390.smt_ok; tcenv = uu___147_6390.tcenv})
in (let _0_441 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _0_441)))
end
| uu____6391 -> begin
()
end));
(

let uu____6392 = (solve_t env eq_prob (

let uu___148_6393 = wl
in {attempting = sub_probs; wl_deferred = uu___148_6393.wl_deferred; ctr = uu___148_6393.ctr; defer_ok = uu___148_6393.defer_ok; smt_ok = uu___148_6393.smt_ok; tcenv = uu___148_6393.tcenv}))
in (match (uu____6392) with
| Success (uu____6395) -> begin
(

let wl = (

let uu___149_6397 = wl
in {attempting = rest; wl_deferred = uu___149_6397.wl_deferred; ctr = uu___149_6397.ctr; defer_ok = uu___149_6397.defer_ok; smt_ok = uu___149_6397.smt_ok; tcenv = uu___149_6397.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let uu____6399 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| uu____6402 -> begin
None
end));
))
end)))
end))
end
| uu____6403 -> begin
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

let uu____6468 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6468) with
| true -> begin
(let _0_442 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _0_442))
end
| uu____6469 -> begin
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

let uu___150_6500 = hd1
in (let _0_443 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___150_6500.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___150_6500.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_443}))
in (

let hd2 = (

let uu___151_6502 = hd2
in (let _0_444 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___151_6502.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___151_6502.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_444}))
in (

let prob = (let _0_447 = (let _0_446 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _0_446 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _0_445 -> FStar_TypeChecker_Common.TProb (_0_445)) _0_447))
in (

let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (

let subst = (let _0_448 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd1))))::_0_448)
in (

let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (

let uu____6512 = (aux ((((hd1), (imp)))::scope) env subst xs ys)
in (match (uu____6512) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi = (let _0_450 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _0_449 = (FStar_Syntax_Util.close_forall ((((hd1), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj _0_450 _0_449)))
in ((

let uu____6537 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6537) with
| true -> begin
(let _0_452 = (FStar_Syntax_Print.term_to_string phi)
in (let _0_451 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _0_452 _0_451)))
end
| uu____6538 -> begin
()
end));
FStar_Util.Inl ((((prob)::sub_probs), (phi)));
))
end
| fail -> begin
fail
end))))))))
end
| uu____6552 -> begin
FStar_Util.Inr ("arity or argument-qualifier mismatch")
end))
in (

let scope = (p_scope orig)
in (

let uu____6558 = (aux scope env [] bs1 bs2)
in (match (uu____6558) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end)))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _0_453 = (compress_tprob wl problem)
in (solve_t' env _0_453 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (

let uu____6606 = (head_matches_delta env wl t1 t2)
in (match (uu____6606) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (uu____6623), uu____6624) -> begin
(

let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____6646 -> begin
false
end))
in (match ((((may_relate head1) || (may_relate head2)) && wl.smt_ok)) with
| true -> begin
(

let guard = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end
| uu____6652 -> begin
(

let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(

let x = (FStar_Syntax_Syntax.new_bv None t1)
in (let _0_455 = (let _0_454 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _0_454 t2))
in (FStar_Syntax_Util.mk_forall x _0_455)))
end))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB)) with
| true -> begin
(has_type_guard t1 t2)
end
| uu____6668 -> begin
(has_type_guard t2 t1)
end))
end)
in (let _0_456 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _0_456)))
end
| uu____6671 -> begin
(giveup env "head mismatch" orig)
end))
end
| (uu____6672, Some (t1, t2)) -> begin
(solve_t env (

let uu___152_6680 = problem
in {FStar_TypeChecker_Common.pid = uu___152_6680.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___152_6680.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___152_6680.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___152_6680.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___152_6680.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___152_6680.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___152_6680.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___152_6680.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____6681, None) -> begin
((

let uu____6688 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____6688) with
| true -> begin
(let _0_460 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_459 = (FStar_Syntax_Print.tag_of_term t1)
in (let _0_458 = (FStar_Syntax_Print.term_to_string t2)
in (let _0_457 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _0_460 _0_459 _0_458 _0_457)))))
end
| uu____6689 -> begin
()
end));
(

let uu____6690 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____6690) with
| (head1, args1) -> begin
(

let uu____6716 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____6716) with
| (head2, args2) -> begin
(

let nargs = (FStar_List.length args1)
in (match ((nargs <> (FStar_List.length args2))) with
| true -> begin
(let _0_465 = (let _0_464 = (FStar_Syntax_Print.term_to_string head1)
in (let _0_463 = (args_to_string args1)
in (let _0_462 = (FStar_Syntax_Print.term_to_string head2)
in (let _0_461 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _0_464 _0_463 _0_462 _0_461)))))
in (giveup env _0_465 orig))
end
| uu____6756 -> begin
(

let uu____6757 = ((nargs = (Prims.parse_int "0")) || (let _0_466 = (FStar_Syntax_Util.eq_args args1 args2)
in (_0_466 = FStar_Syntax_Util.Equal)))
in (match (uu____6757) with
| true -> begin
(

let uu____6760 = (solve_maybe_uinsts env orig head1 head2 wl)
in (match (uu____6760) with
| USolved (wl) -> begin
(let _0_467 = (solve_prob orig None [] wl)
in (solve env _0_467))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end))
end
| uu____6764 -> begin
(

let uu____6765 = (base_and_refinement env wl t1)
in (match (uu____6765) with
| (base1, refinement1) -> begin
(

let uu____6791 = (base_and_refinement env wl t2)
in (match (uu____6791) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (None, None) -> begin
(

let uu____6845 = (solve_maybe_uinsts env orig head1 head2 wl)
in (match (uu____6845) with
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end
| USolved (wl) -> begin
(

let subprobs = (FStar_List.map2 (fun uu____6855 uu____6856 -> (match (((uu____6855), (uu____6856))) with
| ((a, uu____6866), (a', uu____6868)) -> begin
(let _0_469 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _0_468 -> FStar_TypeChecker_Common.TProb (_0_468)) _0_469))
end)) args1 args2)
in (

let formula = (FStar_Syntax_Util.mk_conj_l (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs))
in (

let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end))
end
| uu____6878 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env (

let uu___153_6911 = problem
in {FStar_TypeChecker_Common.pid = uu___153_6911.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = uu___153_6911.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = uu___153_6911.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___153_6911.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___153_6911.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___153_6911.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___153_6911.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___153_6911.FStar_TypeChecker_Common.rank}) wl)))
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

let uu____6931 = p
in (match (uu____6931) with
| (((u, k), xs, c), ps, (h, uu____6942, qs)) -> begin
(

let xs = (sn_binders env xs)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____6991 = (imitation_sub_probs orig env xs ps qs)
in (match (uu____6991) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (let _0_474 = (h gs_xs)
in (let _0_473 = (let _0_472 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_470 -> FStar_Util.Inl (_0_470)))
in (FStar_All.pipe_right _0_472 (fun _0_471 -> Some (_0_471))))
in (FStar_Syntax_Util.abs xs _0_474 _0_473)))
in ((

let uu____7030 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7030) with
| true -> begin
(let _0_481 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _0_480 = (FStar_Syntax_Print.comp_to_string c)
in (let _0_479 = (FStar_Syntax_Print.term_to_string im)
in (let _0_478 = (FStar_Syntax_Print.tag_of_term im)
in (let _0_477 = (let _0_475 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _0_475 (FStar_String.concat ", ")))
in (let _0_476 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" _0_481 _0_480 _0_479 _0_478 _0_477 _0_476)))))))
end
| uu____7032 -> begin
()
end));
(

let wl = (solve_prob orig (Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl)
in (solve env (attempt sub_probs wl)));
))
end))))
end)))
in (

let imitate' = (fun orig env wl uu___123_7049 -> (match (uu___123_7049) with
| None -> begin
(giveup env "unable to compute subterms" orig)
end
| Some (p) -> begin
(imitate orig env wl p)
end))
in (

let project = (fun orig env wl i p -> (

let uu____7078 = p
in (match (uu____7078) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let uu____7136 = (FStar_List.nth ps i)
in (match (uu____7136) with
| (pi, uu____7139) -> begin
(

let uu____7144 = (FStar_List.nth xs i)
in (match (uu____7144) with
| (xi, uu____7151) -> begin
(

let rec gs = (fun k -> (

let uu____7160 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____7160) with
| (bs, k) -> begin
(

let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
(([]), ([]))
end
| ((a, uu____7212))::tl -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (

let uu____7220 = (new_uvar r xs k_a)
in (match (uu____7220) with
| (gi_xs, gi) -> begin
(

let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (

let gi_ps = ((FStar_Syntax_Syntax.mk_Tm_app gi ps) (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst = (FStar_Syntax_Syntax.NT (((a), (gi_xs))))::subst
in (

let uu____7239 = (aux subst tl)
in (match (uu____7239) with
| (gi_xs', gi_ps') -> begin
(let _0_485 = (let _0_482 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_0_482)::gi_xs')
in (let _0_484 = (let _0_483 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_0_483)::gi_ps')
in ((_0_485), (_0_484))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in (

let uu____7256 = (let _0_486 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _0_486))
in (match (uu____7256) with
| true -> begin
None
end
| uu____7258 -> begin
(

let uu____7259 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (uu____7259) with
| (g_xs, uu____7266) -> begin
(

let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (let _0_491 = ((FStar_Syntax_Syntax.mk_Tm_app xi g_xs) None r)
in (let _0_490 = (let _0_489 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_487 -> FStar_Util.Inl (_0_487)))
in (FStar_All.pipe_right _0_489 (fun _0_488 -> Some (_0_488))))
in (FStar_Syntax_Util.abs xs _0_491 _0_490)))
in (

let sub = (let _0_496 = (let _0_495 = ((FStar_Syntax_Syntax.mk_Tm_app proj ps) None r)
in (let _0_494 = (let _0_493 = (FStar_List.map (fun uu____7319 -> (match (uu____7319) with
| (uu____7324, uu____7325, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _0_493))
in (mk_problem (p_scope orig) orig _0_495 (p_rel orig) _0_494 None "projection")))
in (FStar_All.pipe_left (fun _0_492 -> FStar_TypeChecker_Common.TProb (_0_492)) _0_496))
in ((

let uu____7330 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7330) with
| true -> begin
(let _0_498 = (FStar_Syntax_Print.term_to_string proj)
in (let _0_497 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _0_498 _0_497)))
end
| uu____7331 -> begin
()
end));
(

let wl = (let _0_499 = Some ((FStar_All.pipe_left Prims.fst (p_guard sub)))
in (solve_prob orig _0_499 ((TERM (((u), (proj))))::[]) wl))
in (let _0_501 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _0_500 -> Some (_0_500)) _0_501)));
))))
end))
end)))
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl -> (

let uu____7360 = lhs
in (match (uu____7360) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let uu____7383 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (uu____7383) with
| (xs, c) -> begin
(match (((FStar_List.length xs) = (FStar_List.length ps))) with
| true -> begin
Some ((let _0_502 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (_0_502))))
end
| uu____7457 -> begin
(

let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (

let uu____7474 = (let _0_503 = (FStar_Syntax_Subst.compress k).FStar_Syntax_Syntax.n
in ((_0_503), (args)))
in (match (uu____7474) with
| (uu____7482, []) -> begin
Some ((let _0_504 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_0_504))))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(

let uu____7500 = (FStar_Syntax_Util.head_and_args k)
in (match (uu____7500) with
| (uv, uv_args) -> begin
(

let uu____7529 = (FStar_Syntax_Subst.compress uv).FStar_Syntax_Syntax.n
in (match (uu____7529) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____7534) -> begin
(

let uu____7547 = (pat_vars env [] uv_args)
in (match (uu____7547) with
| None -> begin
None
end
| Some (scope) -> begin
(

let xs = (FStar_All.pipe_right args (FStar_List.map (fun uu____7561 -> (let _0_508 = (let _0_507 = (Prims.fst (let _0_506 = (let _0_505 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_505 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _0_506)))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) _0_507))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _0_508)))))
in (

let c = (FStar_Syntax_Syntax.mk_Total (Prims.fst (let _0_510 = (let _0_509 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_509 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _0_510))))
in (

let k' = (FStar_Syntax_Util.arrow xs c)
in (

let uv_sol = (let _0_513 = Some (FStar_Util.Inl ((let _0_512 = (FStar_Syntax_Syntax.mk_Total (let _0_511 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_511 Prims.fst)))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_512))))
in (FStar_Syntax_Util.abs scope k' _0_513))
in ((FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)));
Some (((xs), (c)));
)))))
end))
end
| uu____7591 -> begin
None
end))
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), uu____7596) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs)
in (match ((n_xs = n_args)) with
| true -> begin
(let _0_515 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right _0_515 (fun _0_514 -> Some (_0_514))))
end
| uu____7629 -> begin
(match ((n_xs < n_args)) with
| true -> begin
(

let uu____7638 = (FStar_Util.first_N n_xs args)
in (match (uu____7638) with
| (args, rest) -> begin
(

let uu____7654 = (FStar_Syntax_Subst.open_comp xs c)
in (match (uu____7654) with
| (xs, c) -> begin
(let _0_516 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt _0_516 (fun uu____7669 -> (match (uu____7669) with
| (xs', c) -> begin
Some ((((FStar_List.append xs xs')), (c)))
end))))
end))
end))
end
| uu____7690 -> begin
(

let uu____7691 = (FStar_Util.first_N n_args xs)
in (match (uu____7691) with
| (xs, rest) -> begin
(

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c))))) None k.FStar_Syntax_Syntax.pos)
in (let _0_519 = (let _0_517 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs _0_517))
in (FStar_All.pipe_right _0_519 (fun _0_518 -> Some (_0_518)))))
end))
end)
end)))
end
| uu____7744 -> begin
(failwith (let _0_522 = (FStar_Syntax_Print.uvar_to_string uv)
in (let _0_521 = (FStar_Syntax_Print.term_to_string k)
in (let _0_520 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" _0_522 _0_521 _0_520)))))
end)))
in (let _0_524 = (elim k_uv ps)
in (FStar_Util.bind_opt _0_524 (fun uu____7778 -> (match (uu____7778) with
| (xs, c) -> begin
Some ((let _0_523 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (_0_523))))
end))))))
end)
end)))
in (

let rec imitate_or_project = (fun n stopt i -> (match (((i >= n) || (FStar_Option.isNone stopt))) with
| true -> begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end
| uu____7861 -> begin
(

let st = (FStar_Option.get stopt)
in (

let tx = (FStar_Unionfind.new_transaction ())
in (match ((i = (~- ((Prims.parse_int "1"))))) with
| true -> begin
(

let uu____7864 = (imitate orig env wl st)
in (match (uu____7864) with
| Failed (uu____7869) -> begin
((FStar_Unionfind.rollback tx);
(imitate_or_project n stopt (i + (Prims.parse_int "1")));
)
end
| sol -> begin
sol
end))
end
| uu____7874 -> begin
(

let uu____7875 = (project orig env wl i st)
in (match (uu____7875) with
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

let uu____7893 = (FStar_Syntax_Util.head_and_args t2)
in (match (uu____7893) with
| (hd, uu____7904) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| uu____7922 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd)
in (

let uu____7925 = (FStar_Util.set_is_subset_of fvs_hd fvs1)
in (match (uu____7925) with
| true -> begin
true
end
| uu____7926 -> begin
((

let uu____7928 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7928) with
| true -> begin
(let _0_525 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _0_525))
end
| uu____7929 -> begin
()
end));
false;
)
end)))
end)
end)))
in (

let imitate_ok = (fun t2 -> (

let fvs_hd = (let _0_527 = (let _0_526 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _0_526 Prims.fst))
in (FStar_All.pipe_right _0_527 FStar_Syntax_Free.names))
in (

let uu____7957 = (FStar_Util.set_is_empty fvs_hd)
in (match (uu____7957) with
| true -> begin
(~- ((Prims.parse_int "1")))
end
| uu____7958 -> begin
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

let uu____7966 = (occurs_check env wl ((uv), (k_uv)) t2)
in (match (uu____7966) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(let _0_529 = (let _0_528 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _0_528))
in (giveup_or_defer orig _0_529))
end
| uu____7974 -> begin
(

let uu____7975 = (FStar_Util.set_is_subset_of fvs2 fvs1)
in (match (uu____7975) with
| true -> begin
(

let uu____7976 = (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t2)) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))
in (match (uu____7976) with
| true -> begin
(let _0_530 = (subterms args_lhs)
in (imitate' orig env wl _0_530))
end
| uu____7977 -> begin
((

let uu____7979 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7979) with
| true -> begin
(let _0_533 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_532 = (names_to_string fvs1)
in (let _0_531 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _0_533 _0_532 _0_531))))
end
| uu____7980 -> begin
()
end));
(

let sol = (match (vars) with
| [] -> begin
t2
end
| uu____7984 -> begin
(let _0_534 = (sn_binders env vars)
in (u_abs k_uv _0_534 t2))
end)
in (

let wl = (solve_prob orig None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl)
in (solve env wl)));
)
end))
end
| uu____7988 -> begin
(match ((((not (patterns_only)) && wl.defer_ok) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ))) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end
| uu____7989 -> begin
(

let uu____7990 = ((not (patterns_only)) && (check_head fvs1 t2))
in (match (uu____7990) with
| true -> begin
((

let uu____7992 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____7992) with
| true -> begin
(let _0_537 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_536 = (names_to_string fvs1)
in (let _0_535 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _0_537 _0_536 _0_535))))
end
| uu____7993 -> begin
()
end));
(let _0_538 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _0_538 (~- ((Prims.parse_int "1")))));
)
end
| uu____8001 -> begin
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
| uu____8002 -> begin
(

let uu____8003 = (let _0_539 = (FStar_Syntax_Free.names t1)
in (check_head _0_539 t2))
in (match (uu____8003) with
| true -> begin
(

let im_ok = (imitate_ok t2)
in ((

let uu____8006 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8006) with
| true -> begin
(let _0_540 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _0_540 (match ((im_ok < (Prims.parse_int "0"))) with
| true -> begin
"imitating"
end
| uu____8007 -> begin
"projecting"
end)))
end
| uu____8008 -> begin
()
end));
(let _0_541 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _0_541 im_ok));
))
end
| uu____8016 -> begin
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
| uu____8027 -> begin
(

let force_quasi_pattern = (fun xs_opt uu____8049 -> (match (uu____8049) with
| (t, u, k, args) -> begin
(

let uu____8079 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____8079) with
| (all_formals, uu____8090) -> begin
(

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match (((formals), (args))) with
| ([], []) -> begin
(

let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun uu____8182 -> (match (uu____8182) with
| (x, imp) -> begin
(let _0_542 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_0_542), (imp)))
end))))
in (

let pattern_vars = (FStar_List.rev pattern_vars)
in (

let kk = (

let uu____8196 = (FStar_Syntax_Util.type_u ())
in (match (uu____8196) with
| (t, uu____8200) -> begin
(Prims.fst (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t))
end))
in (

let uu____8201 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (uu____8201) with
| (t', tm_u1) -> begin
(

let uu____8208 = (destruct_flex_t t')
in (match (uu____8208) with
| (uu____8228, u1, k1, uu____8231) -> begin
(

let sol = TERM ((let _0_543 = (u_abs k all_formals t')
in ((((u), (k))), (_0_543))))
in (

let t_app = ((FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args) None t.FStar_Syntax_Syntax.pos)
in ((sol), (((t_app), (u1), (k1), (pat_args))))))
end))
end)))))
end
| ((formal)::formals, (hd)::tl) -> begin
(

let uu____8318 = (pat_var_opt env pat_args hd)
in (match (uu____8318) with
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun uu____8347 -> (match (uu____8347) with
| (x, uu____8351) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in (match ((not (maybe_pat))) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| uu____8354 -> begin
(

let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in (

let uu____8357 = (not ((FStar_Util.set_is_subset_of fvs pattern_var_set)))
in (match (uu____8357) with
| true -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| uu____8360 -> begin
(let _0_544 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _0_544 formals tl))
end)))
end))
end))
end
| uu____8365 -> begin
(failwith "Impossible")
end))
in (let _0_545 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _0_545 all_formals args)))
end))
end))
in (

let solve_both_pats = (fun wl uu____8422 uu____8423 r -> (match (((uu____8422), (uu____8423))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
(

let uu____8577 = ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys))
in (match (uu____8577) with
| true -> begin
(let _0_546 = (solve_prob orig None [] wl)
in (solve env _0_546))
end
| uu____8581 -> begin
(

let xs = (sn_binders env xs)
in (

let ys = (sn_binders env ys)
in (

let zs = (intersect_vars xs ys)
in ((

let uu____8595 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____8595) with
| true -> begin
(let _0_551 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _0_550 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _0_549 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (let _0_548 = (FStar_Syntax_Print.term_to_string k1)
in (let _0_547 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" _0_551 _0_550 _0_549 _0_548 _0_547))))))
end
| uu____8596 -> begin
()
end));
(

let subst_k = (fun k xs args -> (

let xs_len = (FStar_List.length xs)
in (

let args_len = (FStar_List.length args)
in (match ((xs_len = args_len)) with
| true -> begin
(let _0_552 = (FStar_Syntax_Util.subst_of_list xs args)
in (FStar_Syntax_Subst.subst _0_552 k))
end
| uu____8637 -> begin
(match ((args_len < xs_len)) with
| true -> begin
(

let uu____8643 = (FStar_Util.first_N args_len xs)
in (match (uu____8643) with
| (xs, xs_rest) -> begin
(

let k = (let _0_553 = (FStar_Syntax_Syntax.mk_GTotal k)
in (FStar_Syntax_Util.arrow xs_rest _0_553))
in (let _0_554 = (FStar_Syntax_Util.subst_of_list xs args)
in (FStar_Syntax_Subst.subst _0_554 k)))
end))
end
| uu____8673 -> begin
(failwith (let _0_557 = (FStar_Syntax_Print.term_to_string k)
in (let _0_556 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _0_555 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" _0_557 _0_556 _0_555)))))
end)
end))))
in (

let uu____8674 = (

let uu____8680 = (FStar_Syntax_Util.arrow_formals (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1))
in (match (uu____8680) with
| (bs, k1') -> begin
(

let uu____8705 = (FStar_Syntax_Util.arrow_formals (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2))
in (match (uu____8705) with
| (cs, k2') -> begin
(

let k1'_xs = (subst_k k1' bs args1)
in (

let k2'_ys = (subst_k k2' cs args2)
in (

let sub_prob = (let _0_559 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_558 -> FStar_TypeChecker_Common.TProb (_0_558)) _0_559))
in (

let uu____8735 = (let _0_561 = (FStar_Syntax_Subst.compress k1').FStar_Syntax_Syntax.n
in (let _0_560 = (FStar_Syntax_Subst.compress k2').FStar_Syntax_Syntax.n
in ((_0_561), (_0_560))))
in (match (uu____8735) with
| (FStar_Syntax_Syntax.Tm_type (uu____8743), uu____8744) -> begin
((k1'), ((sub_prob)::[]))
end
| (uu____8748, FStar_Syntax_Syntax.Tm_type (uu____8749)) -> begin
((k2'), ((sub_prob)::[]))
end
| uu____8753 -> begin
(

let uu____8756 = (FStar_Syntax_Util.type_u ())
in (match (uu____8756) with
| (t, uu____8765) -> begin
(

let uu____8766 = (new_uvar r zs t)
in (match (uu____8766) with
| (k_zs, uu____8775) -> begin
(

let kprob = (let _0_563 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k_zs None "flex-flex kinding")
in (FStar_All.pipe_left (fun _0_562 -> FStar_TypeChecker_Common.TProb (_0_562)) _0_563))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end)))))
end))
end))
in (match (uu____8674) with
| (k_u', sub_probs) -> begin
(

let uu____8788 = (let _0_569 = (let _0_564 = (new_uvar r zs k_u')
in (FStar_All.pipe_left Prims.fst _0_564))
in (let _0_568 = (let _0_565 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs _0_565))
in (let _0_567 = (let _0_566 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys _0_566))
in ((_0_569), (_0_568), (_0_567)))))
in (match (uu____8788) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs u_zs)
in (

let uu____8814 = (occurs_check env wl ((u1), (k1)) sub1)
in (match (uu____8814) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end
| uu____8826 -> begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in (

let uu____8838 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____8838) with
| true -> begin
(

let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end
| uu____8843 -> begin
(

let sub2 = (u_abs knew2 ys u_zs)
in (

let uu____8845 = (occurs_check env wl ((u2), (k2)) sub2)
in (match (uu____8845) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end
| uu____8857 -> begin
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

let solve_one_pat = (fun uu____8897 uu____8898 -> (match (((uu____8897), (uu____8898))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
((

let uu____9002 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____9002) with
| true -> begin
(let _0_571 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_570 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _0_571 _0_570)))
end
| uu____9003 -> begin
()
end));
(

let uu____9004 = (FStar_Unionfind.equivalent u1 u2)
in (match (uu____9004) with
| true -> begin
(

let sub_probs = (FStar_List.map2 (fun uu____9014 uu____9015 -> (match (((uu____9014), (uu____9015))) with
| ((a, uu____9025), (t2, uu____9027)) -> begin
(let _0_574 = (let _0_572 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _0_572 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _0_574 (fun _0_573 -> FStar_TypeChecker_Common.TProb (_0_573))))
end)) xs args2)
in (

let guard = (FStar_Syntax_Util.mk_conj_l (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end
| uu____9039 -> begin
(

let t2 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t2)
in (

let uu____9043 = (occurs_check env wl ((u1), (k1)) t2)
in (match (uu____9043) with
| (occurs_ok, uu____9052) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in (

let uu____9057 = (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars))
in (match (uu____9057) with
| true -> begin
(

let sol = TERM ((let _0_575 = (u_abs k1 xs t2)
in ((((u1), (k1))), (_0_575))))
in (

let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end
| uu____9070 -> begin
(

let uu____9071 = (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok))
in (match (uu____9071) with
| true -> begin
(

let uu____9072 = (force_quasi_pattern (Some (xs)) ((t2), (u2), (k2), (args2)))
in (match (uu____9072) with
| (sol, (uu____9086, u2, k2, ys)) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____9096 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____9096) with
| true -> begin
(let _0_576 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _0_576))
end
| uu____9097 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| uu____9101 -> begin
(giveup env "impossible" orig)
end);
))
end))
end
| uu____9102 -> begin
(giveup_or_defer orig "flex-flex constraint")
end))
end)))
end))))
end));
)
end))
in (

let uu____9103 = lhs
in (match (uu____9103) with
| (t1, u1, k1, args1) -> begin
(

let uu____9108 = rhs
in (match (uu____9108) with
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
| uu____9134 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end
| uu____9139 -> begin
(

let uu____9140 = (force_quasi_pattern None ((t1), (u1), (k1), (args1)))
in (match (uu____9140) with
| (sol, uu____9147) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in ((

let uu____9150 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern")))
in (match (uu____9150) with
| true -> begin
(let _0_577 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _0_577))
end
| uu____9151 -> begin
()
end));
(match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| uu____9155 -> begin
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

let uu____9157 = (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs)
in (match (uu____9157) with
| true -> begin
(let _0_578 = (solve_prob orig None [] wl)
in (solve env _0_578))
end
| uu____9158 -> begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in (

let uu____9161 = (FStar_Util.physical_equality t1 t2)
in (match (uu____9161) with
| true -> begin
(let _0_579 = (solve_prob orig None [] wl)
in (solve env _0_579))
end
| uu____9162 -> begin
((

let uu____9164 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck")))
in (match (uu____9164) with
| true -> begin
(let _0_580 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _0_580))
end
| uu____9165 -> begin
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

let mk_c = (fun c uu___124_9210 -> (match (uu___124_9210) with
| [] -> begin
c
end
| bs -> begin
(FStar_Syntax_Syntax.mk_Total ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c))))) None c.FStar_Syntax_Syntax.pos))
end))
in (

let uu____9245 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (uu____9245) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (

let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (

let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (

let rel = (

let uu____9331 = (FStar_Options.use_eq_at_higher_order ())
in (match (uu____9331) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____9332 -> begin
problem.FStar_TypeChecker_Common.relation
end))
in (let _0_582 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _0_581 -> FStar_TypeChecker_Common.CProb (_0_581)) _0_582)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l uu___125_9407 -> (match (uu___125_9407) with
| [] -> begin
t
end
| bs -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l))))) None t.FStar_Syntax_Syntax.pos)
end))
in (

let uu____9446 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (uu____9446) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _0_586 = (let _0_585 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _0_584 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _0_585 problem.FStar_TypeChecker_Common.relation _0_584 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _0_583 -> FStar_TypeChecker_Common.TProb (_0_583)) _0_586))))
end)))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (uu____9543) -> begin
true
end
| uu____9558 -> begin
false
end))
in (

let maybe_eta = (fun t -> (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____9577 -> begin
(

let t = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in (match ((is_abs t)) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____9583 -> begin
FStar_Util.Inr (t)
end))
end))
in (

let uu____9586 = (let _0_588 = (maybe_eta t1)
in (let _0_587 = (maybe_eta t2)
in ((_0_588), (_0_587))))
in (match (uu____9586) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(solve_t env (

let uu___154_9623 = problem
in {FStar_TypeChecker_Common.pid = uu___154_9623.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___154_9623.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___154_9623.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___154_9623.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___154_9623.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___154_9623.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___154_9623.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___154_9623.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs))) | ((FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs))) -> begin
(

let uu____9656 = ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ))
in (match (uu____9656) with
| true -> begin
(let _0_589 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig _0_589 t_abs wl))
end
| uu____9657 -> begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end))
end
| uu____9658 -> begin
(failwith "Impossible: at least one side is an abstraction")
end))))
end
| (FStar_Syntax_Syntax.Tm_refine (uu____9669), FStar_Syntax_Syntax.Tm_refine (uu____9670)) -> begin
(

let uu____9679 = (as_refinement env wl t1)
in (match (uu____9679) with
| (x1, phi1) -> begin
(

let uu____9684 = (as_refinement env wl t2)
in (match (uu____9684) with
| (x2, phi2) -> begin
(

let base_prob = (let _0_591 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _0_590 -> FStar_TypeChecker_Common.TProb (_0_590)) _0_591))
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

let mk_imp = (fun imp phi1 phi2 -> (let _0_592 = (imp phi1 phi2)
in (FStar_All.pipe_right _0_592 (guard_on_element problem x1))))
in (

let fallback = (fun uu____9723 -> (

let impl = (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end
| uu____9725 -> begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end)
in (

let guard = (let _0_593 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _0_593 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl))))))
in (match ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) with
| true -> begin
(

let ref_prob = (let _0_597 = (let _0_596 = (let _0_595 = (FStar_Syntax_Syntax.mk_binder x1)
in (_0_595)::(p_scope orig))
in (mk_problem _0_596 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _0_594 -> FStar_TypeChecker_Common.TProb (_0_594)) _0_597))
in (

let uu____9737 = (solve env (

let uu___155_9738 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = uu___155_9738.ctr; defer_ok = false; smt_ok = uu___155_9738.smt_ok; tcenv = uu___155_9738.tcenv}))
in (match (uu____9737) with
| Failed (uu____9742) -> begin
(fallback ())
end
| Success (uu____9745) -> begin
(

let guard = (let _0_600 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _0_599 = (let _0_598 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _0_598 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _0_600 _0_599)))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (

let wl = (

let uu___156_9757 = wl
in {attempting = uu___156_9757.attempting; wl_deferred = uu___156_9757.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = uu___156_9757.defer_ok; smt_ok = uu___156_9757.smt_ok; tcenv = uu___156_9757.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end)))
end
| uu____9758 -> begin
(fallback ())
end)))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _0_602 = (destruct_flex_t t1)
in (let _0_601 = (destruct_flex_t t2)
in (flex_flex orig _0_602 _0_601)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _0_603 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig _0_603 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_arrow (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
(solve_t' env (

let uu___157_9871 = problem
in {FStar_TypeChecker_Common.pid = uu___157_9871.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___157_9871.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___157_9871.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___157_9871.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___157_9871.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___157_9871.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___157_9871.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___157_9871.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___157_9871.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| uu____9887 -> begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in (

let uu____9889 = (let _0_604 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _0_604))
in (match (uu____9889) with
| true -> begin
(let _0_607 = (FStar_All.pipe_left (fun _0_605 -> FStar_TypeChecker_Common.TProb (_0_605)) (

let uu___158_9892 = problem
in {FStar_TypeChecker_Common.pid = uu___158_9892.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___158_9892.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___158_9892.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___158_9892.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___158_9892.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___158_9892.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___158_9892.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___158_9892.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___158_9892.FStar_TypeChecker_Common.rank}))
in (let _0_606 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false _0_607 _0_606 t2 wl)))
end
| uu____9893 -> begin
(

let uu____9894 = (base_and_refinement env wl t2)
in (match (uu____9894) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _0_610 = (FStar_All.pipe_left (fun _0_608 -> FStar_TypeChecker_Common.TProb (_0_608)) (

let uu___159_9926 = problem
in {FStar_TypeChecker_Common.pid = uu___159_9926.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___159_9926.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = uu___159_9926.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___159_9926.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___159_9926.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___159_9926.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___159_9926.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___159_9926.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___159_9926.FStar_TypeChecker_Common.rank}))
in (let _0_609 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false _0_610 _0_609 t_base wl)))
end
| Some (y, phi) -> begin
(

let y' = (

let uu___160_9938 = y
in {FStar_Syntax_Syntax.ppname = uu___160_9938.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___160_9938.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element problem y' phi)
in (

let base_prob = (let _0_612 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _0_611 -> FStar_TypeChecker_Common.TProb (_0_611)) _0_612))
in (

let guard = (let _0_613 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _0_613 impl))
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
| uu____9966 -> begin
(

let uu____9967 = (base_and_refinement env wl t1)
in (match (uu____9967) with
| (t_base, uu____9978) -> begin
(solve_t env (

let uu___161_9993 = problem
in {FStar_TypeChecker_Common.pid = uu___161_9993.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = uu___161_9993.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___161_9993.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___161_9993.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___161_9993.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___161_9993.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___161_9993.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___161_9993.FStar_TypeChecker_Common.rank}) wl)
end))
end)
end
| (FStar_Syntax_Syntax.Tm_refine (uu____9996), uu____9997) -> begin
(

let t2 = (let _0_614 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _0_614))
in (solve_t env (

let uu___162_10012 = problem
in {FStar_TypeChecker_Common.pid = uu___162_10012.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___162_10012.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___162_10012.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___162_10012.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___162_10012.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___162_10012.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___162_10012.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___162_10012.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___162_10012.FStar_TypeChecker_Common.rank}) wl))
end
| (uu____10013, FStar_Syntax_Syntax.Tm_refine (uu____10014)) -> begin
(

let t1 = (let _0_615 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _0_615))
in (solve_t env (

let uu___163_10029 = problem
in {FStar_TypeChecker_Common.pid = uu___163_10029.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___163_10029.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___163_10029.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___163_10029.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___163_10029.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___163_10029.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___163_10029.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___163_10029.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___163_10029.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(

let head1 = (let _0_616 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _0_616 Prims.fst))
in (

let head2 = (let _0_617 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _0_617 Prims.fst))
in (

let uu____10098 = ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ))
in (match (uu____10098) with
| true -> begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in (

let uu____10107 = ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2))
in (match (uu____10107) with
| true -> begin
(

let guard = (

let uu____10116 = (let _0_618 = (FStar_Syntax_Util.eq_tm t1 t2)
in (_0_618 = FStar_Syntax_Util.Equal))
in (match (uu____10116) with
| true -> begin
None
end
| uu____10122 -> begin
(let _0_620 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _0_619 -> Some (_0_619)) _0_620))
end))
in (let _0_621 = (solve_prob orig guard [] wl)
in (solve env _0_621)))
end
| uu____10130 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| uu____10131 -> begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, uu____10133, uu____10134), uu____10135) -> begin
(solve_t' env (

let uu___164_10154 = problem
in {FStar_TypeChecker_Common.pid = uu___164_10154.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = uu___164_10154.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___164_10154.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___164_10154.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___164_10154.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___164_10154.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___164_10154.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___164_10154.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___164_10154.FStar_TypeChecker_Common.rank}) wl)
end
| (uu____10157, FStar_Syntax_Syntax.Tm_ascribed (t2, uu____10159, uu____10160)) -> begin
(solve_t' env (

let uu___165_10179 = problem
in {FStar_TypeChecker_Common.pid = uu___165_10179.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___165_10179.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___165_10179.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = uu___165_10179.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___165_10179.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___165_10179.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___165_10179.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___165_10179.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___165_10179.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(failwith (let _0_623 = (FStar_Syntax_Print.tag_of_term t1)
in (let _0_622 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _0_623 _0_622))))
end
| uu____10192 -> begin
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

let uu____10224 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ")))
in (match (uu____10224) with
| true -> begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end
| uu____10225 -> begin
()
end));
(

let sub_probs = (FStar_List.map2 (fun uu____10232 uu____10233 -> (match (((uu____10232), (uu____10233))) with
| ((a1, uu____10243), (a2, uu____10245)) -> begin
(let _0_625 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _0_624 -> FStar_TypeChecker_Common.TProb (_0_624)) _0_625))
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
| ((wp1, uu____10274))::[] -> begin
wp1
end
| uu____10287 -> begin
(failwith (let _0_626 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _0_626)))
end)
in (

let c1 = (let _0_628 = (let _0_627 = (FStar_Syntax_Syntax.as_arg (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp))
in (_0_627)::[])
in {FStar_Syntax_Syntax.comp_univs = c1.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _0_628; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2)))
end
| uu____10296 -> begin
(

let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___126_10299 -> (match (uu___126_10299) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| uu____10300 -> begin
false
end))))
in (

let uu____10301 = (match (((c1.FStar_Syntax_Syntax.effect_args), (c2.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, uu____10325))::uu____10326, ((wp2, uu____10328))::uu____10329) -> begin
((wp1), (wp2))
end
| uu____10370 -> begin
(failwith (let _0_630 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _0_629 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _0_630 _0_629))))
end)
in (match (uu____10301) with
| (wpc1, wpc2) -> begin
(

let uu____10399 = (FStar_Util.physical_equality wpc1 wpc2)
in (match (uu____10399) with
| true -> begin
(let _0_631 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _0_631 wl))
end
| uu____10404 -> begin
(

let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let g = (match (env.FStar_TypeChecker_Env.lax) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____10407 -> begin
(match (is_null_wp_2) with
| true -> begin
((

let uu____10409 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10409) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| uu____10410 -> begin
()
end));
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_639 = (let _0_633 = (let _0_632 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_0_632)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _0_633 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _0_638 = (let _0_637 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _0_636 = (let _0_635 = (let _0_634 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_634))
in (_0_635)::[])
in (_0_637)::_0_636))
in ((_0_639), (_0_638))))))) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r);
)
end
| uu____10420 -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_649 = (let _0_641 = (let _0_640 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_0_640)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _0_641 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (let _0_648 = (let _0_647 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _0_646 = (let _0_645 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _0_644 = (let _0_643 = (let _0_642 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_642))
in (_0_643)::[])
in (_0_645)::_0_644))
in (_0_647)::_0_646))
in ((_0_649), (_0_648))))))) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)
end)
end)
in (

let base_prob = (let _0_651 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _0_650 -> FStar_TypeChecker_Common.TProb (_0_650)) _0_651))
in (

let wl = (let _0_655 = (let _0_654 = (let _0_653 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _0_653 g))
in (FStar_All.pipe_left (fun _0_652 -> Some (_0_652)) _0_654))
in (solve_prob orig _0_655 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end))
end)))
end)))
in (

let uu____10443 = (FStar_Util.physical_equality c1 c2)
in (match (uu____10443) with
| true -> begin
(let _0_656 = (solve_prob orig None [] wl)
in (solve env _0_656))
end
| uu____10444 -> begin
((

let uu____10446 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10446) with
| true -> begin
(let _0_658 = (FStar_Syntax_Print.comp_to_string c1)
in (let _0_657 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _0_658 (rel_to_string problem.FStar_TypeChecker_Common.relation) _0_657)))
end
| uu____10447 -> begin
()
end));
(

let uu____10448 = (let _0_660 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (let _0_659 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((_0_660), (_0_659))))
in (match (uu____10448) with
| (c1, c2) -> begin
(match (((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, uu____10454), FStar_Syntax_Syntax.Total (t2, uu____10456)) when (FStar_Syntax_Util.non_informative t2) -> begin
(let _0_661 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _0_661 wl))
end
| (FStar_Syntax_Syntax.GTotal (uu____10471), FStar_Syntax_Syntax.Total (uu____10472)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.Total (t2, _))) | ((FStar_Syntax_Syntax.GTotal (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) | ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) -> begin
(let _0_662 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _0_662 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _0_665 = (

let uu___166_10527 = problem
in (let _0_664 = (let _0_663 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _0_663))
in {FStar_TypeChecker_Common.pid = uu___166_10527.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _0_664; FStar_TypeChecker_Common.relation = uu___166_10527.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = uu___166_10527.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = uu___166_10527.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___166_10527.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___166_10527.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___166_10527.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___166_10527.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___166_10527.FStar_TypeChecker_Common.rank}))
in (solve_c env _0_665 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _0_668 = (

let uu___167_10534 = problem
in (let _0_667 = (let _0_666 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c2)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _0_666))
in {FStar_TypeChecker_Common.pid = uu___167_10534.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = uu___167_10534.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = uu___167_10534.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _0_667; FStar_TypeChecker_Common.element = uu___167_10534.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = uu___167_10534.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = uu___167_10534.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = uu___167_10534.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = uu___167_10534.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = uu___167_10534.FStar_TypeChecker_Common.rank}))
in (solve_c env _0_668 wl))
end
| (FStar_Syntax_Syntax.Comp (uu____10537), FStar_Syntax_Syntax.Comp (uu____10538)) -> begin
(

let uu____10539 = (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2))))
in (match (uu____10539) with
| true -> begin
(let _0_669 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _0_669 wl))
end
| uu____10542 -> begin
(

let c1_comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c1)
in (

let c2_comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c2)
in (match (((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name))) with
| true -> begin
(solve_eq c1_comp c2_comp)
end
| uu____10545 -> begin
(

let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (

let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in ((

let uu____10549 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10549) with
| true -> begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end
| uu____10550 -> begin
()
end));
(

let uu____10551 = (FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (uu____10551) with
| None -> begin
(

let uu____10553 = (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (FStar_Syntax_Util.non_informative (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)))
in (match (uu____10553) with
| true -> begin
(

let edge = {FStar_TypeChecker_Env.msource = c1.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c2.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = (fun r t -> t)}
in (solve_sub c1 edge c2))
end
| uu____10557 -> begin
(let _0_672 = (let _0_671 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _0_670 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _0_671 _0_670)))
in (giveup env _0_672 orig))
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


let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _0_673 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun uu____10581 -> (match (uu____10581) with
| (uu____10592, uu____10593, u, uu____10595, uu____10596, uu____10597) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _0_673 (FStar_String.concat ", "))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred))) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| uu____10620 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____10625 = (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme))
in (match (uu____10625) with
| true -> begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end
| uu____10626 -> begin
"non-trivial"
end))
end)
in (

let carry = (let _0_674 = (FStar_List.map (fun uu____10631 -> (match (uu____10631) with
| (uu____10634, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _0_674 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu____10654; FStar_TypeChecker_Env.implicits = uu____10655} -> begin
true
end
| uu____10666 -> begin
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
| uu____10691 -> begin
(failwith "impossible")
end)
in Some ((

let uu___168_10692 = g
in (let _0_683 = (let _0_682 = (let _0_681 = (let _0_676 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_676)::[])
in (let _0_680 = Some ((let _0_679 = (let _0_677 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _0_677 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _0_679 (fun _0_678 -> FStar_Util.Inl (_0_678)))))
in (FStar_Syntax_Util.abs _0_681 f _0_680)))
in (FStar_All.pipe_left (fun _0_675 -> FStar_TypeChecker_Common.NonTrivial (_0_675)) _0_682))
in {FStar_TypeChecker_Env.guard_f = _0_683; FStar_TypeChecker_Env.deferred = uu___168_10692.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___168_10692.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___168_10692.FStar_TypeChecker_Env.implicits}))))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___169_10713 = g
in (let _0_688 = (let _0_687 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_686 = (let _0_685 = (FStar_Syntax_Syntax.as_arg e)
in (_0_685)::[])
in ((f), (_0_686)))))) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left (fun _0_684 -> FStar_TypeChecker_Common.NonTrivial (_0_684)) _0_687))
in {FStar_TypeChecker_Env.guard_f = _0_688; FStar_TypeChecker_Env.deferred = uu___169_10713.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___169_10713.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___169_10713.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (uu____10730) -> begin
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
| uu____10748 -> begin
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


let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _0_689 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _0_689; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu___170_10806 = g
in (let _0_692 = (let _0_691 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _0_691 (fun _0_690 -> FStar_TypeChecker_Common.NonTrivial (_0_690))))
in {FStar_TypeChecker_Env.guard_f = _0_692; FStar_TypeChecker_Env.deferred = uu___170_10806.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___170_10806.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___170_10806.FStar_TypeChecker_Env.implicits}))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = (

let uu____10844 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____10844) with
| true -> begin
(let _0_694 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _0_693 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _0_694 (rel_to_string rel) _0_693)))
end
| uu____10845 -> begin
"TOP"
end))
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (let _0_697 = (let _0_696 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _0_695 -> Some (_0_695)) _0_696))
in (FStar_Syntax_Syntax.new_bv _0_697 t1))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (let _0_701 = (let _0_699 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _0_698 -> Some (_0_698)) _0_699))
in (let _0_700 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _0_701 _0_700)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (

let probs = (

let uu____10892 = (FStar_Options.eager_inference ())
in (match (uu____10892) with
| true -> begin
(

let uu___171_10893 = probs
in {attempting = uu___171_10893.attempting; wl_deferred = uu___171_10893.wl_deferred; ctr = uu___171_10893.ctr; defer_ok = false; smt_ok = uu___171_10893.smt_ok; tcenv = uu___171_10893.tcenv})
end
| uu____10894 -> begin
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

let uu____10904 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel")))
in (match (uu____10904) with
| true -> begin
(let _0_702 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _0_702))
end
| uu____10905 -> begin
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

let uu____10914 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____10914) with
| true -> begin
(let _0_703 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _0_703))
end
| uu____10915 -> begin
()
end));
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in ((

let uu____10918 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification")))
in (match (uu____10918) with
| true -> begin
(let _0_704 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _0_704))
end
| uu____10919 -> begin
()
end));
(

let f = (

let uu____10921 = (FStar_Syntax_Util.unmeta f).FStar_Syntax_Syntax.n
in (match (uu____10921) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| uu____10923 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end))
in (

let uu___172_10924 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = uu___172_10924.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___172_10924.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___172_10924.FStar_TypeChecker_Env.implicits}));
));
)
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _0_710 = (let _0_709 = (let _0_708 = (let _0_707 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _0_707 (fun _0_706 -> FStar_TypeChecker_Common.NonTrivial (_0_706))))
in {FStar_TypeChecker_Env.guard_f = _0_708; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _0_709))
in (FStar_All.pipe_left (fun _0_705 -> Some (_0_705)) _0_710))
end))


let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> ((

let uu____10960 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10960) with
| true -> begin
(let _0_712 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_711 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _0_712 _0_711)))
end
| uu____10961 -> begin
()
end));
(

let prob = (let _0_715 = (let _0_714 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _0_714))
in (FStar_All.pipe_left (fun _0_713 -> FStar_TypeChecker_Common.TProb (_0_713)) _0_715))
in (

let g = (let _0_717 = (let _0_716 = (singleton env prob)
in (solve_and_commit env _0_716 (fun uu____10969 -> None)))
in (FStar_All.pipe_left (with_guard env prob) _0_717))
in g));
))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (

let uu____10981 = (try_teq env t1 t2)
in (match (uu____10981) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_719 = (FStar_TypeChecker_Err.basic_type_error env None t2 t1)
in (let _0_718 = (FStar_TypeChecker_Env.get_range env)
in ((_0_719), (_0_718)))))))
end
| Some (g) -> begin
((

let uu____10985 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____10985) with
| true -> begin
(let _0_722 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_721 = (FStar_Syntax_Print.term_to_string t2)
in (let _0_720 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _0_722 _0_721 _0_720))))
end
| uu____10986 -> begin
()
end));
g;
)
end)))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 smt_ok -> ((

let uu____11001 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11001) with
| true -> begin
(let _0_724 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _0_723 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _0_724 _0_723)))
end
| uu____11002 -> begin
()
end));
(

let uu____11003 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (uu____11003) with
| (prob, x) -> begin
(

let g = (let _0_726 = (let _0_725 = (singleton' env prob smt_ok)
in (solve_and_commit env _0_725 (fun uu____11013 -> None)))
in (FStar_All.pipe_left (with_guard env prob) _0_726))
in ((

let uu____11017 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))
in (match (uu____11017) with
| true -> begin
(let _0_730 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _0_729 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _0_728 = (let _0_727 = (FStar_Util.must g)
in (guard_to_string env _0_727))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _0_730 _0_729 _0_728))))
end
| uu____11018 -> begin
()
end));
(abstract_guard x g);
))
end));
))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env e t1 t2 -> (let _0_732 = (FStar_TypeChecker_Env.get_range env)
in (let _0_731 = (FStar_TypeChecker_Err.basic_type_error env (Some (e)) t2 t1)
in (FStar_Errors.report _0_732 _0_731))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> ((

let uu____11052 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11052) with
| true -> begin
(let _0_734 = (FStar_Syntax_Print.comp_to_string c1)
in (let _0_733 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _0_734 _0_733)))
end
| uu____11053 -> begin
()
end));
(

let rel = (match (env.FStar_TypeChecker_Env.use_eq) with
| true -> begin
FStar_TypeChecker_Common.EQ
end
| uu____11055 -> begin
FStar_TypeChecker_Common.SUB
end)
in (

let prob = (let _0_737 = (let _0_736 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _0_736 "sub_comp"))
in (FStar_All.pipe_left (fun _0_735 -> FStar_TypeChecker_Common.CProb (_0_735)) _0_737))
in (let _0_739 = (let _0_738 = (singleton env prob)
in (solve_and_commit env _0_738 (fun uu____11061 -> None)))
in (FStar_All.pipe_left (with_guard env prob) _0_739))));
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
in (Prims.raise (FStar_Errors.Error ((let _0_743 = (let _0_741 = (FStar_Syntax_Print.univ_to_string u1)
in (let _0_740 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _0_741 _0_740 msg)))
in (let _0_742 = (FStar_TypeChecker_Env.get_range env)
in ((_0_743), (_0_742))))))));
))
in (

let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
(((uv), ((u1)::[])))::[]
end
| (hd)::tl -> begin
(

let uu____11168 = hd
in (match (uu____11168) with
| (uv', lower_bounds) -> begin
(

let uu____11188 = (FStar_Unionfind.equivalent uv uv')
in (match (uu____11188) with
| true -> begin
(((uv'), ((u1)::lower_bounds)))::tl
end
| uu____11204 -> begin
(let _0_744 = (insert uv u1 tl)
in (hd)::_0_744)
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

let uu____11277 = (FStar_Syntax_Util.eq_univs u1 u2)
in (match (uu____11277) with
| true -> begin
(group_by out rest)
end
| uu____11285 -> begin
(let _0_745 = (insert uv u1 out)
in (group_by _0_745 rest))
end)))
end
| uu____11286 -> begin
None
end))
end))
in (

let ad_hoc_fallback = (fun uu____11296 -> (match (ineqs) with
| [] -> begin
()
end
| uu____11299 -> begin
(

let wl = (

let uu___173_11304 = (empty_worklist env)
in {attempting = uu___173_11304.attempting; wl_deferred = uu___173_11304.wl_deferred; ctr = uu___173_11304.ctr; defer_ok = true; smt_ok = uu___173_11304.smt_ok; tcenv = uu___173_11304.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun uu____11310 -> (match (uu____11310) with
| (u1, u2) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| uu____11317 -> begin
(

let uu____11318 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl u1 u2)
in (match (uu____11318) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(

let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| uu____11326 -> begin
(u1)::[]
end)
in (

let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| uu____11332 -> begin
(u2)::[]
end)
in (

let uu____11333 = (FStar_All.pipe_right us1 (FStar_Util.for_all (fun uu___127_11335 -> (match (uu___127_11335) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(

let uu____11337 = (FStar_Syntax_Util.univ_kernel u)
in (match (uu____11337) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (

let uu____11344 = (FStar_Syntax_Util.univ_kernel u')
in (match (uu____11344) with
| (k_u', n') -> begin
((FStar_Syntax_Util.eq_univs k_u k_u') && (n <= n'))
end)))))
end))
end))))
in (match (uu____11333) with
| true -> begin
()
end
| uu____11349 -> begin
(fail None u1 u2)
end))))
end
| USolved (uu____11350) -> begin
()
end))
end)))
end)))))
end))
in (

let uu____11351 = (group_by [] ineqs)
in (match (uu____11351) with
| Some (groups) -> begin
(

let wl = (

let uu___174_11378 = (empty_worklist env)
in {attempting = uu___174_11378.attempting; wl_deferred = uu___174_11378.wl_deferred; ctr = uu___174_11378.ctr; defer_ok = false; smt_ok = uu___174_11378.smt_ok; tcenv = uu___174_11378.tcenv})
in (

let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| ((u, lower_bounds))::groups -> begin
(

let uu____11423 = (solve_universe_eq (~- ((Prims.parse_int "1"))) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))
in (match (uu____11423) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| uu____11425 -> begin
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

let fail = (fun uu____11458 -> (match (uu____11458) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Errors.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in ((

let uu____11468 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11468) with
| true -> begin
(let _0_747 = (wl_to_string wl)
in (let _0_746 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _0_747 _0_746)))
end
| uu____11478 -> begin
()
end));
(

let g = (

let uu____11480 = (solve_and_commit env wl fail)
in (match (uu____11480) with
| Some ([]) -> begin
(

let uu___175_11487 = g
in {FStar_TypeChecker_Env.guard_f = uu___175_11487.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = uu___175_11487.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___175_11487.FStar_TypeChecker_Env.implicits})
end
| uu____11490 -> begin
(failwith "impossible: Unexpected deferred constraints remain")
end))
in ((solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs);
(

let uu___176_11493 = g
in {FStar_TypeChecker_Env.guard_f = uu___176_11493.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___176_11493.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = uu___176_11493.FStar_TypeChecker_Env.implicits});
));
))))


let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (

let g = (solve_deferred_constraints env g)
in ((

let uu____11512 = (not ((FStar_TypeChecker_Env.should_verify env)))
in (match (uu____11512) with
| true -> begin
()
end
| uu____11513 -> begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
((

let uu____11516 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Norm")))
in (match (uu____11516) with
| true -> begin
(let _0_750 = (FStar_TypeChecker_Env.get_range env)
in (let _0_749 = (let _0_748 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" _0_748))
in (FStar_Errors.diag _0_750 _0_749)))
end
| uu____11517 -> begin
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

let uu____11521 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel")))
in (match (uu____11521) with
| true -> begin
(let _0_753 = (FStar_TypeChecker_Env.get_range env)
in (let _0_752 = (let _0_751 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _0_751))
in (FStar_Errors.diag _0_753 _0_752)))
end
| uu____11522 -> begin
()
end));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc);
)
end));
)
end)
end));
(

let uu___177_11523 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___177_11523.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___177_11523.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___177_11523.FStar_TypeChecker_Env.implicits});
)))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (

let uu____11547 = (FStar_Unionfind.find u)
in (match (uu____11547) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| uu____11556 -> begin
false
end)))
in (

let rec until_fixpoint = (fun acc implicits -> (

let uu____11571 = acc
in (match (uu____11571) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
(match ((not (changed))) with
| true -> begin
out
end
| uu____11582 -> begin
(until_fixpoint (([]), (false)) out)
end)
end
| (hd)::tl -> begin
(

let uu____11617 = hd
in (match (uu____11617) with
| (uu____11624, env, u, tm, k, r) -> begin
(

let uu____11630 = (unresolved u)
in (match (uu____11630) with
| true -> begin
(until_fixpoint (((hd)::out), (changed)) tl)
end
| uu____11644 -> begin
(

let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in ((

let uu____11648 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____11648) with
| true -> begin
(let _0_756 = (FStar_Syntax_Print.uvar_to_string u)
in (let _0_755 = (FStar_Syntax_Print.term_to_string tm)
in (let _0_754 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _0_756 _0_755 _0_754))))
end
| uu____11652 -> begin
()
end));
(

let uu____11653 = (env.FStar_TypeChecker_Env.type_of (

let uu___178_11657 = env
in {FStar_TypeChecker_Env.solver = uu___178_11657.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___178_11657.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___178_11657.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___178_11657.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___178_11657.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___178_11657.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___178_11657.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___178_11657.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___178_11657.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___178_11657.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___178_11657.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___178_11657.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___178_11657.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___178_11657.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___178_11657.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___178_11657.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___178_11657.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___178_11657.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___178_11657.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___178_11657.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___178_11657.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___178_11657.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___178_11657.FStar_TypeChecker_Env.qname_and_index}) tm)
in (match (uu____11653) with
| (uu____11658, uu____11659, g) -> begin
(

let g = (match (env.FStar_TypeChecker_Env.is_pattern) with
| true -> begin
(

let uu___179_11662 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___179_11662.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___179_11662.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___179_11662.FStar_TypeChecker_Env.implicits})
end
| uu____11663 -> begin
g
end)
in (

let g' = (discharge_guard' (Some ((fun uu____11667 -> (FStar_Syntax_Print.term_to_string tm)))) env g)
in (until_fixpoint (((FStar_List.append g'.FStar_TypeChecker_Env.implicits out)), (true)) tl)))
end));
)))
end))
end))
end)
end)))
in (

let uu___180_11681 = g
in (let _0_757 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___180_11681.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___180_11681.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___180_11681.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _0_757})))))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g = (let _0_758 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _0_758 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _0_759 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _0_759))
end
| ((reason, uu____11709, uu____11710, e, t, r))::uu____11714 -> begin
(let _0_762 = (let _0_761 = (FStar_Syntax_Print.term_to_string t)
in (let _0_760 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" _0_761 _0_760 reason)))
in (FStar_Errors.report r _0_762))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let uu___181_11734 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___181_11734.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___181_11734.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (((u1), (u2)))::[]; FStar_TypeChecker_Env.implicits = uu___181_11734.FStar_TypeChecker_Env.implicits}))





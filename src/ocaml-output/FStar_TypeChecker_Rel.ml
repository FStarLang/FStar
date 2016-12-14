
open Prims

let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (

let uv = (FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(

let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k)))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((uv), (uv)))
end
| _56_37 -> begin
(

let args = (FStar_All.pipe_right binders (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder))
in (

let k' = (let _153_7 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _153_7))
in (

let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k')))) None r)
in (let _153_8 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((uv), (args)))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((_153_8), (uv))))))
end)))


type uvi =
| TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)


let is_TERM = (fun _discr_ -> (match (_discr_) with
| TERM (_) -> begin
true
end
| _ -> begin
false
end))


let is_UNIV = (fun _discr_ -> (match (_discr_) with
| UNIV (_) -> begin
true
end
| _ -> begin
false
end))


let ___TERM____0 = (fun projectee -> (match (projectee) with
| TERM (_56_43) -> begin
_56_43
end))


let ___UNIV____0 = (fun projectee -> (match (projectee) with
| UNIV (_56_46) -> begin
_56_46
end))


type worklist =
{attempting : FStar_TypeChecker_Common.probs; wl_deferred : (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list; ctr : Prims.int; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_TypeChecker_Env.env}


let is_Mkworklist : worklist  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkworklist"))))


type solution =
| Success of FStar_TypeChecker_Common.deferred
| Failed of (FStar_TypeChecker_Common.prob * Prims.string)


let is_Success = (fun _discr_ -> (match (_discr_) with
| Success (_) -> begin
true
end
| _ -> begin
false
end))


let is_Failed = (fun _discr_ -> (match (_discr_) with
| Failed (_) -> begin
true
end
| _ -> begin
false
end))


let ___Success____0 = (fun projectee -> (match (projectee) with
| Success (_56_56) -> begin
_56_56
end))


let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_56_59) -> begin
_56_59
end))


type variance =
| COVARIANT
| CONTRAVARIANT
| INVARIANT


let is_COVARIANT = (fun _discr_ -> (match (_discr_) with
| COVARIANT (_) -> begin
true
end
| _ -> begin
false
end))


let is_CONTRAVARIANT = (fun _discr_ -> (match (_discr_) with
| CONTRAVARIANT (_) -> begin
true
end
| _ -> begin
false
end))


let is_INVARIANT = (fun _discr_ -> (match (_discr_) with
| INVARIANT (_) -> begin
true
end
| _ -> begin
false
end))


type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem


type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem


type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun _56_1 -> (match (_56_1) with
| FStar_TypeChecker_Common.EQ -> begin
"="
end
| FStar_TypeChecker_Common.SUB -> begin
"<:"
end
| FStar_TypeChecker_Common.SUBINV -> begin
":>"
end))


let term_to_string = (fun env t -> (match ((let _153_91 = (FStar_Syntax_Subst.compress t)
in _153_91.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, t) -> begin
(let _153_93 = (FStar_Syntax_Print.uvar_to_string u)
in (let _153_92 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "(%s:%s)" _153_93 _153_92)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty); FStar_Syntax_Syntax.tk = _56_77; FStar_Syntax_Syntax.pos = _56_75; FStar_Syntax_Syntax.vars = _56_73}, args) -> begin
(let _153_96 = (FStar_Syntax_Print.uvar_to_string u)
in (let _153_95 = (FStar_Syntax_Print.term_to_string ty)
in (let _153_94 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "(%s:%s) %s" _153_96 _153_95 _153_94))))
end
| _56_87 -> begin
(FStar_Syntax_Print.term_to_string t)
end))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _56_2 -> (match (_56_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _153_115 = (let _153_114 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _153_113 = (let _153_112 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _153_111 = (let _153_110 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _153_109 = (let _153_108 = (let _153_107 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _153_106 = (let _153_105 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _153_104 = (let _153_103 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _153_102 = (let _153_101 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_153_101)::[])
in (_153_103)::_153_102))
in (_153_105)::_153_104))
in (_153_107)::_153_106))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_153_108)
in (_153_110)::_153_109))
in (_153_112)::_153_111))
in (_153_114)::_153_113))
in (FStar_Util.format "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _153_115))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _153_117 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _153_116 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _153_117 (rel_to_string p.FStar_TypeChecker_Common.relation) _153_116)))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _56_3 -> (match (_56_3) with
| UNIV (u, t) -> begin
(

let x = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _153_122 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _153_122 FStar_Util.string_of_int))
end
in (let _153_123 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _153_123)))
end
| TERM ((u, _56_103), t) -> begin
(

let x = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _153_124 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _153_124 FStar_Util.string_of_int))
end
in (let _153_125 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _153_125)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _153_130 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _153_130 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (let _153_134 = (let _153_133 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _153_133 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _153_134 (FStar_String.concat ", "))))


let args_to_string = (fun args -> (let _153_137 = (FStar_All.pipe_right args (FStar_List.map (fun _56_116 -> (match (_56_116) with
| (x, _56_115) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _153_137 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = true; smt_ok = true; tcenv = env})


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let _56_121 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _56_121.wl_deferred; ctr = _56_121.ctr; defer_ok = _56_121.defer_ok; smt_ok = smt_ok; tcenv = _56_121.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard = (fun env g -> (

let _56_127 = (empty_worklist env)
in (let _153_152 = (FStar_List.map Prims.snd g)
in {attempting = _153_152; wl_deferred = _56_127.wl_deferred; ctr = _56_127.ctr; defer_ok = false; smt_ok = _56_127.smt_ok; tcenv = _56_127.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let _56_132 = wl
in {attempting = _56_132.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = _56_132.ctr; defer_ok = _56_132.defer_ok; smt_ok = _56_132.smt_ok; tcenv = _56_132.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let _56_136 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _56_136.wl_deferred; ctr = _56_136.ctr; defer_ok = _56_136.defer_ok; smt_ok = _56_136.smt_ok; tcenv = _56_136.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (

let _56_141 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_169 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _153_169))
end else begin
()
end
in Failed (((prob), (reason)))))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun _56_4 -> (match (_56_4) with
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

let _56_148 = p
in {FStar_TypeChecker_Common.pid = _56_148.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _56_148.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_148.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_148.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_148.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_148.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_148.FStar_TypeChecker_Common.rank}))


let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _56_5 -> (match (_56_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _153_176 -> FStar_TypeChecker_Common.TProb (_153_176)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _153_177 -> FStar_TypeChecker_Common.CProb (_153_177)))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel _56_6 -> (match (_56_6) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun _56_7 -> (match (_56_7) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun _56_8 -> (match (_56_8) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun _56_9 -> (match (_56_9) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun _56_10 -> (match (_56_10) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun _56_11 -> (match (_56_11) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun _56_12 -> (match (_56_12) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _56_13 -> (match (_56_13) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _153_196 -> FStar_TypeChecker_Common.TProb (_153_196)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _153_197 -> FStar_TypeChecker_Common.CProb (_153_197)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = (Prims.parse_int "1")))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_ST.alloc (Prims.parse_int "0"))
in (fun _56_198 -> (match (()) with
| () -> begin
(

let _56_199 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))


let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _153_210 = (next_pid ())
in (let _153_209 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _153_210; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _153_209; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))


let new_problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _153_219 = (next_pid ())
in (let _153_218 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _153_219; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _153_218; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _153_226 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _153_226; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))


let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _153_238 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _153_237 = (prob_to_string env d)
in (let _153_236 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _153_238 _153_237 _153_236 s))))
end else begin
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
| _56_235 -> begin
(FStar_All.failwith "impossible")
end)
in (

let _56_243 = (match (d) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(let _153_240 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (let _153_239 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((_153_240), (_153_239))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _153_242 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (let _153_241 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((_153_242), (_153_241))))
end)
in (match (_56_243) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)


let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _56_14 -> (match (_56_14) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| _56_253 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _56_256), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _56_15 -> (match (_56_15) with
| UNIV (_56_265) -> begin
None
end
| TERM ((u, _56_269), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun _56_16 -> (match (_56_16) with
| UNIV (u', t) -> begin
if (FStar_Unionfind.equivalent u u') then begin
Some (t)
end else begin
None
end
end
| _56_282 -> begin
None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _153_261 = (let _153_260 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _153_260))
in (FStar_Syntax_Subst.compress _153_261)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _153_266 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _153_266)))


let norm_arg = (fun env t -> (let _153_269 = (sn env (Prims.fst t))
in ((_153_269), ((Prims.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _56_293 -> (match (_56_293) with
| (x, imp) -> begin
(let _153_276 = (

let _56_294 = x
in (let _153_275 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _56_294.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_294.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_275}))
in ((_153_276), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _153_283 = (aux u)
in FStar_Syntax_Syntax.U_succ (_153_283))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _153_284 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_153_284))
end
| _56_306 -> begin
u
end)))
in (let _153_285 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _153_285))))


let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement = (fun env wl t1 -> (

let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
if norm then begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end else begin
(match ((normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _56_326; FStar_Syntax_Syntax.pos = _56_324; FStar_Syntax_Syntax.vars = _56_322} -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| tt -> begin
(let _153_299 = (let _153_298 = (FStar_Syntax_Print.term_to_string tt)
in (let _153_297 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _153_298 _153_297)))
in (FStar_All.failwith _153_299))
end)
end
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
if norm then begin
((t1), (None))
end else begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (match ((let _153_300 = (FStar_Syntax_Subst.compress t1')
in _153_300.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_refine (_56_344) -> begin
(aux true t1')
end
| _56_347 -> begin
((t1), (None))
end))
end
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
((t1), (None))
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _153_303 = (let _153_302 = (FStar_Syntax_Print.term_to_string t1)
in (let _153_301 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _153_302 _153_301)))
in (FStar_All.failwith _153_303))
end))
in (let _153_304 = (whnf env t1)
in (aux false _153_304))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _153_309 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _153_309 Prims.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _153_312 = (FStar_Syntax_Syntax.null_bv t)
in ((_153_312), (FStar_Syntax_Util.t_true))))


let as_refinement = (fun env wl t -> (

let _56_393 = (base_and_refinement env wl t)
in (match (_56_393) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement = (fun _56_401 -> (match (_56_401) with
| (t_base, refopt) -> begin
(

let _56_409 = (match (refopt) with
| Some (y, phi) -> begin
((y), (phi))
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_56_409) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _56_17 -> (match (_56_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _153_325 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _153_324 = (let _153_321 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _153_321))
in (let _153_323 = (let _153_322 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _153_322))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _153_325 _153_324 (rel_to_string p.FStar_TypeChecker_Common.relation) _153_323))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _153_328 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _153_327 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _153_326 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _153_328 _153_327 (rel_to_string p.FStar_TypeChecker_Common.relation) _153_326))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _153_334 = (let _153_333 = (let _153_332 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _56_422 -> (match (_56_422) with
| (_56_418, _56_420, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _153_332))
in (FStar_List.map (wl_prob_to_string wl) _153_333))
in (FStar_All.pipe_right _153_334 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let _56_443 = (match ((let _153_341 = (FStar_Syntax_Subst.compress k)
in _153_341.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if ((FStar_List.length bs) = (FStar_List.length ys)) then begin
(let _153_342 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (_153_342)))
end else begin
(

let _56_434 = (FStar_Syntax_Util.abs_formals t)
in (match (_56_434) with
| (ys', t, _56_433) -> begin
(let _153_343 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t))), (_153_343)))
end))
end
end
| _56_436 -> begin
(let _153_345 = (let _153_344 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_153_344)))
in ((((ys), (t))), (_153_345)))
end)
in (match (_56_443) with
| ((ys, t), (xs, c)) -> begin
if ((FStar_List.length xs) <> (FStar_List.length ys)) then begin
(FStar_Syntax_Util.abs ys t (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ([]))))))
end else begin
(

let c = (let _153_346 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp _153_346 c))
in (let _153_350 = (let _153_349 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _153_347 -> FStar_Util.Inl (_153_347)))
in (FStar_All.pipe_right _153_349 (fun _153_348 -> Some (_153_348))))
in (FStar_Syntax_Util.abs ys t _153_350)))
end
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

let _56_457 = (p_guard prob)
in (match (_56_457) with
| (_56_455, uv) -> begin
(

let _56_468 = (match ((let _153_361 = (FStar_Syntax_Subst.compress uv)
in _153_361.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi = (u_abs k bs phi)
in (

let _56_464 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _153_364 = (FStar_Util.string_of_int (p_pid prob))
in (let _153_363 = (FStar_Syntax_Print.term_to_string uv)
in (let _153_362 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _153_364 _153_363 _153_362))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi))))
end
| _56_467 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (

let _56_470 = (commit uvis)
in (

let _56_472 = wl
in {attempting = _56_472.attempting; wl_deferred = _56_472.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = _56_472.defer_ok; smt_ok = _56_472.smt_ok; tcenv = _56_472.tcenv})))
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (

let _56_477 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _153_373 = (FStar_Util.string_of_int pid)
in (let _153_372 = (let _153_371 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _153_371 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _153_373 _153_372)))
end else begin
()
end
in (

let _56_479 = (commit sol)
in (

let _56_481 = wl
in {attempting = _56_481.attempting; wl_deferred = _56_481.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = _56_481.defer_ok; smt_ok = _56_481.smt_ok; tcenv = _56_481.tcenv}))))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard = (fun t g -> (match (((t), (g))) with
| (_56_491, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _153_386 = (FStar_Syntax_Util.mk_conj t f)
in Some (_153_386))
end))
in (

let _56_503 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _153_389 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _153_388 = (let _153_387 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _153_387 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _153_389 _153_388)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))


let rec occurs = (fun wl uk t -> (let _153_399 = (let _153_397 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _153_397 FStar_Util.set_elements))
in (FStar_All.pipe_right _153_399 (FStar_Util.for_some (fun _56_512 -> (match (_56_512) with
| (uv, _56_511) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (not ((occurs wl uk t)))
in (

let msg = if occurs_ok then begin
None
end else begin
(let _153_406 = (let _153_405 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _153_404 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _153_405 _153_404)))
in Some (_153_406))
end
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let _56_527 = (occurs_check env wl uk t)
in (match (_56_527) with
| (occurs_ok, msg) -> begin
(let _153_412 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (_153_412), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set v1)
in (

let _56_545 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _56_537 _56_540 -> (match (((_56_537), (_56_540))) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _153_421 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _153_421)) then begin
((isect), (isect_set))
end else begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _153_422 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (_153_422)))
end else begin
((isect), (isect_set))
end)
end
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (_56_545) with
| (isect, _56_544) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _56_551 _56_555 -> (match (((_56_551), (_56_555))) with
| ((a, _56_550), (b, _56_554)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _56_565 -> (match (_56_565) with
| (b, _56_564) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some (((a), ((Prims.snd hd))))
end
end
| _56_567 -> begin
None
end)))


let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| (hd)::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(

let _56_576 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_437 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _153_437))
end else begin
()
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))


let is_flex : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _153_440 = (FStar_Syntax_Subst.compress t)
in _153_440.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
true
end
| _56_599 -> begin
false
end))


let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _56_610; FStar_Syntax_Syntax.pos = _56_608; FStar_Syntax_Syntax.vars = _56_606}, args) -> begin
((t), (uv), (k), (args))
end
| _56_620 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let _56_627 = (destruct_flex_t t)
in (match (_56_627) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((((t), (uv), (k), (args))), (Some (vars)))
end
| _56_631 -> begin
((((t), (uv), (k), (args))), (None))
end)
end)))


type match_result =
| MisMatch of (FStar_Syntax_Syntax.delta_depth Prims.option * FStar_Syntax_Syntax.delta_depth Prims.option)
| HeadMatch
| FullMatch


let is_MisMatch = (fun _discr_ -> (match (_discr_) with
| MisMatch (_) -> begin
true
end
| _ -> begin
false
end))


let is_HeadMatch = (fun _discr_ -> (match (_discr_) with
| HeadMatch (_) -> begin
true
end
| _ -> begin
false
end))


let is_FullMatch = (fun _discr_ -> (match (_discr_) with
| FullMatch (_) -> begin
true
end
| _ -> begin
false
end))


let ___MisMatch____0 = (fun projectee -> (match (projectee) with
| MisMatch (_56_634) -> begin
_56_634
end))


let head_match : match_result  ->  match_result = (fun _56_18 -> (match (_56_18) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| _56_641 -> begin
HeadMatch
end))


let fv_delta_depth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.delta_depth = (fun env fv -> (match (fv.FStar_Syntax_Syntax.fv_delta) with
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
if (env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr) then begin
d
end else begin
FStar_Syntax_Syntax.Delta_constant
end
end
| d -> begin
d
end))


let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth Prims.option = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) -> begin
(FStar_All.failwith "Impossible")
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
if (FStar_Syntax_Syntax.bv_eq x y) then begin
FullMatch
end else begin
MisMatch (((None), (None)))
end
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
if (FStar_Syntax_Syntax.fv_eq f g) then begin
FullMatch
end else begin
MisMatch (((Some ((fv_delta_depth env f))), (Some ((fv_delta_depth env g)))))
end
end
| (FStar_Syntax_Syntax.Tm_uinst (f, _56_727), FStar_Syntax_Syntax.Tm_uinst (g, _56_732)) -> begin
(let _153_476 = (head_matches env f g)
in (FStar_All.pipe_right _153_476 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch (((None), (None)))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _56_743), FStar_Syntax_Syntax.Tm_uvar (uv', _56_748)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch (((None), (None)))
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _56_754), FStar_Syntax_Syntax.Tm_refine (y, _56_759)) -> begin
(let _153_477 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _153_477 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _56_765), _56_769) -> begin
(let _153_478 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _153_478 head_match))
end
| (_56_772, FStar_Syntax_Syntax.Tm_refine (x, _56_775)) -> begin
(let _153_479 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _153_479 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _56_795), FStar_Syntax_Syntax.Tm_app (head', _56_800)) -> begin
(let _153_480 = (head_matches env head head')
in (FStar_All.pipe_right _153_480 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head, _56_806), _56_810) -> begin
(let _153_481 = (head_matches env head t2)
in (FStar_All.pipe_right _153_481 head_match))
end
| (_56_813, FStar_Syntax_Syntax.Tm_app (head, _56_816)) -> begin
(let _153_482 = (head_matches env t1 head)
in (FStar_All.pipe_right _153_482 head_match))
end
| _56_821 -> begin
(let _153_485 = (let _153_484 = (delta_depth_of_term env t1)
in (let _153_483 = (delta_depth_of_term env t2)
in ((_153_484), (_153_483))))
in MisMatch (_153_485))
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let _56_831 = (FStar_Syntax_Util.head_and_args t)
in (match (_56_831) with
| (head, _56_830) -> begin
(match ((let _153_492 = (FStar_Syntax_Util.un_uinst head)
in _153_492.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (let _153_493 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _153_493 FStar_Option.isSome)) then begin
(let _153_495 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right _153_495 (fun _153_494 -> Some (_153_494))))
end else begin
None
end
end
| _56_835 -> begin
None
end)
end)))
in (

let success = (fun d r t1 t2 -> ((r), (if (d > (Prims.parse_int "0")) then begin
Some (((t1), (t2)))
end else begin
None
end)))
in (

let fail = (fun r -> ((r), (None)))
in (

let rec aux = (fun retry n_delta t1 t2 -> (

let r = (head_matches env t1 t2)
in (match (r) with
| (MisMatch (Some (FStar_Syntax_Syntax.Delta_equational), _)) | (MisMatch (_, Some (FStar_Syntax_Syntax.Delta_equational))) -> begin
if (not (retry)) then begin
(fail r)
end else begin
(match ((let _153_515 = (maybe_inline t1)
in (let _153_514 = (maybe_inline t2)
in ((_153_515), (_153_514))))) with
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
end)
end
end
| MisMatch (Some (d1), Some (d2)) when (d1 = d2) -> begin
(match ((FStar_TypeChecker_Common.decr_delta_depth d1)) with
| None -> begin
(fail r)
end
| Some (d) -> begin
(

let t1 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (

let t2 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (aux retry (n_delta + (Prims.parse_int "1")) t1 t2)))
end)
end
| MisMatch (Some (d1), Some (d2)) -> begin
(

let d1_greater_than_d2 = (FStar_TypeChecker_Common.delta_depth_greater_than d1 d2)
in (

let _56_899 = if d1_greater_than_d2 then begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in ((t1'), (t2)))
end else begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (let _153_516 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in ((t1), (_153_516))))
end
in (match (_56_899) with
| (t1, t2) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t1 t2)
end)))
end
| MisMatch (_56_901) -> begin
(fail r)
end
| _56_904 -> begin
(success n_delta r t1 t2)
end)))
in (aux true (Prims.parse_int "0") t1 t2))))))


type tc =
| T of (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term))
| C of FStar_Syntax_Syntax.comp


let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))


let is_C = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))


let ___T____0 = (fun projectee -> (match (projectee) with
| T (_56_907) -> begin
_56_907
end))


let ___C____0 = (fun projectee -> (match (projectee) with
| C (_56_910) -> begin
_56_910
end))


type tcs =
tc Prims.list


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let _56_916 = (FStar_Syntax_Util.type_u ())
in (match (_56_916) with
| (t, _56_915) -> begin
(let _153_587 = (new_uvar r binders t)
in (Prims.fst _153_587))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (let _153_592 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_592 Prims.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (match ((head_matches env t t')) with
| MisMatch (_56_925) -> begin
false
end
| _56_928 -> begin
true
end))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(

let rebuild = (fun args' -> (

let args = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((_56_938, imp), T (t, _56_943)) -> begin
((t), (imp))
end
| _56_948 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), (args)))) None t.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _56_953 -> (match (_56_953) with
| (t, _56_952) -> begin
((None), (INVARIANT), (T (((t), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let fail = (fun _56_960 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (

let _56_963 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_56_963) with
| (bs, c) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs tcs -> (match (((bs), (tcs))) with
| (((x, imp))::bs, (T (t, _56_978))::tcs) -> begin
(aux (((((

let _56_983 = x
in {FStar_Syntax_Syntax.ppname = _56_983.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_983.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp)))::out) bs tcs)
end
| ([], (C (c))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _56_991 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (

let rec decompose = (fun out _56_19 -> (match (_56_19) with
| [] -> begin
(FStar_List.rev ((((None), (COVARIANT), (C (c))))::out))
end
| (hd)::rest -> begin
(decompose ((((Some (hd)), (CONTRAVARIANT), (T ((((Prims.fst hd).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (let _153_654 = (decompose [] bs)
in ((rebuild), (matches), (_153_654)))))
end)))
end
| _56_1000 -> begin
(

let rebuild = (fun _56_20 -> (match (_56_20) with
| [] -> begin
t
end
| _56_1004 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t -> true)), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _56_21 -> (match (_56_21) with
| T (t, _56_1010) -> begin
t
end
| _56_1014 -> begin
(FStar_All.failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _56_22 -> (match (_56_22) with
| T (t, _56_1018) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _56_1022 -> begin
(FStar_All.failwith "Impossible")
end))


let imitation_sub_probs = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope args q -> (match (q) with
| (_56_1035, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope r)
in (

let _56_1045 = (new_uvar r scope k)
in (match (_56_1045) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| _56_1048 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) None r)
end)
in (let _153_686 = (let _153_685 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _153_684 -> FStar_TypeChecker_Common.TProb (_153_684)) _153_685))
in ((T (((gi_xs), (mk_kind)))), (_153_686))))
end)))
end
| (_56_1051, _56_1053, C (_56_1055)) -> begin
(FStar_All.failwith "impos")
end))
in (

let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs -> begin
(

let _56_1143 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.tk = _56_1073; FStar_Syntax_Syntax.pos = _56_1071; FStar_Syntax_Syntax.vars = _56_1069})) -> begin
(match ((sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))) with
| (T (gi_xs, _56_1083), prob) -> begin
(let _153_699 = (let _153_698 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _153_697 -> C (_153_697)) _153_698))
in ((_153_699), ((prob)::[])))
end
| _56_1089 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.tk = _56_1097; FStar_Syntax_Syntax.pos = _56_1095; FStar_Syntax_Syntax.vars = _56_1093})) -> begin
(match ((sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))) with
| (T (gi_xs, _56_1107), prob) -> begin
(let _153_706 = (let _153_705 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _153_704 -> C (_153_704)) _153_705))
in ((_153_706), ((prob)::[])))
end
| _56_1113 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_56_1115, _56_1117, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _56_1123; FStar_Syntax_Syntax.pos = _56_1121; FStar_Syntax_Syntax.vars = _56_1119})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((None), (INVARIANT), (T ((((Prims.fst t)), (generic_kind))))))))
in (

let components = (((None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let _56_1134 = (let _153_712 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _153_712 FStar_List.unzip))
in (match (_56_1134) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (let _153_717 = (let _153_716 = (let _153_713 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _153_713 un_T))
in (let _153_715 = (let _153_714 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _153_714 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _153_716; FStar_Syntax_Syntax.effect_args = _153_715; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _153_717))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| _56_1137 -> begin
(

let _56_1140 = (sub_prob scope args q)
in (match (_56_1140) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (_56_1143) with
| (tc, probs) -> begin
(

let _56_1156 = (match (q) with
| (Some (b), _56_1147, _56_1149) -> begin
(let _153_719 = (let _153_718 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_153_718)::args)
in ((Some (b)), ((b)::scope), (_153_719)))
end
| _56_1152 -> begin
((None), (scope), (args))
end)
in (match (_56_1156) with
| (bopt, scope, args) -> begin
(

let _56_1160 = (aux scope args qs)
in (match (_56_1160) with
| (sub_probs, tcs, f) -> begin
(

let f = (match (bopt) with
| None -> begin
(let _153_722 = (let _153_721 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_153_721)
in (FStar_Syntax_Util.mk_conj_l _153_722))
end
| Some (b) -> begin
(let _153_726 = (let _153_725 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _153_724 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_153_725)::_153_724))
in (FStar_Syntax_Util.mk_conj_l _153_726))
end)
in (((FStar_List.append probs sub_probs)), ((tc)::tcs), (f)))
end))
end))
end))
end))
in (aux scope ps qs))))))


let rec eq_tm : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (

let t1 = (FStar_Syntax_Subst.compress t1)
in (

let t2 = (FStar_Syntax_Subst.compress t2)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(FStar_Syntax_Syntax.fv_eq f g)
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(c = d)
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, _56_1188), FStar_Syntax_Syntax.Tm_uvar (u2, _56_1193)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _56_1207 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _56_1213 _56_1217 -> (match (((_56_1213), (_56_1217))) with
| ((a1, _56_1212), (a2, _56_1216)) -> begin
(eq_tm a1 a2)
end)) a1 a2)))


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

let _56_1220 = p
in (let _153_748 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _153_747 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _56_1220.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _153_748; FStar_TypeChecker_Common.relation = _56_1220.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _153_747; FStar_TypeChecker_Common.element = _56_1220.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_1220.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_1220.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_1220.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_1220.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_1220.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _153_754 = (compress_tprob wl p)
in (FStar_All.pipe_right _153_754 (fun _153_753 -> FStar_TypeChecker_Common.TProb (_153_753))))
end
| FStar_TypeChecker_Common.CProb (_56_1227) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (let _153_759 = (compress_prob wl pr)
in (FStar_All.pipe_right _153_759 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let _56_1237 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_56_1237) with
| (lh, _56_1236) -> begin
(

let _56_1241 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_56_1241) with
| (rh, _56_1240) -> begin
(

let _56_1297 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (_56_1243), FStar_Syntax_Syntax.Tm_uvar (_56_1246)) -> begin
((flex_flex), (tp))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (_56_1262), _56_1265) -> begin
(

let _56_1269 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_56_1269) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((flex_rigid), (tp))
end
| _56_1272 -> begin
(

let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _153_761 = (

let _56_1274 = tp
in (let _153_760 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = _56_1274.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_1274.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _56_1274.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _153_760; FStar_TypeChecker_Common.element = _56_1274.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_1274.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_1274.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_1274.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_1274.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_1274.FStar_TypeChecker_Common.rank}))
in ((rank), (_153_761))))
end)
end))
end
| (_56_1277, FStar_Syntax_Syntax.Tm_uvar (_56_1279)) -> begin
(

let _56_1284 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_56_1284) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((rigid_flex), (tp))
end
| _56_1287 -> begin
(let _153_763 = (

let _56_1288 = tp
in (let _153_762 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = _56_1288.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _153_762; FStar_TypeChecker_Common.relation = _56_1288.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _56_1288.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_1288.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_1288.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_1288.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_1288.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_1288.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_1288.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (_153_763)))
end)
end))
end
| (_56_1291, _56_1293) -> begin
((rigid_rigid), (tp))
end)
in (match (_56_1297) with
| (rank, tp) -> begin
(let _153_765 = (FStar_All.pipe_right (

let _56_1298 = tp
in {FStar_TypeChecker_Common.pid = _56_1298.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_1298.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _56_1298.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _56_1298.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_1298.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_1298.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_1298.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_1298.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_1298.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _153_764 -> FStar_TypeChecker_Common.TProb (_153_764)))
in ((rank), (_153_765)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _153_767 = (FStar_All.pipe_right (

let _56_1302 = cp
in {FStar_TypeChecker_Common.pid = _56_1302.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_1302.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _56_1302.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _56_1302.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_1302.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_1302.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_1302.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_1302.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_1302.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _153_766 -> FStar_TypeChecker_Common.CProb (_153_766)))
in ((rigid_rigid), (_153_767)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun _56_1309 probs -> (match (_56_1309) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
((min), (out), (min_rank))
end
| (hd)::tl -> begin
(

let _56_1317 = (rank wl hd)
in (match (_56_1317) with
| (rank, hd) -> begin
if (rank <= flex_rigid_eq) then begin
(match (min) with
| None -> begin
((Some (hd)), ((FStar_List.append out tl)), (rank))
end
| Some (m) -> begin
((Some (hd)), ((FStar_List.append out ((m)::tl))), (rank))
end)
end else begin
if (rank < min_rank) then begin
(match (min) with
| None -> begin
(aux ((rank), (Some (hd)), (out)) tl)
end
| Some (m) -> begin
(aux ((rank), (Some (hd)), ((m)::out)) tl)
end)
end else begin
(aux ((min_rank), (min), ((hd)::out)) tl)
end
end
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


let is_UDeferred = (fun _discr_ -> (match (_discr_) with
| UDeferred (_) -> begin
true
end
| _ -> begin
false
end))


let is_USolved = (fun _discr_ -> (match (_discr_) with
| USolved (_) -> begin
true
end
| _ -> begin
false
end))


let is_UFailed = (fun _discr_ -> (match (_discr_) with
| UFailed (_) -> begin
true
end
| _ -> begin
false
end))


let ___UDeferred____0 = (fun projectee -> (match (projectee) with
| UDeferred (_56_1328) -> begin
_56_1328
end))


let ___USolved____0 = (fun projectee -> (match (projectee) with
| USolved (_56_1331) -> begin
_56_1331
end))


let ___UFailed____0 = (fun projectee -> (match (projectee) with
| UFailed (_56_1334) -> begin
_56_1334
end))


let rec really_solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (

let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (

let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (

let _56_1350 = (FStar_Syntax_Util.univ_kernel u)
in (match (_56_1350) with
| (k, _56_1349) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _56_1354 -> begin
false
end)
end)))))
end
| _56_1356 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (

let try_umax_components = (fun u1 u2 msg -> (match (((u1), (u2))) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
if ((FStar_List.length us1) = (FStar_List.length us2)) then begin
(

let rec aux = (fun wl us1 us2 -> (match (((us1), (us2))) with
| ((u1)::us1, (u2)::us2) -> begin
(match ((really_solve_universe_eq orig wl u1 u2)) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed -> begin
failed
end)
end
| _56_1381 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end else begin
(let _153_847 = (let _153_846 = (FStar_Syntax_Print.univ_to_string u1)
in (let _153_845 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _153_846 _153_845)))
in UFailed (_153_847))
end
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(

let rec aux = (fun wl us -> (match (us) with
| [] -> begin
USolved (wl)
end
| (u)::us -> begin
(match ((really_solve_universe_eq orig wl u u')) with
| USolved (wl) -> begin
(aux wl us)
end
| failed -> begin
failed
end)
end))
in (aux wl us))
end
| _56_1399 -> begin
(let _153_854 = (let _153_853 = (FStar_Syntax_Print.univ_to_string u1)
in (let _153_852 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _153_853 _153_852 msg)))
in UFailed (_153_854))
end))
in (match (((u1), (u2))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(let _153_857 = (let _153_856 = (FStar_Syntax_Print.univ_to_string u1)
in (let _153_855 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" _153_856 _153_855)))
in (FStar_All.failwith _153_857))
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
if (x.FStar_Ident.idText = y.FStar_Ident.idText) then begin
USolved (wl)
end else begin
UFailed ("Incompatible universes")
end
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
USolved (wl)
end
| (FStar_Syntax_Syntax.U_succ (u1), FStar_Syntax_Syntax.U_succ (u2)) -> begin
(really_solve_universe_eq orig wl u1 u2)
end
| (FStar_Syntax_Syntax.U_unif (v1), FStar_Syntax_Syntax.U_unif (v2)) -> begin
if (FStar_Unionfind.equivalent v1 v2) then begin
USolved (wl)
end else begin
(

let wl = (extend_solution orig ((UNIV (((v1), (u2))))::[]) wl)
in USolved (wl))
end
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(

let u = (norm_univ wl u)
in if (occurs_univ v1 u) then begin
(let _153_860 = (let _153_859 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _153_858 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _153_859 _153_858)))
in (try_umax_components u1 u2 _153_860))
end else begin
(let _153_861 = (extend_solution orig ((UNIV (((v1), (u))))::[]) wl)
in USolved (_153_861))
end)
end
| ((FStar_Syntax_Syntax.U_max (_), _)) | ((_, FStar_Syntax_Syntax.U_max (_))) -> begin
if wl.defer_ok then begin
UDeferred (wl)
end else begin
(

let u1 = (norm_univ wl u1)
in (

let u2 = (norm_univ wl u2)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
USolved (wl)
end else begin
(try_umax_components u1 u2 "")
end))
end
end
| ((FStar_Syntax_Syntax.U_succ (_), FStar_Syntax_Syntax.U_zero)) | ((FStar_Syntax_Syntax.U_succ (_), FStar_Syntax_Syntax.U_name (_))) | ((FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ (_))) | ((FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name (_))) | ((FStar_Syntax_Syntax.U_name (_), FStar_Syntax_Syntax.U_succ (_))) | ((FStar_Syntax_Syntax.U_name (_), FStar_Syntax_Syntax.U_zero)) -> begin
UFailed ("Incompatible universes")
end))))))


let solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> if wl.tcenv.FStar_TypeChecker_Env.lax_universes then begin
USolved (wl)
end else begin
(really_solve_universe_eq orig wl u1 u2)
end)


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> (

let _56_1500 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _153_915 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _153_915))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(

let probs = (

let _56_1507 = probs
in {attempting = tl; wl_deferred = _56_1507.wl_deferred; ctr = _56_1507.ctr; defer_ok = _56_1507.defer_ok; smt_ok = _56_1507.smt_ok; tcenv = _56_1507.tcenv})
in (match (hd) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
if (((not (probs.defer_ok)) && (flex_refine_inner <= rank)) && (rank <= flex_rigid)) then begin
(match ((solve_flex_rigid_join env tp probs)) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end)
end else begin
if (((not (probs.defer_ok)) && (rigid_flex <= rank)) && (rank <= refine_flex)) then begin
(match ((solve_rigid_flex_meet env tp probs)) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end)
end else begin
(solve_t' env (maybe_invert tp) probs)
end
end
end))
end
| (None, _56_1522, _56_1524) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _56_1528 -> begin
(

let _56_1537 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _56_1534 -> (match (_56_1534) with
| (c, _56_1531, _56_1533) -> begin
(c < probs.ctr)
end))))
in (match (_56_1537) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _153_918 = (FStar_List.map (fun _56_1543 -> (match (_56_1543) with
| (_56_1540, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (_153_918))
end
| _56_1545 -> begin
(let _153_921 = (

let _56_1546 = probs
in (let _153_920 = (FStar_All.pipe_right attempt (FStar_List.map (fun _56_1553 -> (match (_56_1553) with
| (_56_1549, _56_1551, y) -> begin
y
end))))
in {attempting = _153_920; wl_deferred = rest; ctr = _56_1546.ctr; defer_ok = _56_1546.defer_ok; smt_ok = _56_1546.smt_ok; tcenv = _56_1546.tcenv}))
in (solve env _153_921))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _153_927 = (solve_prob orig None [] wl)
in (solve env _153_927))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (

let rec aux = (fun wl us1 us2 -> (match (((us1), (us2))) with
| ([], []) -> begin
USolved (wl)
end
| ((u1)::us1, (u2)::us2) -> begin
(match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed_or_deferred -> begin
failed_or_deferred
end)
end
| _56_1588 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t1 = (whnf env t1)
in (

let t2 = (whnf env t2)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _56_1596; FStar_Syntax_Syntax.pos = _56_1594; FStar_Syntax_Syntax.vars = _56_1592}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _56_1608; FStar_Syntax_Syntax.pos = _56_1606; FStar_Syntax_Syntax.vars = _56_1604}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (

let _56_1617 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _56_1632 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(

let _56_1637 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_943 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _153_943 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (

let _56_1642 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _153_947 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" _153_947))
end else begin
()
end
in (

let _56_1646 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_56_1646) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let _56_1652 = (head_matches_delta env () t1 t2)
in (match (_56_1652) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (_56_1654) -> begin
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

let _56_1670 = (match (ts) with
| Some (t1, t2) -> begin
(let _153_953 = (FStar_Syntax_Subst.compress t1)
in (let _153_952 = (FStar_Syntax_Subst.compress t2)
in ((_153_953), (_153_952))))
end
| None -> begin
(let _153_955 = (FStar_Syntax_Subst.compress t1)
in (let _153_954 = (FStar_Syntax_Subst.compress t2)
in ((_153_955), (_153_954))))
end)
in (match (_56_1670) with
| (t1, t2) -> begin
(

let eq_prob = (fun t1 t2 -> (let _153_961 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _153_960 -> FStar_TypeChecker_Common.TProb (_153_960)) _153_961)))
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(let _153_968 = (let _153_967 = (let _153_964 = (let _153_963 = (let _153_962 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (_153_962)))
in FStar_Syntax_Syntax.Tm_refine (_153_963))
in (FStar_Syntax_Syntax.mk _153_964 None t1.FStar_Syntax_Syntax.pos))
in (let _153_966 = (let _153_965 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (_153_965)::[])
in ((_153_967), (_153_966))))
in Some (_153_968))
end
| (_56_1684, FStar_Syntax_Syntax.Tm_refine (x, _56_1687)) -> begin
(let _153_971 = (let _153_970 = (let _153_969 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (_153_969)::[])
in ((t1), (_153_970)))
in Some (_153_971))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _56_1693), _56_1697) -> begin
(let _153_974 = (let _153_973 = (let _153_972 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (_153_972)::[])
in ((t2), (_153_973)))
in Some (_153_974))
end
| _56_1700 -> begin
(

let _56_1704 = (FStar_Syntax_Util.head_and_args t1)
in (match (_56_1704) with
| (head1, _56_1703) -> begin
(match ((let _153_975 = (FStar_Syntax_Util.un_uinst head1)
in _153_975.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _56_1710; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (i); FStar_Syntax_Syntax.fv_qual = _56_1706}) -> begin
(

let prev = if (i > (Prims.parse_int "1")) then begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i - (Prims.parse_int "1")))
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t1)
in (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t2)
in (disjoin t1 t2))))
end
| _56_1717 -> begin
None
end)
end))
end))
end))
end)
end)))
in (

let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _56_1721) -> begin
(

let _56_1746 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _56_23 -> (match (_56_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(

let _56_1732 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_56_1732) with
| (u', _56_1731) -> begin
(match ((let _153_977 = (whnf env u')
in _153_977.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _56_1735) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _56_1739 -> begin
false
end)
end))
end
| _56_1741 -> begin
false
end)
end
| _56_1743 -> begin
false
end))))
in (match (_56_1746) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun _56_1750 tps -> (match (_56_1750) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(match ((let _153_982 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound _153_982))) with
| Some (bound, sub) -> begin
(make_lower_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end)
end
| _56_1763 -> begin
None
end)
end))
in (match ((let _153_984 = (let _153_983 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((_153_983), ([])))
in (make_lower_bound _153_984 lower_bounds))) with
| None -> begin
(

let _56_1765 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No lower bounds\n")
end else begin
()
end
in None)
end
| Some (lhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in (

let _56_1775 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(

let wl' = (

let _56_1772 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _56_1772.wl_deferred; ctr = _56_1772.ctr; defer_ok = _56_1772.defer_ok; smt_ok = _56_1772.smt_ok; tcenv = _56_1772.tcenv})
in (let _153_985 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" _153_985)))
end else begin
()
end
in (match ((solve_t env eq_prob (

let _56_1777 = wl
in {attempting = sub_probs; wl_deferred = _56_1777.wl_deferred; ctr = _56_1777.ctr; defer_ok = _56_1777.defer_ok; smt_ok = _56_1777.smt_ok; tcenv = _56_1777.tcenv}))) with
| Success (_56_1780) -> begin
(

let wl = (

let _56_1782 = wl
in {attempting = rest; wl_deferred = _56_1782.wl_deferred; ctr = _56_1782.ctr; defer_ok = _56_1782.defer_ok; smt_ok = _56_1782.smt_ok; tcenv = _56_1782.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let _56_1788 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| _56_1791 -> begin
None
end)))
end))
end))
end
| _56_1793 -> begin
(FStar_All.failwith "Impossible: Not a rigid-flex")
end)))
end))))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (

let _56_1797 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _153_991 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _153_991))
end else begin
()
end
in (

let _56_1801 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_56_1801) with
| (u, args) -> begin
(

let _56_1807 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (_56_1807) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(

let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (

let base_types_match = (fun t1 t2 -> (

let _56_1816 = (FStar_Syntax_Util.head_and_args t1)
in (match (_56_1816) with
| (h1, args1) -> begin
(

let _56_1820 = (FStar_Syntax_Util.head_and_args t2)
in (match (_56_1820) with
| (h2, _56_1819) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = (Prims.parse_int "0")) then begin
Some ([])
end else begin
(let _153_1003 = (let _153_1002 = (let _153_1001 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _153_1000 -> FStar_TypeChecker_Common.TProb (_153_1000)) _153_1001))
in (_153_1002)::[])
in Some (_153_1003))
end
end else begin
None
end
end
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
if (FStar_Syntax_Syntax.bv_eq a b) then begin
if ((FStar_List.length args1) = (Prims.parse_int "0")) then begin
Some ([])
end else begin
(let _153_1007 = (let _153_1006 = (let _153_1005 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _153_1004 -> FStar_TypeChecker_Common.TProb (_153_1004)) _153_1005))
in (_153_1006)::[])
in Some (_153_1007))
end
end else begin
None
end
end
| _56_1832 -> begin
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
in (let _153_1014 = (let _153_1013 = (let _153_1012 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _153_1012))
in ((_153_1013), (m)))
in Some (_153_1014))))))
end))
end
| (_56_1854, FStar_Syntax_Syntax.Tm_refine (y, _56_1857)) -> begin
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
| (FStar_Syntax_Syntax.Tm_refine (x, _56_1867), _56_1871) -> begin
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
| _56_1878 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, _56_1886) -> begin
(

let _56_1911 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _56_24 -> (match (_56_24) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(

let _56_1897 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_56_1897) with
| (u', _56_1896) -> begin
(match ((let _153_1016 = (whnf env u')
in _153_1016.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _56_1900) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _56_1904 -> begin
false
end)
end))
end
| _56_1906 -> begin
false
end)
end
| _56_1908 -> begin
false
end))))
in (match (_56_1911) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun _56_1915 tps -> (match (_56_1915) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(match ((let _153_1021 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _153_1021))) with
| Some (bound, sub) -> begin
(make_upper_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end)
end
| _56_1928 -> begin
None
end)
end))
in (match ((let _153_1023 = (let _153_1022 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((_153_1022), ([])))
in (make_upper_bound _153_1023 upper_bounds))) with
| None -> begin
(

let _56_1930 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in (

let _56_1940 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(

let wl' = (

let _56_1937 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _56_1937.wl_deferred; ctr = _56_1937.ctr; defer_ok = _56_1937.defer_ok; smt_ok = _56_1937.smt_ok; tcenv = _56_1937.tcenv})
in (let _153_1024 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _153_1024)))
end else begin
()
end
in (match ((solve_t env eq_prob (

let _56_1942 = wl
in {attempting = sub_probs; wl_deferred = _56_1942.wl_deferred; ctr = _56_1942.ctr; defer_ok = _56_1942.defer_ok; smt_ok = _56_1942.smt_ok; tcenv = _56_1942.tcenv}))) with
| Success (_56_1945) -> begin
(

let wl = (

let _56_1947 = wl
in {attempting = rest; wl_deferred = _56_1947.wl_deferred; ctr = _56_1947.ctr; defer_ok = _56_1947.defer_ok; smt_ok = _56_1947.smt_ok; tcenv = _56_1947.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let _56_1953 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _56_1956 -> begin
None
end)))
end))
end))
end
| _56_1958 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (

let rec aux = (fun scope env subst xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
(

let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (

let _56_1975 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1052 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _153_1052))
end else begin
()
end
in (

let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl ((((rhs_prob)::[]), (formula))))))
end
| (((hd1, imp))::xs, ((hd2, imp'))::ys) when (imp = imp') -> begin
(

let hd1 = (

let _56_1989 = hd1
in (let _153_1053 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _56_1989.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1989.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_1053}))
in (

let hd2 = (

let _56_1992 = hd2
in (let _153_1054 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _56_1992.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1992.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_1054}))
in (

let prob = (let _153_1057 = (let _153_1056 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _153_1056 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _153_1055 -> FStar_TypeChecker_Common.TProb (_153_1055)) _153_1057))
in (

let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (

let subst = (let _153_1058 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd1))))::_153_1058)
in (

let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux ((((hd1), (imp)))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi = (let _153_1060 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _153_1059 = (FStar_Syntax_Util.close_forall ((((hd1), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj _153_1060 _153_1059)))
in (

let _56_2004 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1062 = (FStar_Syntax_Print.term_to_string phi)
in (let _153_1061 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _153_1062 _153_1061)))
end else begin
()
end
in FStar_Util.Inl ((((prob)::sub_probs), (phi)))))
end
| fail -> begin
fail
end)))))))
end
| _56_2008 -> begin
FStar_Util.Inr ("arity or argument-qualifier mismatch")
end))
in (

let scope = (p_scope orig)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _153_1066 = (compress_tprob wl problem)
in (solve_t' env _153_1066 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (

let _56_2036 = (head_matches_delta env wl t1 t2)
in (match (_56_2036) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (_56_2038), _56_2041) -> begin
(

let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _56_2054 -> begin
false
end))
in if (((may_relate head1) || (may_relate head2)) && wl.smt_ok) then begin
(

let guard = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end else begin
(

let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(

let x = (FStar_Syntax_Syntax.new_bv None t1)
in (let _153_1095 = (let _153_1094 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _153_1094 t2))
in (FStar_Syntax_Util.mk_forall x _153_1095)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _153_1096 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _153_1096)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_56_2064, Some (t1, t2)) -> begin
(solve_t env (

let _56_2070 = problem
in {FStar_TypeChecker_Common.pid = _56_2070.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _56_2070.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _56_2070.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2070.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2070.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2070.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2070.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2070.FStar_TypeChecker_Common.rank}) wl)
end
| (_56_2073, None) -> begin
(

let _56_2076 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1100 = (FStar_Syntax_Print.term_to_string t1)
in (let _153_1099 = (FStar_Syntax_Print.tag_of_term t1)
in (let _153_1098 = (FStar_Syntax_Print.term_to_string t2)
in (let _153_1097 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _153_1100 _153_1099 _153_1098 _153_1097)))))
end else begin
()
end
in (

let _56_2080 = (FStar_Syntax_Util.head_and_args t1)
in (match (_56_2080) with
| (head1, args1) -> begin
(

let _56_2083 = (FStar_Syntax_Util.head_and_args t2)
in (match (_56_2083) with
| (head2, args2) -> begin
(

let nargs = (FStar_List.length args1)
in if (nargs <> (FStar_List.length args2)) then begin
(let _153_1105 = (let _153_1104 = (FStar_Syntax_Print.term_to_string head1)
in (let _153_1103 = (args_to_string args1)
in (let _153_1102 = (FStar_Syntax_Print.term_to_string head2)
in (let _153_1101 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _153_1104 _153_1103 _153_1102 _153_1101)))))
in (giveup env _153_1105 orig))
end else begin
if ((nargs = (Prims.parse_int "0")) || (eq_args args1 args2)) then begin
(match ((solve_maybe_uinsts env orig head1 head2 wl)) with
| USolved (wl) -> begin
(let _153_1106 = (solve_prob orig None [] wl)
in (solve env _153_1106))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(

let _56_2093 = (base_and_refinement env wl t1)
in (match (_56_2093) with
| (base1, refinement1) -> begin
(

let _56_2096 = (base_and_refinement env wl t2)
in (match (_56_2096) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (None, None) -> begin
(match ((solve_maybe_uinsts env orig head1 head2 wl)) with
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end
| USolved (wl) -> begin
(

let subprobs = (FStar_List.map2 (fun _56_2109 _56_2113 -> (match (((_56_2109), (_56_2113))) with
| ((a, _56_2108), (a', _56_2112)) -> begin
(let _153_1110 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _153_1109 -> FStar_TypeChecker_Common.TProb (_153_1109)) _153_1110))
end)) args1 args2)
in (

let formula = (let _153_1112 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _153_1112))
in (

let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _56_2119 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env (

let _56_2122 = problem
in {FStar_TypeChecker_Common.pid = _56_2122.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _56_2122.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _56_2122.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2122.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2122.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2122.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2122.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2122.FStar_TypeChecker_Common.rank}) wl)))
end)
end))
end))
end
end)
end))
end)))
end)
end)))
in (

let imitate = (fun orig env wl p -> (

let _56_2141 = p
in (match (_56_2141) with
| (((u, k), xs, c), ps, (h, _56_2138, qs)) -> begin
(

let xs = (sn_binders env xs)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _56_2147 = (imitation_sub_probs orig env xs ps qs)
in (match (_56_2147) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (let _153_1127 = (h gs_xs)
in (let _153_1126 = (let _153_1125 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _153_1123 -> FStar_Util.Inl (_153_1123)))
in (FStar_All.pipe_right _153_1125 (fun _153_1124 -> Some (_153_1124))))
in (FStar_Syntax_Util.abs xs _153_1127 _153_1126)))
in (

let _56_2149 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1134 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _153_1133 = (FStar_Syntax_Print.comp_to_string c)
in (let _153_1132 = (FStar_Syntax_Print.term_to_string im)
in (let _153_1131 = (FStar_Syntax_Print.tag_of_term im)
in (let _153_1130 = (let _153_1128 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _153_1128 (FStar_String.concat ", ")))
in (let _153_1129 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" _153_1134 _153_1133 _153_1132 _153_1131 _153_1130 _153_1129)))))))
end else begin
()
end
in (

let wl = (solve_prob orig (Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (

let imitate' = (fun orig env wl _56_25 -> (match (_56_25) with
| None -> begin
(giveup env "unable to compute subterms" orig)
end
| Some (p) -> begin
(imitate orig env wl p)
end))
in (

let project = (fun orig env wl i p -> (

let _56_2175 = p
in (match (_56_2175) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _56_2180 = (FStar_List.nth ps i)
in (match (_56_2180) with
| (pi, _56_2179) -> begin
(

let _56_2184 = (FStar_List.nth xs i)
in (match (_56_2184) with
| (xi, _56_2183) -> begin
(

let rec gs = (fun k -> (

let _56_2189 = (FStar_Syntax_Util.arrow_formals k)
in (match (_56_2189) with
| (bs, k) -> begin
(

let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
(([]), ([]))
end
| ((a, _56_2197))::tl -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (

let _56_2203 = (new_uvar r xs k_a)
in (match (_56_2203) with
| (gi_xs, gi) -> begin
(

let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (

let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst = (FStar_Syntax_Syntax.NT (((a), (gi_xs))))::subst
in (

let _56_2209 = (aux subst tl)
in (match (_56_2209) with
| (gi_xs', gi_ps') -> begin
(let _153_1164 = (let _153_1161 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_153_1161)::gi_xs')
in (let _153_1163 = (let _153_1162 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_153_1162)::gi_ps')
in ((_153_1164), (_153_1163))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _153_1165 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _153_1165)) then begin
None
end else begin
(

let _56_2213 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_56_2213) with
| (g_xs, _56_2212) -> begin
(

let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (let _153_1170 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (let _153_1169 = (let _153_1168 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _153_1166 -> FStar_Util.Inl (_153_1166)))
in (FStar_All.pipe_right _153_1168 (fun _153_1167 -> Some (_153_1167))))
in (FStar_Syntax_Util.abs xs _153_1170 _153_1169)))
in (

let sub = (let _153_1176 = (let _153_1175 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _153_1174 = (let _153_1173 = (FStar_List.map (fun _56_2221 -> (match (_56_2221) with
| (_56_2217, _56_2219, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _153_1173))
in (mk_problem (p_scope orig) orig _153_1175 (p_rel orig) _153_1174 None "projection")))
in (FStar_All.pipe_left (fun _153_1171 -> FStar_TypeChecker_Common.TProb (_153_1171)) _153_1176))
in (

let _56_2223 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1178 = (FStar_Syntax_Print.term_to_string proj)
in (let _153_1177 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _153_1178 _153_1177)))
end else begin
()
end
in (

let wl = (let _153_1180 = (let _153_1179 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_153_1179))
in (solve_prob orig _153_1180 ((TERM (((u), (proj))))::[]) wl))
in (let _153_1182 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _153_1181 -> Some (_153_1181)) _153_1182)))))))
end))
end)
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl -> (

let _56_2238 = lhs
in (match (_56_2238) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let _56_2243 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (_56_2243) with
| (xs, c) -> begin
if ((FStar_List.length xs) = (FStar_List.length ps)) then begin
(let _153_1206 = (let _153_1205 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (_153_1205)))
in Some (_153_1206))
end else begin
(

let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (match ((let _153_1212 = (let _153_1211 = (FStar_Syntax_Subst.compress k)
in _153_1211.FStar_Syntax_Syntax.n)
in ((_153_1212), (args)))) with
| (_56_2249, []) -> begin
(let _153_1214 = (let _153_1213 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_153_1213)))
in Some (_153_1214))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(

let _56_2266 = (FStar_Syntax_Util.head_and_args k)
in (match (_56_2266) with
| (uv, uv_args) -> begin
(match ((let _153_1215 = (FStar_Syntax_Subst.compress uv)
in _153_1215.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, _56_2269) -> begin
(match ((pat_vars env [] uv_args)) with
| None -> begin
None
end
| Some (scope) -> begin
(

let xs = (FStar_All.pipe_right args (FStar_List.map (fun _56_2275 -> (let _153_1221 = (let _153_1220 = (let _153_1219 = (let _153_1218 = (let _153_1217 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_1217 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _153_1218))
in (Prims.fst _153_1219))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) _153_1220))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _153_1221)))))
in (

let c = (let _153_1225 = (let _153_1224 = (let _153_1223 = (let _153_1222 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_1222 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _153_1223))
in (Prims.fst _153_1224))
in (FStar_Syntax_Syntax.mk_Total _153_1225))
in (

let k' = (FStar_Syntax_Util.arrow xs c)
in (

let uv_sol = (let _153_1231 = (let _153_1230 = (let _153_1229 = (let _153_1228 = (let _153_1227 = (let _153_1226 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_1226 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total _153_1227))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_1228))
in FStar_Util.Inl (_153_1229))
in Some (_153_1230))
in (FStar_Syntax_Util.abs scope k' _153_1231))
in (

let _56_2281 = (FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)))
in Some (((xs), (c))))))))
end)
end
| _56_2284 -> begin
None
end)
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), _56_2290) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs)
in if (n_xs = n_args) then begin
(let _153_1233 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right _153_1233 (fun _153_1232 -> Some (_153_1232))))
end else begin
if (n_xs < n_args) then begin
(

let _56_2296 = (FStar_Util.first_N n_xs args)
in (match (_56_2296) with
| (args, rest) -> begin
(

let _56_2299 = (FStar_Syntax_Subst.open_comp xs c)
in (match (_56_2299) with
| (xs, c) -> begin
(let _153_1235 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt _153_1235 (fun _56_2302 -> (match (_56_2302) with
| (xs', c) -> begin
Some ((((FStar_List.append xs xs')), (c)))
end))))
end))
end))
end else begin
(

let _56_2305 = (FStar_Util.first_N n_args xs)
in (match (_56_2305) with
| (xs, rest) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) None k.FStar_Syntax_Syntax.pos)
in (let _153_1238 = (let _153_1236 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs _153_1236))
in (FStar_All.pipe_right _153_1238 (fun _153_1237 -> Some (_153_1237)))))
end))
end
end))
end
| _56_2308 -> begin
(let _153_1242 = (let _153_1241 = (FStar_Syntax_Print.uvar_to_string uv)
in (let _153_1240 = (FStar_Syntax_Print.term_to_string k)
in (let _153_1239 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" _153_1241 _153_1240 _153_1239))))
in (FStar_All.failwith _153_1242))
end))
in (let _153_1280 = (elim k_uv ps)
in (FStar_Util.bind_opt _153_1280 (fun _56_2311 -> (match (_56_2311) with
| (xs, c) -> begin
(let _153_1279 = (let _153_1278 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (_153_1278)))
in Some (_153_1279))
end))))))
end
end)))
in (

let rec imitate_or_project = (fun n stopt i -> if ((i >= n) || (FStar_Option.isNone stopt)) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
(

let st = (FStar_Option.get stopt)
in (

let tx = (FStar_Unionfind.new_transaction ())
in if (i = (~- ((Prims.parse_int "1")))) then begin
(match ((imitate orig env wl st)) with
| Failed (_56_2319) -> begin
(

let _56_2321 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + (Prims.parse_int "1"))))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(

let _56_2329 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + (Prims.parse_int "1"))))
end
| Some (sol) -> begin
sol
end)
end))
end)
in (

let check_head = (fun fvs1 t2 -> (

let _56_2339 = (FStar_Syntax_Util.head_and_args t2)
in (match (_56_2339) with
| (hd, _56_2338) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _56_2350 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(

let _56_2352 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1291 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _153_1291))
end else begin
()
end
in false)
end)
end)
end)))
in (

let imitate_ok = (fun t2 -> (

let fvs_hd = (let _153_1295 = (let _153_1294 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _153_1294 Prims.fst))
in (FStar_All.pipe_right _153_1295 FStar_Syntax_Free.names))
in if (FStar_Util.set_is_empty fvs_hd) then begin
(~- ((Prims.parse_int "1")))
end else begin
(Prims.parse_int "0")
end))
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

let _56_2365 = (occurs_check env wl ((uv), (k_uv)) t2)
in (match (_56_2365) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _153_1297 = (let _153_1296 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _153_1296))
in (giveup_or_defer orig _153_1297))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t2)) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _153_1298 = (subterms args_lhs)
in (imitate' orig env wl _153_1298))
end else begin
(

let _56_2366 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1301 = (FStar_Syntax_Print.term_to_string t1)
in (let _153_1300 = (names_to_string fvs1)
in (let _153_1299 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _153_1301 _153_1300 _153_1299))))
end else begin
()
end
in (

let sol = (match (vars) with
| [] -> begin
t2
end
| _56_2370 -> begin
(let _153_1302 = (sn_binders env vars)
in (u_abs k_uv _153_1302 t2))
end)
in (

let wl = (solve_prob orig None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl)
in (solve env wl))))
end
end else begin
if (((not (patterns_only)) && wl.defer_ok) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if ((not (patterns_only)) && (check_head fvs1 t2)) then begin
(

let _56_2373 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1305 = (FStar_Syntax_Print.term_to_string t1)
in (let _153_1304 = (names_to_string fvs1)
in (let _153_1303 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _153_1305 _153_1304 _153_1303))))
end else begin
()
end
in (let _153_1306 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _153_1306 (~- ((Prims.parse_int "1"))))))
end else begin
(giveup env "free-variable check failed on a non-redex" orig)
end
end
end
end
end))))))
end
| None when patterns_only -> begin
(giveup env "not a pattern" orig)
end
| None -> begin
if wl.defer_ok then begin
(solve env (defer "not a pattern" orig wl))
end else begin
if (let _153_1307 = (FStar_Syntax_Free.names t1)
in (check_head _153_1307 t2)) then begin
(

let im_ok = (imitate_ok t2)
in (

let _56_2378 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1308 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _153_1308 (if (im_ok < (Prims.parse_int "0")) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _153_1309 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _153_1309 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (

let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(

let force_quasi_pattern = (fun xs_opt _56_2390 -> (match (_56_2390) with
| (t, u, k, args) -> begin
(

let _56_2394 = (FStar_Syntax_Util.arrow_formals k)
in (match (_56_2394) with
| (all_formals, _56_2393) -> begin
(

let _56_2395 = ()
in (

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match (((formals), (args))) with
| ([], []) -> begin
(

let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _56_2408 -> (match (_56_2408) with
| (x, imp) -> begin
(let _153_1331 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_153_1331), (imp)))
end))))
in (

let pattern_vars = (FStar_List.rev pattern_vars)
in (

let kk = (

let _56_2414 = (FStar_Syntax_Util.type_u ())
in (match (_56_2414) with
| (t, _56_2413) -> begin
(let _153_1332 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _153_1332))
end))
in (

let _56_2418 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_56_2418) with
| (t', tm_u1) -> begin
(

let _56_2425 = (destruct_flex_t t')
in (match (_56_2425) with
| (_56_2420, u1, k1, _56_2424) -> begin
(

let sol = (let _153_1334 = (let _153_1333 = (u_abs k all_formals t')
in ((((u), (k))), (_153_1333)))
in TERM (_153_1334))
in (

let t_app = (FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args None t.FStar_Syntax_Syntax.pos)
in ((sol), (((t_app), (u1), (k1), (pat_args))))))
end))
end)))))
end
| ((formal)::formals, (hd)::tl) -> begin
(match ((pat_var_opt env pat_args hd)) with
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _56_2444 -> (match (_56_2444) with
| (x, _56_2443) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in if (not (maybe_pat)) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(

let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in if (not ((FStar_Util.set_is_subset_of fvs pattern_var_set))) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let _153_1336 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _153_1336 formals tl))
end)
end)
end)
end
| _56_2448 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _153_1337 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _153_1337 all_formals args))))
end))
end))
in (

let solve_both_pats = (fun wl _56_2455 _56_2460 r -> (match (((_56_2455), (_56_2460))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _153_1346 = (solve_prob orig None [] wl)
in (solve env _153_1346))
end else begin
(

let xs = (sn_binders env xs)
in (

let ys = (sn_binders env ys)
in (

let zs = (intersect_vars xs ys)
in (

let _56_2465 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1351 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _153_1350 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _153_1349 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (let _153_1348 = (FStar_Syntax_Print.term_to_string k1)
in (let _153_1347 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" _153_1351 _153_1350 _153_1349 _153_1348 _153_1347))))))
end else begin
()
end
in (

let subst_of_list = (fun k xs args -> (

let xs_len = (FStar_List.length xs)
in (

let args_len = (FStar_List.length args)
in if (xs_len = args_len) then begin
(FStar_Syntax_Util.subst_of_list xs args)
end else begin
(let _153_1361 = (let _153_1360 = (FStar_Syntax_Print.term_to_string k)
in (let _153_1359 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _153_1358 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" _153_1360 _153_1359 _153_1358))))
in (FStar_All.failwith _153_1361))
end)))
in (

let _56_2507 = (

let _56_2475 = (let _153_1362 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals _153_1362))
in (match (_56_2475) with
| (bs, k1') -> begin
(

let _56_2478 = (let _153_1363 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals _153_1363))
in (match (_56_2478) with
| (cs, k2') -> begin
(

let k1'_xs = (let _153_1364 = (subst_of_list k1 bs args1)
in (FStar_Syntax_Subst.subst _153_1364 k1'))
in (

let k2'_ys = (let _153_1365 = (subst_of_list k2 cs args2)
in (FStar_Syntax_Subst.subst _153_1365 k2'))
in (

let sub_prob = (let _153_1367 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys None "flex-flex kinding")
in (FStar_All.pipe_left (fun _153_1366 -> FStar_TypeChecker_Common.TProb (_153_1366)) _153_1367))
in (match ((let _153_1371 = (let _153_1368 = (FStar_Syntax_Subst.compress k1')
in _153_1368.FStar_Syntax_Syntax.n)
in (let _153_1370 = (let _153_1369 = (FStar_Syntax_Subst.compress k2')
in _153_1369.FStar_Syntax_Syntax.n)
in ((_153_1371), (_153_1370))))) with
| (FStar_Syntax_Syntax.Tm_type (_56_2483), _56_2486) -> begin
((k1'), ((sub_prob)::[]))
end
| (_56_2489, FStar_Syntax_Syntax.Tm_type (_56_2491)) -> begin
((k2'), ((sub_prob)::[]))
end
| _56_2495 -> begin
(

let _56_2499 = (FStar_Syntax_Util.type_u ())
in (match (_56_2499) with
| (t, _56_2498) -> begin
(

let _56_2503 = (new_uvar r zs t)
in (match (_56_2503) with
| (k_zs, _56_2502) -> begin
(

let kprob = (let _153_1373 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k_zs None "flex-flex kinding")
in (FStar_All.pipe_left (fun _153_1372 -> FStar_TypeChecker_Common.TProb (_153_1372)) _153_1373))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end))))
end))
end))
in (match (_56_2507) with
| (k_u', sub_probs) -> begin
(

let _56_2511 = (let _153_1379 = (let _153_1374 = (new_uvar r zs k_u')
in (FStar_All.pipe_left Prims.fst _153_1374))
in (let _153_1378 = (let _153_1375 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs _153_1375))
in (let _153_1377 = (let _153_1376 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys _153_1376))
in ((_153_1379), (_153_1378), (_153_1377)))))
in (match (_56_2511) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs u_zs)
in (

let _56_2515 = (occurs_check env wl ((u1), (k1)) sub1)
in (match (_56_2515) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(

let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(

let sub2 = (u_abs knew2 ys u_zs)
in (

let _56_2521 = (occurs_check env wl ((u2), (k2)) sub2)
in (match (_56_2521) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(

let sol2 = TERM (((((u2), (k2))), (sub2)))
in (

let wl = (solve_prob orig None ((sol1)::(sol2)::[]) wl)
in (solve env (attempt sub_probs wl))))
end
end)))
end)
end
end)))
end))
end)))))))
end
end))
in (

let solve_one_pat = (fun _56_2529 _56_2534 -> (match (((_56_2529), (_56_2534))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(

let _56_2535 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1385 = (FStar_Syntax_Print.term_to_string t1)
in (let _153_1384 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _153_1385 _153_1384)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(

let sub_probs = (FStar_List.map2 (fun _56_2540 _56_2544 -> (match (((_56_2540), (_56_2544))) with
| ((a, _56_2539), (t2, _56_2543)) -> begin
(let _153_1390 = (let _153_1388 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _153_1388 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _153_1390 (fun _153_1389 -> FStar_TypeChecker_Common.TProb (_153_1389))))
end)) xs args2)
in (

let guard = (let _153_1392 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _153_1392))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(

let t2 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t2)
in (

let _56_2554 = (occurs_check env wl ((u1), (k1)) t2)
in (match (_56_2554) with
| (occurs_ok, _56_2553) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(

let sol = (let _153_1394 = (let _153_1393 = (u_abs k1 xs t2)
in ((((u1), (k1))), (_153_1393)))
in TERM (_153_1394))
in (

let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(

let _56_2565 = (force_quasi_pattern (Some (xs)) ((t2), (u2), (k2), (args2)))
in (match (_56_2565) with
| (sol, (_56_2560, u2, k2, ys)) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (

let _56_2567 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _153_1395 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _153_1395))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _56_2572 -> begin
(giveup env "impossible" orig)
end)))
end))
end else begin
(giveup_or_defer orig "flex-flex constraint")
end
end)
end))))
end)
end))
in (

let _56_2577 = lhs
in (match (_56_2577) with
| (t1, u1, k1, args1) -> begin
(

let _56_2582 = rhs
in (match (_56_2582) with
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
| _56_2600 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(

let _56_2604 = (force_quasi_pattern None ((t1), (u1), (k1), (args1)))
in (match (_56_2604) with
| (sol, _56_2603) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (

let _56_2606 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _153_1396 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _153_1396))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _56_2611 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (

let orig = FStar_TypeChecker_Common.TProb (problem)
in if (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs) then begin
(let _153_1397 = (solve_prob orig None [] wl)
in (solve env _153_1397))
end else begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _153_1398 = (solve_prob orig None [] wl)
in (solve env _153_1398))
end else begin
(

let _56_2615 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _153_1399 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _153_1399))
end else begin
()
end
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let match_num_binders = (fun _56_2620 _56_2623 -> (match (((_56_2620), (_56_2623))) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(

let curry = (fun n bs mk_cod -> (

let _56_2630 = (FStar_Util.first_N n bs)
in (match (_56_2630) with
| (bs, rest) -> begin
(let _153_1429 = (mk_cod rest)
in ((bs), (_153_1429)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _153_1433 = (let _153_1430 = (mk_cod1 [])
in ((bs1), (_153_1430)))
in (let _153_1432 = (let _153_1431 = (mk_cod2 [])
in ((bs2), (_153_1431)))
in ((_153_1433), (_153_1432))))
end else begin
if (l1 > l2) then begin
(let _153_1436 = (curry l2 bs1 mk_cod1)
in (let _153_1435 = (let _153_1434 = (mk_cod2 [])
in ((bs2), (_153_1434)))
in ((_153_1436), (_153_1435))))
end else begin
(let _153_1439 = (let _153_1437 = (mk_cod1 [])
in ((bs1), (_153_1437)))
in (let _153_1438 = (curry l1 bs2 mk_cod2)
in ((_153_1439), (_153_1438))))
end
end)))
end))
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| ((FStar_Syntax_Syntax.Tm_bvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_bvar (_))) -> begin
(FStar_All.failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (FStar_Syntax_Syntax.Tm_type (u1), FStar_Syntax_Syntax.Tm_type (u2)) -> begin
(solve_one_universe_eq env orig u1 u2 wl)
end
| (FStar_Syntax_Syntax.Tm_arrow (bs1, c1), FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) -> begin
(

let mk_c = (fun c _56_26 -> (match (_56_26) with
| [] -> begin
c
end
| bs -> begin
(let _153_1444 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _153_1444))
end))
in (

let _56_2673 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (_56_2673) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (

let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (

let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (

let rel = if (FStar_Options.use_eq_at_higher_order ()) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in (let _153_1451 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _153_1450 -> FStar_TypeChecker_Common.CProb (_153_1450)) _153_1451)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l _56_27 -> (match (_56_27) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l)))) None t.FStar_Syntax_Syntax.pos)
end))
in (

let _56_2703 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (_56_2703) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _153_1466 = (let _153_1465 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _153_1464 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _153_1465 problem.FStar_TypeChecker_Common.relation _153_1464 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _153_1463 -> FStar_TypeChecker_Common.TProb (_153_1463)) _153_1466))))
end)))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_56_2722) -> begin
true
end
| _56_2725 -> begin
false
end))
in (

let maybe_eta = (fun t -> if (is_abs t) then begin
FStar_Util.Inl (t)
end else begin
(

let t = (FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
in if (is_abs t) then begin
FStar_Util.Inl (t)
end else begin
FStar_Util.Inr (t)
end)
end)
in (match ((let _153_1472 = (maybe_eta t1)
in (let _153_1471 = (maybe_eta t2)
in ((_153_1472), (_153_1471))))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(solve_t env (

let _56_2734 = problem
in {FStar_TypeChecker_Common.pid = _56_2734.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _56_2734.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _56_2734.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2734.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2734.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2734.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2734.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2734.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs))) | ((FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs))) -> begin
if ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ)) then begin
(let _153_1473 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig _153_1473 t_abs wl))
end else begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end
end
| _56_2745 -> begin
(FStar_All.failwith "Impossible: at least one side is an abstraction")
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_56_2747), FStar_Syntax_Syntax.Tm_refine (_56_2750)) -> begin
(

let _56_2755 = (as_refinement env wl t1)
in (match (_56_2755) with
| (x1, phi1) -> begin
(

let _56_2758 = (as_refinement env wl t2)
in (match (_56_2758) with
| (x2, phi2) -> begin
(

let base_prob = (let _153_1475 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _153_1474 -> FStar_TypeChecker_Common.TProb (_153_1474)) _153_1475))
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

let mk_imp = (fun imp phi1 phi2 -> (let _153_1492 = (imp phi1 phi2)
in (FStar_All.pipe_right _153_1492 (guard_on_element problem x1))))
in (

let fallback = (fun _56_2770 -> (match (()) with
| () -> begin
(

let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (

let guard = (let _153_1495 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _153_1495 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(

let ref_prob = (let _153_1499 = (let _153_1498 = (let _153_1497 = (FStar_Syntax_Syntax.mk_binder x1)
in (_153_1497)::(p_scope orig))
in (mk_problem _153_1498 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _153_1496 -> FStar_TypeChecker_Common.TProb (_153_1496)) _153_1499))
in (match ((solve env (

let _56_2775 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _56_2775.ctr; defer_ok = false; smt_ok = _56_2775.smt_ok; tcenv = _56_2775.tcenv}))) with
| Failed (_56_2778) -> begin
(fallback ())
end
| Success (_56_2781) -> begin
(

let guard = (let _153_1502 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _153_1501 = (let _153_1500 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _153_1500 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _153_1502 _153_1501)))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (

let wl = (

let _56_2785 = wl
in {attempting = _56_2785.attempting; wl_deferred = _56_2785.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = _56_2785.defer_ok; smt_ok = _56_2785.smt_ok; tcenv = _56_2785.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _153_1504 = (destruct_flex_t t1)
in (let _153_1503 = (destruct_flex_t t2)
in (flex_flex orig _153_1504 _153_1503)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _153_1505 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig _153_1505 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_arrow (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
(solve_t' env (

let _56_2956 = problem
in {FStar_TypeChecker_Common.pid = _56_2956.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_2956.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _56_2956.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_2956.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2956.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2956.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2956.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2956.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2956.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in if (let _153_1506 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _153_1506)) then begin
(let _153_1509 = (FStar_All.pipe_left (fun _153_1507 -> FStar_TypeChecker_Common.TProb (_153_1507)) (

let _56_2982 = problem
in {FStar_TypeChecker_Common.pid = _56_2982.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_2982.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _56_2982.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_2982.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2982.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2982.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2982.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2982.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2982.FStar_TypeChecker_Common.rank}))
in (let _153_1508 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false _153_1509 _153_1508 t2 wl)))
end else begin
(

let _56_2986 = (base_and_refinement env wl t2)
in (match (_56_2986) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _153_1512 = (FStar_All.pipe_left (fun _153_1510 -> FStar_TypeChecker_Common.TProb (_153_1510)) (

let _56_2988 = problem
in {FStar_TypeChecker_Common.pid = _56_2988.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_2988.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _56_2988.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_2988.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2988.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2988.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2988.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2988.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2988.FStar_TypeChecker_Common.rank}))
in (let _153_1511 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false _153_1512 _153_1511 t_base wl)))
end
| Some (y, phi) -> begin
(

let y' = (

let _56_2994 = y
in {FStar_Syntax_Syntax.ppname = _56_2994.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_2994.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element problem y' phi)
in (

let base_prob = (let _153_1514 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _153_1513 -> FStar_TypeChecker_Common.TProb (_153_1513)) _153_1514))
in (

let guard = (let _153_1515 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _153_1515 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))))
end)
end))
end)
end
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
if wl.defer_ok then begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end else begin
(

let _56_3027 = (base_and_refinement env wl t1)
in (match (_56_3027) with
| (t_base, _56_3026) -> begin
(solve_t env (

let _56_3028 = problem
in {FStar_TypeChecker_Common.pid = _56_3028.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _56_3028.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_3028.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_3028.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_3028.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_3028.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_3028.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_3028.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_56_3031), _56_3034) -> begin
(

let t2 = (let _153_1516 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _153_1516))
in (solve_t env (

let _56_3037 = problem
in {FStar_TypeChecker_Common.pid = _56_3037.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_3037.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _56_3037.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _56_3037.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_3037.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_3037.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_3037.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_3037.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_3037.FStar_TypeChecker_Common.rank}) wl))
end
| (_56_3040, FStar_Syntax_Syntax.Tm_refine (_56_3042)) -> begin
(

let t1 = (let _153_1517 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _153_1517))
in (solve_t env (

let _56_3046 = problem
in {FStar_TypeChecker_Common.pid = _56_3046.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _56_3046.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _56_3046.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_3046.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_3046.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_3046.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_3046.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_3046.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_3046.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(

let head1 = (let _153_1518 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _153_1518 Prims.fst))
in (

let head2 = (let _153_1519 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _153_1519 Prims.fst))
in if ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) then begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in if ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2)) then begin
(

let guard = if (eq_tm t1 t2) then begin
None
end else begin
(let _153_1521 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _153_1520 -> Some (_153_1520)) _153_1521))
end
in (let _153_1522 = (solve_prob orig guard [] wl)
in (solve env _153_1522)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _56_3127, _56_3129), _56_3133) -> begin
(solve_t' env (

let _56_3135 = problem
in {FStar_TypeChecker_Common.pid = _56_3135.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _56_3135.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _56_3135.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_3135.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_3135.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_3135.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_3135.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_3135.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_3135.FStar_TypeChecker_Common.rank}) wl)
end
| (_56_3138, FStar_Syntax_Syntax.Tm_ascribed (t2, _56_3141, _56_3143)) -> begin
(solve_t' env (

let _56_3147 = problem
in {FStar_TypeChecker_Common.pid = _56_3147.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_3147.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _56_3147.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _56_3147.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_3147.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_3147.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_3147.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_3147.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_3147.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _153_1525 = (let _153_1524 = (FStar_Syntax_Print.tag_of_term t1)
in (let _153_1523 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _153_1524 _153_1523)))
in (FStar_All.failwith _153_1525))
end
| _56_3186 -> begin
(giveup env "head tag mismatch" orig)
end))))
end))
end)))))))))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (

let c1 = problem.FStar_TypeChecker_Common.lhs
in (

let c2 = problem.FStar_TypeChecker_Common.rhs
in (

let orig = FStar_TypeChecker_Common.CProb (problem)
in (

let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (

let solve_eq = (fun c1_comp c2_comp -> (

let _56_3203 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (

let sub_probs = (FStar_List.map2 (fun _56_3208 _56_3212 -> (match (((_56_3208), (_56_3212))) with
| ((a1, _56_3207), (a2, _56_3211)) -> begin
(let _153_1540 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _153_1539 -> FStar_TypeChecker_Common.TProb (_153_1539)) _153_1540))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (let _153_1542 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _153_1542))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in (

let solve_sub = (fun c1 edge c2 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(

let wp = (match (c1.FStar_Syntax_Syntax.effect_args) with
| ((wp1, _56_3224))::[] -> begin
wp1
end
| _56_3228 -> begin
(let _153_1550 = (let _153_1549 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _153_1549))
in (FStar_All.failwith _153_1550))
end)
in (

let c1 = (let _153_1553 = (let _153_1552 = (let _153_1551 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _153_1551))
in (_153_1552)::[])
in {FStar_Syntax_Syntax.comp_univs = c1.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _153_1553; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2)))
end else begin
(

let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _56_28 -> (match (_56_28) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _56_3236 -> begin
false
end))))
in (

let _56_3257 = (match (((c1.FStar_Syntax_Syntax.effect_args), (c2.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, _56_3242))::_56_3239, ((wp2, _56_3249))::_56_3246) -> begin
((wp1), (wp2))
end
| _56_3254 -> begin
(let _153_1557 = (let _153_1556 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _153_1555 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _153_1556 _153_1555)))
in (FStar_All.failwith _153_1557))
end)
in (match (_56_3257) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _153_1558 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _153_1558 wl))
end else begin
(

let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let g = if is_null_wp_2 then begin
(

let _56_3259 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _153_1568 = (let _153_1567 = (let _153_1566 = (let _153_1560 = (let _153_1559 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_153_1559)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _153_1560 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _153_1565 = (let _153_1564 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _153_1563 = (let _153_1562 = (let _153_1561 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_1561))
in (_153_1562)::[])
in (_153_1564)::_153_1563))
in ((_153_1566), (_153_1565))))
in FStar_Syntax_Syntax.Tm_app (_153_1567))
in (FStar_Syntax_Syntax.mk _153_1568 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(let _153_1580 = (let _153_1579 = (let _153_1578 = (let _153_1570 = (let _153_1569 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_153_1569)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _153_1570 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (let _153_1577 = (let _153_1576 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _153_1575 = (let _153_1574 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _153_1573 = (let _153_1572 = (let _153_1571 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_1571))
in (_153_1572)::[])
in (_153_1574)::_153_1573))
in (_153_1576)::_153_1575))
in ((_153_1578), (_153_1577))))
in FStar_Syntax_Syntax.Tm_app (_153_1579))
in (FStar_Syntax_Syntax.mk _153_1580 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r))
end
in (

let base_prob = (let _153_1582 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _153_1581 -> FStar_TypeChecker_Common.TProb (_153_1581)) _153_1582))
in (

let wl = (let _153_1586 = (let _153_1585 = (let _153_1584 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _153_1584 g))
in (FStar_All.pipe_left (fun _153_1583 -> Some (_153_1583)) _153_1585))
in (solve_prob orig _153_1586 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end
end)))
end))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _153_1587 = (solve_prob orig None [] wl)
in (solve env _153_1587))
end else begin
(

let _56_3264 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1589 = (FStar_Syntax_Print.comp_to_string c1)
in (let _153_1588 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _153_1589 (rel_to_string problem.FStar_TypeChecker_Common.relation) _153_1588)))
end else begin
()
end
in (

let _56_3268 = (let _153_1591 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (let _153_1590 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((_153_1591), (_153_1590))))
in (match (_56_3268) with
| (c1, c2) -> begin
(match (((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, _56_3271), FStar_Syntax_Syntax.Total (t2, _56_3276)) when (FStar_Syntax_Util.non_informative t2) -> begin
(let _153_1592 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _153_1592 wl))
end
| (FStar_Syntax_Syntax.GTotal (_56_3281), FStar_Syntax_Syntax.Total (_56_3284)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.Total (t2, _))) | ((FStar_Syntax_Syntax.GTotal (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) | ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) -> begin
(let _153_1593 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _153_1593 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _153_1596 = (

let _56_3330 = problem
in (let _153_1595 = (let _153_1594 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _153_1594))
in {FStar_TypeChecker_Common.pid = _56_3330.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _153_1595; FStar_TypeChecker_Common.relation = _56_3330.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _56_3330.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_3330.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_3330.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_3330.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_3330.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_3330.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_3330.FStar_TypeChecker_Common.rank}))
in (solve_c env _153_1596 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _153_1599 = (

let _56_3346 = problem
in (let _153_1598 = (let _153_1597 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c2)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _153_1597))
in {FStar_TypeChecker_Common.pid = _56_3346.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_3346.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _56_3346.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _153_1598; FStar_TypeChecker_Common.element = _56_3346.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_3346.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_3346.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_3346.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_3346.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_3346.FStar_TypeChecker_Common.rank}))
in (solve_c env _153_1599 wl))
end
| (FStar_Syntax_Syntax.Comp (_56_3349), FStar_Syntax_Syntax.Comp (_56_3352)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _153_1600 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _153_1600 wl))
end else begin
(

let c1_comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c1)
in (

let c2_comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(

let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (

let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (

let _56_3359 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
if (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (let _153_1601 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative _153_1601))) then begin
(

let edge = {FStar_TypeChecker_Env.msource = c1.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c2.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = (fun r t -> t)}
in (solve_sub c1 edge c2))
end else begin
(let _153_1606 = (let _153_1605 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _153_1604 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _153_1605 _153_1604)))
in (giveup env _153_1606 orig))
end
end
| Some (edge) -> begin
(solve_sub c1 edge c2)
end))))
end))
end
end)
end)))
end)))))))


let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _153_1610 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _56_3379 -> (match (_56_3379) with
| (_56_3369, _56_3371, u, _56_3374, _56_3376, _56_3378) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _153_1610 (FStar_String.concat ", "))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred))) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _56_3386 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
if (((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)) then begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end else begin
"non-trivial"
end
end)
in (

let carry = (let _153_1616 = (FStar_List.map (fun _56_3394 -> (match (_56_3394) with
| (_56_3392, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _153_1616 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _56_3403; FStar_TypeChecker_Env.implicits = _56_3401} -> begin
true
end
| _56_3408 -> begin
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
| _56_3426 -> begin
(FStar_All.failwith "impossible")
end)
in (let _153_1637 = (

let _56_3428 = g
in (let _153_1636 = (let _153_1635 = (let _153_1634 = (let _153_1628 = (FStar_Syntax_Syntax.mk_binder x)
in (_153_1628)::[])
in (let _153_1633 = (let _153_1632 = (let _153_1631 = (let _153_1629 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _153_1629 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _153_1631 (fun _153_1630 -> FStar_Util.Inl (_153_1630))))
in Some (_153_1632))
in (FStar_Syntax_Util.abs _153_1634 f _153_1633)))
in (FStar_All.pipe_left (fun _153_1627 -> FStar_TypeChecker_Common.NonTrivial (_153_1627)) _153_1635))
in {FStar_TypeChecker_Env.guard_f = _153_1636; FStar_TypeChecker_Env.deferred = _56_3428.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_3428.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_3428.FStar_TypeChecker_Env.implicits}))
in Some (_153_1637)))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _56_3435 = g
in (let _153_1648 = (let _153_1647 = (let _153_1646 = (let _153_1645 = (let _153_1644 = (let _153_1643 = (FStar_Syntax_Syntax.as_arg e)
in (_153_1643)::[])
in ((f), (_153_1644)))
in FStar_Syntax_Syntax.Tm_app (_153_1645))
in (FStar_Syntax_Syntax.mk _153_1646 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _153_1642 -> FStar_TypeChecker_Common.NonTrivial (_153_1642)) _153_1647))
in {FStar_TypeChecker_Env.guard_f = _153_1648; FStar_TypeChecker_Env.deferred = _56_3435.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_3435.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_3435.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_56_3440) -> begin
(FStar_All.failwith "impossible")
end))


let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _153_1655 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_153_1655))
end))


let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _56_3458 -> begin
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


let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _153_1678 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _153_1678; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _56_3485 = g
in (let _153_1693 = (let _153_1692 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _153_1692 (fun _153_1691 -> FStar_TypeChecker_Common.NonTrivial (_153_1691))))
in {FStar_TypeChecker_Env.guard_f = _153_1693; FStar_TypeChecker_Env.deferred = _56_3485.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_3485.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_3485.FStar_TypeChecker_Env.implicits}))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _153_1701 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _153_1700 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _153_1701 (rel_to_string rel) _153_1700)))
end else begin
"TOP"
end
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (let _153_1712 = (let _153_1711 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _153_1710 -> Some (_153_1710)) _153_1711))
in (FStar_Syntax_Syntax.new_bv _153_1712 t1))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (let _153_1716 = (let _153_1714 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _153_1713 -> Some (_153_1713)) _153_1714))
in (let _153_1715 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _153_1716 _153_1715)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (

let probs = if (FStar_Options.eager_inference ()) then begin
(

let _56_3505 = probs
in {attempting = _56_3505.attempting; wl_deferred = _56_3505.wl_deferred; ctr = _56_3505.ctr; defer_ok = false; smt_ok = _56_3505.smt_ok; tcenv = _56_3505.tcenv})
end else begin
probs
end
in (

let tx = (FStar_Unionfind.new_transaction ())
in (

let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
(

let _56_3512 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(

let _56_3518 = (FStar_Unionfind.rollback tx)
in (

let _56_3520 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _153_1728 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _153_1728))
end else begin
()
end
in (err ((d), (s)))))
end)))))


let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _56_3527 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _153_1733 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _153_1733))
end else begin
()
end
in (

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (

let _56_3530 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _153_1734 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _153_1734))
end else begin
()
end
in (

let f = (match ((let _153_1735 = (FStar_Syntax_Util.unmeta f)
in _153_1735.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _56_3535 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (

let _56_3537 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _56_3537.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_3537.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_3537.FStar_TypeChecker_Env.implicits})))))
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _153_1747 = (let _153_1746 = (let _153_1745 = (let _153_1744 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _153_1744 (fun _153_1743 -> FStar_TypeChecker_Common.NonTrivial (_153_1743))))
in {FStar_TypeChecker_Env.guard_f = _153_1745; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _153_1746))
in (FStar_All.pipe_left (fun _153_1742 -> Some (_153_1742)) _153_1747))
end))


let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (

let _56_3548 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1755 = (FStar_Syntax_Print.term_to_string t1)
in (let _153_1754 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _153_1755 _153_1754)))
end else begin
()
end
in (

let prob = (let _153_1758 = (let _153_1757 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _153_1757))
in (FStar_All.pipe_left (fun _153_1756 -> FStar_TypeChecker_Common.TProb (_153_1756)) _153_1758))
in (

let g = (let _153_1760 = (solve_and_commit env (singleton env prob) (fun _56_3551 -> None))
in (FStar_All.pipe_left (with_guard env prob) _153_1760))
in g))))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _153_1770 = (let _153_1769 = (let _153_1768 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _153_1767 = (FStar_TypeChecker_Env.get_range env)
in ((_153_1768), (_153_1767))))
in FStar_Syntax_Syntax.Error (_153_1769))
in (Prims.raise _153_1770))
end
| Some (g) -> begin
(

let _56_3560 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1773 = (FStar_Syntax_Print.term_to_string t1)
in (let _153_1772 = (FStar_Syntax_Print.term_to_string t2)
in (let _153_1771 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _153_1773 _153_1772 _153_1771))))
end else begin
()
end
in g)
end))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 smt_ok -> (

let _56_3566 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1783 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _153_1782 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _153_1783 _153_1782)))
end else begin
()
end
in (

let _56_3571 = (

let rel = FStar_TypeChecker_Common.SUB
in (new_t_prob env t1 rel t2))
in (match (_56_3571) with
| (prob, x) -> begin
(

let g = (let _153_1785 = (solve_and_commit env (singleton' env prob smt_ok) (fun _56_3572 -> None))
in (FStar_All.pipe_left (with_guard env prob) _153_1785))
in (

let _56_3575 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _153_1789 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _153_1788 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _153_1787 = (let _153_1786 = (FStar_Util.must g)
in (guard_to_string env _153_1786))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _153_1789 _153_1788 _153_1787))))
end else begin
()
end
in (abstract_guard x g)))
end))))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env e t1 t2 -> (let _153_1805 = (FStar_TypeChecker_Env.get_range env)
in (let _153_1804 = (FStar_TypeChecker_Errors.basic_type_error env (Some (e)) t2 t1)
in (FStar_TypeChecker_Errors.report _153_1805 _153_1804))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (

let _56_3587 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1813 = (FStar_Syntax_Print.comp_to_string c1)
in (let _153_1812 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _153_1813 _153_1812)))
end else begin
()
end
in (

let rel = if env.FStar_TypeChecker_Env.use_eq then begin
FStar_TypeChecker_Common.EQ
end else begin
FStar_TypeChecker_Common.SUB
end
in (

let prob = (let _153_1816 = (let _153_1815 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _153_1815 "sub_comp"))
in (FStar_All.pipe_left (fun _153_1814 -> FStar_TypeChecker_Common.CProb (_153_1814)) _153_1816))
in (let _153_1818 = (solve_and_commit env (singleton env prob) (fun _56_3591 -> None))
in (FStar_All.pipe_left (with_guard env prob) _153_1818))))))


let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (

let fail = (fun msg u1 u2 -> (

let _56_3600 = (FStar_Unionfind.rollback tx)
in (

let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _153_1836 = (let _153_1835 = (let _153_1834 = (let _153_1832 = (FStar_Syntax_Print.univ_to_string u1)
in (let _153_1831 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _153_1832 _153_1831 msg)))
in (let _153_1833 = (FStar_TypeChecker_Env.get_range env)
in ((_153_1834), (_153_1833))))
in FStar_Syntax_Syntax.Error (_153_1835))
in (Prims.raise _153_1836)))))
in (

let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
(((uv), ((u1)::[])))::[]
end
| (hd)::tl -> begin
(

let _56_3616 = hd
in (match (_56_3616) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
(((uv'), ((u1)::lower_bounds)))::tl
end else begin
(let _153_1843 = (insert uv u1 tl)
in (hd)::_153_1843)
end
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
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
(group_by out rest)
end else begin
(let _153_1848 = (insert uv u1 out)
in (group_by _153_1848 rest))
end)
end
| _56_3631 -> begin
None
end))
end))
in (

let ad_hoc_fallback = (fun _56_3633 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _56_3636 -> begin
(

let wl = (

let _56_3637 = (empty_worklist env)
in {attempting = _56_3637.attempting; wl_deferred = _56_3637.wl_deferred; ctr = _56_3637.ctr; defer_ok = true; smt_ok = _56_3637.smt_ok; tcenv = _56_3637.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun _56_3642 -> (match (_56_3642) with
| (u1, u2) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _56_3647 -> begin
(match ((solve_universe_eq (~- ((Prims.parse_int "1"))) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(

let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _56_3657 -> begin
(u1)::[]
end)
in (

let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _56_3662 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _56_29 -> (match (_56_29) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(

let _56_3669 = (FStar_Syntax_Util.univ_kernel u)
in (match (_56_3669) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (

let _56_3673 = (FStar_Syntax_Util.univ_kernel u')
in (match (_56_3673) with
| (k_u', n') -> begin
((FStar_Syntax_Util.eq_univs k_u k_u') && (n <= n'))
end)))))
end))
end)))) then begin
()
end else begin
(fail None u1 u2)
end))
end
| USolved (_56_3675) -> begin
()
end)
end)))
end)))))
end)
end))
in (match ((group_by [] ineqs)) with
| Some (groups) -> begin
(

let wl = (

let _56_3679 = (empty_worklist env)
in {attempting = _56_3679.attempting; wl_deferred = _56_3679.wl_deferred; ctr = _56_3679.ctr; defer_ok = false; smt_ok = _56_3679.smt_ok; tcenv = _56_3679.tcenv})
in (

let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| ((u, lower_bounds))::groups -> begin
(match ((solve_universe_eq (~- ((Prims.parse_int "1"))) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| _56_3694 -> begin
(ad_hoc_fallback ())
end)
end))
in (solve_all_groups wl groups)))
end
| None -> begin
(ad_hoc_fallback ())
end))))))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun env ineqs -> (

let tx = (FStar_Unionfind.new_transaction ())
in (

let _56_3699 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail = (fun _56_3706 -> (match (_56_3706) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (

let _56_3709 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _153_1869 = (wl_to_string wl)
in (let _153_1868 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _153_1869 _153_1868)))
end else begin
()
end
in (

let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(

let _56_3713 = g
in {FStar_TypeChecker_Env.guard_f = _56_3713.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _56_3713.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_3713.FStar_TypeChecker_Env.implicits})
end
| _56_3716 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (

let _56_3718 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (

let _56_3720 = g
in {FStar_TypeChecker_Env.guard_f = _56_3720.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _56_3720.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _56_3720.FStar_TypeChecker_Env.implicits})))))))


let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (

let g = (solve_deferred_constraints env g)
in (

let _56_3737 = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(

let _56_3729 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Norm"))) then begin
(let _153_1886 = (FStar_TypeChecker_Env.get_range env)
in (let _153_1885 = (let _153_1884 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" _153_1884))
in (FStar_TypeChecker_Errors.diag _153_1886 _153_1885)))
end else begin
()
end
in (

let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(

let _56_3735 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_1889 = (FStar_TypeChecker_Env.get_range env)
in (let _153_1888 = (let _153_1887 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _153_1887))
in (FStar_TypeChecker_Errors.diag _153_1889 _153_1888)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc))
end)))
end)
end
in (

let _56_3739 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_3739.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_3739.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_3739.FStar_TypeChecker_Env.implicits}))))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _56_3748 -> begin
false
end))
in (

let rec until_fixpoint = (fun _56_3752 implicits -> (match (_56_3752) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
if (not (changed)) then begin
out
end else begin
(until_fixpoint (([]), (false)) out)
end
end
| (hd)::tl -> begin
(

let _56_3765 = hd
in (match (_56_3765) with
| (_56_3759, env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint (((hd)::out), (changed)) tl)
end else begin
(

let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (

let _56_3768 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _153_1905 = (FStar_Syntax_Print.uvar_to_string u)
in (let _153_1904 = (FStar_Syntax_Print.term_to_string tm)
in (let _153_1903 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _153_1905 _153_1904 _153_1903))))
end else begin
()
end
in (

let _56_3777 = (env.FStar_TypeChecker_Env.type_of (

let _56_3770 = env
in {FStar_TypeChecker_Env.solver = _56_3770.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _56_3770.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _56_3770.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _56_3770.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _56_3770.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _56_3770.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _56_3770.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _56_3770.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _56_3770.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _56_3770.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _56_3770.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _56_3770.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _56_3770.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _56_3770.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _56_3770.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _56_3770.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _56_3770.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _56_3770.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _56_3770.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _56_3770.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _56_3770.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _56_3770.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _56_3770.FStar_TypeChecker_Env.qname_and_index}) tm)
in (match (_56_3777) with
| (_56_3773, _56_3775, g) -> begin
(

let g = if env.FStar_TypeChecker_Env.is_pattern then begin
(

let _56_3778 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_3778.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_3778.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_3778.FStar_TypeChecker_Env.implicits})
end else begin
g
end
in (

let g' = (discharge_guard' (Some ((fun _56_3781 -> (match (()) with
| () -> begin
(FStar_Syntax_Print.term_to_string tm)
end)))) env g)
in (until_fixpoint (((FStar_List.append g'.FStar_TypeChecker_Env.implicits out)), (true)) tl)))
end)))))
end
end))
end)
end))
in (

let _56_3783 = g
in (let _153_1909 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _56_3783.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _56_3783.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_3783.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _153_1909})))))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g = (let _153_1914 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _153_1914 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _153_1915 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _153_1915))
end
| ((reason, _56_3793, _56_3795, e, t, r))::_56_3790 -> begin
(let _153_1918 = (let _153_1917 = (FStar_Syntax_Print.term_to_string t)
in (let _153_1916 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" _153_1917 _153_1916 reason)))
in (FStar_TypeChecker_Errors.report r _153_1918))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let _56_3803 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _56_3803.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _56_3803.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (((u1), (u2)))::[]; FStar_TypeChecker_Env.implicits = _56_3803.FStar_TypeChecker_Env.implicits}))





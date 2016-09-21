
open Prims

let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (

let uv = (FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(

let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k)))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((uv), (uv)))
end
| _55_37 -> begin
(

let args = (FStar_All.pipe_right binders (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder))
in (

let k' = (let _149_7 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _149_7))
in (

let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k')))) None r)
in (let _149_8 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((uv), (args)))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((_149_8), (uv))))))
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
| TERM (_55_43) -> begin
_55_43
end))


let ___UNIV____0 = (fun projectee -> (match (projectee) with
| UNIV (_55_46) -> begin
_55_46
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
| Success (_55_56) -> begin
_55_56
end))


let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_55_59) -> begin
_55_59
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


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun _55_1 -> (match (_55_1) with
| FStar_TypeChecker_Common.EQ -> begin
"="
end
| FStar_TypeChecker_Common.SUB -> begin
"<:"
end
| FStar_TypeChecker_Common.SUBINV -> begin
":>"
end))


let term_to_string = (fun env t -> (match ((let _149_91 = (FStar_Syntax_Subst.compress t)
in _149_91.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, t) -> begin
(let _149_93 = (FStar_Syntax_Print.uvar_to_string u)
in (let _149_92 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "(%s:%s)" _149_93 _149_92)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty); FStar_Syntax_Syntax.tk = _55_77; FStar_Syntax_Syntax.pos = _55_75; FStar_Syntax_Syntax.vars = _55_73}, args) -> begin
(let _149_96 = (FStar_Syntax_Print.uvar_to_string u)
in (let _149_95 = (FStar_Syntax_Print.term_to_string ty)
in (let _149_94 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "(%s:%s) %s" _149_96 _149_95 _149_94))))
end
| _55_87 -> begin
(FStar_Syntax_Print.term_to_string t)
end))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _55_2 -> (match (_55_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _149_115 = (let _149_114 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _149_113 = (let _149_112 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _149_111 = (let _149_110 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _149_109 = (let _149_108 = (let _149_107 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _149_106 = (let _149_105 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _149_104 = (let _149_103 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _149_102 = (let _149_101 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_149_101)::[])
in (_149_103)::_149_102))
in (_149_105)::_149_104))
in (_149_107)::_149_106))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_149_108)
in (_149_110)::_149_109))
in (_149_112)::_149_111))
in (_149_114)::_149_113))
in (FStar_Util.format "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _149_115))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _149_117 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _149_116 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _149_117 (rel_to_string p.FStar_TypeChecker_Common.relation) _149_116)))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _55_3 -> (match (_55_3) with
| UNIV (u, t) -> begin
(

let x = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _149_122 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _149_122 FStar_Util.string_of_int))
end
in (let _149_123 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _149_123)))
end
| TERM ((u, _55_103), t) -> begin
(

let x = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _149_124 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _149_124 FStar_Util.string_of_int))
end
in (let _149_125 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _149_125)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _149_130 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _149_130 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (let _149_134 = (let _149_133 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _149_133 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _149_134 (FStar_String.concat ", "))))


let args_to_string = (fun args -> (let _149_137 = (FStar_All.pipe_right args (FStar_List.map (fun _55_116 -> (match (_55_116) with
| (x, _55_115) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _149_137 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = true; smt_ok = true; tcenv = env})


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let _55_121 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _55_121.wl_deferred; ctr = _55_121.ctr; defer_ok = _55_121.defer_ok; smt_ok = smt_ok; tcenv = _55_121.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard = (fun env g -> (

let _55_127 = (empty_worklist env)
in (let _149_152 = (FStar_List.map Prims.snd g)
in {attempting = _149_152; wl_deferred = _55_127.wl_deferred; ctr = _55_127.ctr; defer_ok = false; smt_ok = _55_127.smt_ok; tcenv = _55_127.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let _55_132 = wl
in {attempting = _55_132.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = _55_132.ctr; defer_ok = _55_132.defer_ok; smt_ok = _55_132.smt_ok; tcenv = _55_132.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let _55_136 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _55_136.wl_deferred; ctr = _55_136.ctr; defer_ok = _55_136.defer_ok; smt_ok = _55_136.smt_ok; tcenv = _55_136.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (

let _55_141 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_169 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _149_169))
end else begin
()
end
in Failed (((prob), (reason)))))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun _55_4 -> (match (_55_4) with
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

let _55_148 = p
in {FStar_TypeChecker_Common.pid = _55_148.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _55_148.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_148.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_148.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_148.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_148.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_148.FStar_TypeChecker_Common.rank}))


let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _55_5 -> (match (_55_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _149_176 -> FStar_TypeChecker_Common.TProb (_149_176)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _149_177 -> FStar_TypeChecker_Common.CProb (_149_177)))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel _55_6 -> (match (_55_6) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun _55_7 -> (match (_55_7) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun _55_8 -> (match (_55_8) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun _55_9 -> (match (_55_9) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun _55_10 -> (match (_55_10) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun _55_11 -> (match (_55_11) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun _55_12 -> (match (_55_12) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _55_13 -> (match (_55_13) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _149_196 -> FStar_TypeChecker_Common.TProb (_149_196)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _149_197 -> FStar_TypeChecker_Common.CProb (_149_197)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = (Prims.parse_int "1")))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_ST.alloc (Prims.parse_int "0"))
in (fun _55_198 -> (match (()) with
| () -> begin
(

let _55_199 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))


let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _149_210 = (next_pid ())
in (let _149_209 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _149_210; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _149_209; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))


let new_problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _149_220 = (next_pid ())
in (let _149_219 = (let _149_218 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _149_218 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _149_220; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _149_219; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _149_227 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _149_227; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))


let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _149_239 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _149_238 = (prob_to_string env d)
in (let _149_237 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _149_239 _149_238 _149_237 s))))
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
| _55_235 -> begin
(FStar_All.failwith "impossible")
end)
in (

let _55_243 = (match (d) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(let _149_241 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (let _149_240 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((_149_241), (_149_240))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _149_243 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (let _149_242 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((_149_243), (_149_242))))
end)
in (match (_55_243) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)


let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _55_14 -> (match (_55_14) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| _55_253 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _55_256), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _55_15 -> (match (_55_15) with
| UNIV (_55_265) -> begin
None
end
| TERM ((u, _55_269), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun _55_16 -> (match (_55_16) with
| UNIV (u', t) -> begin
if (FStar_Unionfind.equivalent u u') then begin
Some (t)
end else begin
None
end
end
| _55_282 -> begin
None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _149_262 = (let _149_261 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _149_261))
in (FStar_Syntax_Subst.compress _149_262)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _149_267 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _149_267)))


let norm_arg = (fun env t -> (let _149_270 = (sn env (Prims.fst t))
in ((_149_270), ((Prims.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _55_293 -> (match (_55_293) with
| (x, imp) -> begin
(let _149_277 = (

let _55_294 = x
in (let _149_276 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_294.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_294.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_276}))
in ((_149_277), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _149_284 = (aux u)
in FStar_Syntax_Syntax.U_succ (_149_284))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _149_285 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_149_285))
end
| _55_306 -> begin
u
end)))
in (let _149_286 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _149_286))))


let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement = (fun env wl t1 -> (

let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
if norm then begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end else begin
(match ((normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _55_326; FStar_Syntax_Syntax.pos = _55_324; FStar_Syntax_Syntax.vars = _55_322} -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| tt -> begin
(let _149_300 = (let _149_299 = (FStar_Syntax_Print.term_to_string tt)
in (let _149_298 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _149_299 _149_298)))
in (FStar_All.failwith _149_300))
end)
end
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
if norm then begin
((t1), (None))
end else begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (match ((let _149_301 = (FStar_Syntax_Subst.compress t1')
in _149_301.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_refine (_55_344) -> begin
(aux true t1')
end
| _55_347 -> begin
((t1), (None))
end))
end
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
((t1), (None))
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _149_304 = (let _149_303 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_302 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _149_303 _149_302)))
in (FStar_All.failwith _149_304))
end))
in (let _149_305 = (whnf env t1)
in (aux false _149_305))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _149_310 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _149_310 Prims.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _149_313 = (FStar_Syntax_Syntax.null_bv t)
in ((_149_313), (FStar_Syntax_Util.t_true))))


let as_refinement = (fun env wl t -> (

let _55_393 = (base_and_refinement env wl t)
in (match (_55_393) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement = (fun _55_401 -> (match (_55_401) with
| (t_base, refopt) -> begin
(

let _55_409 = (match (refopt) with
| Some (y, phi) -> begin
((y), (phi))
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_55_409) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _55_17 -> (match (_55_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _149_326 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _149_325 = (let _149_322 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _149_322))
in (let _149_324 = (let _149_323 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _149_323))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _149_326 _149_325 (rel_to_string p.FStar_TypeChecker_Common.relation) _149_324))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _149_329 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _149_328 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _149_327 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _149_329 _149_328 (rel_to_string p.FStar_TypeChecker_Common.relation) _149_327))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _149_335 = (let _149_334 = (let _149_333 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _55_422 -> (match (_55_422) with
| (_55_418, _55_420, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _149_333))
in (FStar_List.map (wl_prob_to_string wl) _149_334))
in (FStar_All.pipe_right _149_335 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let _55_441 = (match ((let _149_342 = (FStar_Syntax_Subst.compress k)
in _149_342.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if ((FStar_List.length bs) = (FStar_List.length ys)) then begin
(let _149_343 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (_149_343)))
end else begin
(

let _55_432 = (FStar_Syntax_Util.abs_formals t)
in (match (_55_432) with
| (ys', t) -> begin
(let _149_344 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t))), (_149_344)))
end))
end
end
| _55_434 -> begin
(let _149_346 = (let _149_345 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_149_345)))
in ((((ys), (t))), (_149_346)))
end)
in (match (_55_441) with
| ((ys, t), (xs, c)) -> begin
if ((FStar_List.length xs) <> (FStar_List.length ys)) then begin
(FStar_Syntax_Util.abs ys t (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))
end else begin
(

let c = (let _149_347 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp _149_347 c))
in (let _149_351 = (let _149_350 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _149_348 -> FStar_Util.Inl (_149_348)))
in (FStar_All.pipe_right _149_350 (fun _149_349 -> Some (_149_349))))
in (FStar_Syntax_Util.abs ys t _149_351)))
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

let _55_455 = (p_guard prob)
in (match (_55_455) with
| (_55_453, uv) -> begin
(

let _55_466 = (match ((let _149_362 = (FStar_Syntax_Subst.compress uv)
in _149_362.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi = (u_abs k bs phi)
in (

let _55_462 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _149_365 = (FStar_Util.string_of_int (p_pid prob))
in (let _149_364 = (FStar_Syntax_Print.term_to_string uv)
in (let _149_363 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _149_365 _149_364 _149_363))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi))))
end
| _55_465 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (

let _55_468 = (commit uvis)
in (

let _55_470 = wl
in {attempting = _55_470.attempting; wl_deferred = _55_470.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = _55_470.defer_ok; smt_ok = _55_470.smt_ok; tcenv = _55_470.tcenv})))
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (

let _55_475 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_374 = (FStar_Util.string_of_int pid)
in (let _149_373 = (let _149_372 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _149_372 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _149_374 _149_373)))
end else begin
()
end
in (

let _55_477 = (commit sol)
in (

let _55_479 = wl
in {attempting = _55_479.attempting; wl_deferred = _55_479.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = _55_479.defer_ok; smt_ok = _55_479.smt_ok; tcenv = _55_479.tcenv}))))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard = (fun t g -> (match (((t), (g))) with
| (_55_489, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _149_387 = (FStar_Syntax_Util.mk_conj t f)
in Some (_149_387))
end))
in (

let _55_501 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_390 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _149_389 = (let _149_388 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _149_388 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _149_390 _149_389)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))


let rec occurs = (fun wl uk t -> (let _149_400 = (let _149_398 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _149_398 FStar_Util.set_elements))
in (FStar_All.pipe_right _149_400 (FStar_Util.for_some (fun _55_510 -> (match (_55_510) with
| (uv, _55_509) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (not ((occurs wl uk t)))
in (

let msg = if occurs_ok then begin
None
end else begin
(let _149_407 = (let _149_406 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _149_405 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _149_406 _149_405)))
in Some (_149_407))
end
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let _55_525 = (occurs_check env wl uk t)
in (match (_55_525) with
| (occurs_ok, msg) -> begin
(let _149_413 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (_149_413), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set v1)
in (

let _55_543 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _55_535 _55_538 -> (match (((_55_535), (_55_538))) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _149_422 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _149_422)) then begin
((isect), (isect_set))
end else begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _149_423 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (_149_423)))
end else begin
((isect), (isect_set))
end)
end
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (_55_543) with
| (isect, _55_542) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _55_549 _55_553 -> (match (((_55_549), (_55_553))) with
| ((a, _55_548), (b, _55_552)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _55_563 -> (match (_55_563) with
| (b, _55_562) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some (((a), ((Prims.snd hd))))
end
end
| _55_565 -> begin
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

let _55_574 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_438 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _149_438))
end else begin
()
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))


let is_flex : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _149_441 = (FStar_Syntax_Subst.compress t)
in _149_441.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
true
end
| _55_597 -> begin
false
end))


let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _55_608; FStar_Syntax_Syntax.pos = _55_606; FStar_Syntax_Syntax.vars = _55_604}, args) -> begin
((t), (uv), (k), (args))
end
| _55_618 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let _55_625 = (destruct_flex_t t)
in (match (_55_625) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((((t), (uv), (k), (args))), (Some (vars)))
end
| _55_629 -> begin
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
| MisMatch (_55_632) -> begin
_55_632
end))


let head_match : match_result  ->  match_result = (fun _55_18 -> (match (_55_18) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| _55_639 -> begin
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
| (FStar_Syntax_Syntax.Tm_uinst (f, _55_725), FStar_Syntax_Syntax.Tm_uinst (g, _55_730)) -> begin
(let _149_477 = (head_matches env f g)
in (FStar_All.pipe_right _149_477 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch (((None), (None)))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _55_741), FStar_Syntax_Syntax.Tm_uvar (uv', _55_746)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch (((None), (None)))
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_752), FStar_Syntax_Syntax.Tm_refine (y, _55_757)) -> begin
(let _149_478 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _149_478 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_763), _55_767) -> begin
(let _149_479 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _149_479 head_match))
end
| (_55_770, FStar_Syntax_Syntax.Tm_refine (x, _55_773)) -> begin
(let _149_480 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _149_480 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _55_793), FStar_Syntax_Syntax.Tm_app (head', _55_798)) -> begin
(let _149_481 = (head_matches env head head')
in (FStar_All.pipe_right _149_481 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head, _55_804), _55_808) -> begin
(let _149_482 = (head_matches env head t2)
in (FStar_All.pipe_right _149_482 head_match))
end
| (_55_811, FStar_Syntax_Syntax.Tm_app (head, _55_814)) -> begin
(let _149_483 = (head_matches env t1 head)
in (FStar_All.pipe_right _149_483 head_match))
end
| _55_819 -> begin
(let _149_486 = (let _149_485 = (delta_depth_of_term env t1)
in (let _149_484 = (delta_depth_of_term env t2)
in ((_149_485), (_149_484))))
in MisMatch (_149_486))
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let success = (fun d r t1 t2 -> ((r), (if (d > (Prims.parse_int "0")) then begin
Some (((t1), (t2)))
end else begin
None
end)))
in (

let fail = (fun r -> ((r), (None)))
in (

let rec aux = (fun n_delta t1 t2 -> (

let r = (head_matches env t1 t2)
in (match (r) with
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
in (aux (n_delta + (Prims.parse_int "1")) t1 t2)))
end)
end
| (MisMatch (Some (FStar_Syntax_Syntax.Delta_equational), _)) | (MisMatch (_, Some (FStar_Syntax_Syntax.Delta_equational))) -> begin
(fail r)
end
| MisMatch (Some (d1), Some (d2)) -> begin
(

let d1_greater_than_d2 = (FStar_TypeChecker_Common.delta_depth_greater_than d1 d2)
in (

let _55_870 = if d1_greater_than_d2 then begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in ((t1'), (t2)))
end else begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (let _149_507 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in ((t1), (_149_507))))
end
in (match (_55_870) with
| (t1, t2) -> begin
(aux (n_delta + (Prims.parse_int "1")) t1 t2)
end)))
end
| MisMatch (_55_872) -> begin
(fail r)
end
| _55_875 -> begin
(success n_delta r t1 t2)
end)))
in (aux (Prims.parse_int "0") t1 t2)))))


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
| T (_55_878) -> begin
_55_878
end))


let ___C____0 = (fun projectee -> (match (projectee) with
| C (_55_881) -> begin
_55_881
end))


type tcs =
tc Prims.list


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let _55_887 = (FStar_Syntax_Util.type_u ())
in (match (_55_887) with
| (t, _55_886) -> begin
(let _149_578 = (new_uvar r binders t)
in (Prims.fst _149_578))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (let _149_583 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_583 Prims.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (match ((head_matches env t t')) with
| MisMatch (_55_896) -> begin
false
end
| _55_899 -> begin
true
end))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(

let rebuild = (fun args' -> (

let args = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((_55_909, imp), T (t, _55_914)) -> begin
((t), (imp))
end
| _55_919 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), (args)))) None t.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _55_924 -> (match (_55_924) with
| (t, _55_923) -> begin
((None), (INVARIANT), (T (((t), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let fail = (fun _55_931 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (

let _55_934 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_55_934) with
| (bs, c) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs tcs -> (match (((bs), (tcs))) with
| (((x, imp))::bs, (T (t, _55_949))::tcs) -> begin
(aux (((((

let _55_954 = x
in {FStar_Syntax_Syntax.ppname = _55_954.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_954.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp)))::out) bs tcs)
end
| ([], (C (c))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _55_962 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (

let rec decompose = (fun out _55_19 -> (match (_55_19) with
| [] -> begin
(FStar_List.rev ((((None), (COVARIANT), (C (c))))::out))
end
| (hd)::rest -> begin
(decompose ((((Some (hd)), (CONTRAVARIANT), (T ((((Prims.fst hd).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (let _149_645 = (decompose [] bs)
in ((rebuild), (matches), (_149_645)))))
end)))
end
| _55_971 -> begin
(

let rebuild = (fun _55_20 -> (match (_55_20) with
| [] -> begin
t
end
| _55_975 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t -> true)), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _55_21 -> (match (_55_21) with
| T (t, _55_981) -> begin
t
end
| _55_985 -> begin
(FStar_All.failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _55_22 -> (match (_55_22) with
| T (t, _55_989) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _55_993 -> begin
(FStar_All.failwith "Impossible")
end))


let imitation_sub_probs = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope args q -> (match (q) with
| (_55_1006, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope r)
in (

let _55_1016 = (new_uvar r scope k)
in (match (_55_1016) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| _55_1019 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) None r)
end)
in (let _149_677 = (let _149_676 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _149_675 -> FStar_TypeChecker_Common.TProb (_149_675)) _149_676))
in ((T (((gi_xs), (mk_kind)))), (_149_677))))
end)))
end
| (_55_1022, _55_1024, C (_55_1026)) -> begin
(FStar_All.failwith "impos")
end))
in (

let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs -> begin
(

let _55_1114 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.tk = _55_1044; FStar_Syntax_Syntax.pos = _55_1042; FStar_Syntax_Syntax.vars = _55_1040})) -> begin
(match ((sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))) with
| (T (gi_xs, _55_1054), prob) -> begin
(let _149_690 = (let _149_689 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _149_688 -> C (_149_688)) _149_689))
in ((_149_690), ((prob)::[])))
end
| _55_1060 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.tk = _55_1068; FStar_Syntax_Syntax.pos = _55_1066; FStar_Syntax_Syntax.vars = _55_1064})) -> begin
(match ((sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))) with
| (T (gi_xs, _55_1078), prob) -> begin
(let _149_697 = (let _149_696 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _149_695 -> C (_149_695)) _149_696))
in ((_149_697), ((prob)::[])))
end
| _55_1084 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_55_1086, _55_1088, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _55_1094; FStar_Syntax_Syntax.pos = _55_1092; FStar_Syntax_Syntax.vars = _55_1090})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((None), (INVARIANT), (T ((((Prims.fst t)), (generic_kind))))))))
in (

let components = (((None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let _55_1105 = (let _149_703 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _149_703 FStar_List.unzip))
in (match (_55_1105) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (let _149_708 = (let _149_707 = (let _149_704 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _149_704 un_T))
in (let _149_706 = (let _149_705 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _149_705 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _149_707; FStar_Syntax_Syntax.effect_args = _149_706; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _149_708))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| _55_1108 -> begin
(

let _55_1111 = (sub_prob scope args q)
in (match (_55_1111) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (_55_1114) with
| (tc, probs) -> begin
(

let _55_1127 = (match (q) with
| (Some (b), _55_1118, _55_1120) -> begin
(let _149_710 = (let _149_709 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_149_709)::args)
in ((Some (b)), ((b)::scope), (_149_710)))
end
| _55_1123 -> begin
((None), (scope), (args))
end)
in (match (_55_1127) with
| (bopt, scope, args) -> begin
(

let _55_1131 = (aux scope args qs)
in (match (_55_1131) with
| (sub_probs, tcs, f) -> begin
(

let f = (match (bopt) with
| None -> begin
(let _149_713 = (let _149_712 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_149_712)
in (FStar_Syntax_Util.mk_conj_l _149_713))
end
| Some (b) -> begin
(let _149_717 = (let _149_716 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _149_715 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_149_716)::_149_715))
in (FStar_Syntax_Util.mk_conj_l _149_717))
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
| (FStar_Syntax_Syntax.Tm_uvar (u1, _55_1159), FStar_Syntax_Syntax.Tm_uvar (u2, _55_1164)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _55_1178 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _55_1184 _55_1188 -> (match (((_55_1184), (_55_1188))) with
| ((a1, _55_1183), (a2, _55_1187)) -> begin
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

let _55_1191 = p
in (let _149_739 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _149_738 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _55_1191.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _149_739; FStar_TypeChecker_Common.relation = _55_1191.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _149_738; FStar_TypeChecker_Common.element = _55_1191.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1191.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1191.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1191.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1191.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1191.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _149_745 = (compress_tprob wl p)
in (FStar_All.pipe_right _149_745 (fun _149_744 -> FStar_TypeChecker_Common.TProb (_149_744))))
end
| FStar_TypeChecker_Common.CProb (_55_1198) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (let _149_750 = (compress_prob wl pr)
in (FStar_All.pipe_right _149_750 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let _55_1208 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1208) with
| (lh, _55_1207) -> begin
(

let _55_1212 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1212) with
| (rh, _55_1211) -> begin
(

let _55_1268 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (_55_1214), FStar_Syntax_Syntax.Tm_uvar (_55_1217)) -> begin
((flex_flex), (tp))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (_55_1233), _55_1236) -> begin
(

let _55_1240 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1240) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((flex_rigid), (tp))
end
| _55_1243 -> begin
(

let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _149_752 = (

let _55_1245 = tp
in (let _149_751 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = _55_1245.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1245.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1245.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _149_751; FStar_TypeChecker_Common.element = _55_1245.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1245.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1245.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1245.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1245.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1245.FStar_TypeChecker_Common.rank}))
in ((rank), (_149_752))))
end)
end))
end
| (_55_1248, FStar_Syntax_Syntax.Tm_uvar (_55_1250)) -> begin
(

let _55_1255 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1255) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((rigid_flex), (tp))
end
| _55_1258 -> begin
(let _149_754 = (

let _55_1259 = tp
in (let _149_753 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = _55_1259.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _149_753; FStar_TypeChecker_Common.relation = _55_1259.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1259.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1259.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1259.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1259.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1259.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1259.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1259.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (_149_754)))
end)
end))
end
| (_55_1262, _55_1264) -> begin
((rigid_rigid), (tp))
end)
in (match (_55_1268) with
| (rank, tp) -> begin
(let _149_756 = (FStar_All.pipe_right (

let _55_1269 = tp
in {FStar_TypeChecker_Common.pid = _55_1269.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1269.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1269.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1269.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1269.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1269.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1269.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1269.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1269.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _149_755 -> FStar_TypeChecker_Common.TProb (_149_755)))
in ((rank), (_149_756)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _149_758 = (FStar_All.pipe_right (

let _55_1273 = cp
in {FStar_TypeChecker_Common.pid = _55_1273.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1273.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1273.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1273.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1273.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1273.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1273.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1273.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1273.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _149_757 -> FStar_TypeChecker_Common.CProb (_149_757)))
in ((rigid_rigid), (_149_758)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun _55_1280 probs -> (match (_55_1280) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
((min), (out), (min_rank))
end
| (hd)::tl -> begin
(

let _55_1288 = (rank wl hd)
in (match (_55_1288) with
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
| UDeferred (_55_1299) -> begin
_55_1299
end))


let ___USolved____0 = (fun projectee -> (match (projectee) with
| USolved (_55_1302) -> begin
_55_1302
end))


let ___UFailed____0 = (fun projectee -> (match (projectee) with
| UFailed (_55_1305) -> begin
_55_1305
end))


let rec really_solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (

let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (

let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (

let _55_1321 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_1321) with
| (k, _55_1320) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _55_1325 -> begin
false
end)
end)))))
end
| _55_1327 -> begin
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
| _55_1352 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end else begin
(let _149_838 = (let _149_837 = (FStar_Syntax_Print.univ_to_string u1)
in (let _149_836 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _149_837 _149_836)))
in UFailed (_149_838))
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
| _55_1370 -> begin
(let _149_845 = (let _149_844 = (FStar_Syntax_Print.univ_to_string u1)
in (let _149_843 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _149_844 _149_843 msg)))
in UFailed (_149_845))
end))
in (match (((u1), (u2))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(let _149_848 = (let _149_847 = (FStar_Syntax_Print.univ_to_string u1)
in (let _149_846 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" _149_847 _149_846)))
in (FStar_All.failwith _149_848))
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
(let _149_851 = (let _149_850 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _149_849 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _149_850 _149_849)))
in (try_umax_components u1 u2 _149_851))
end else begin
(let _149_852 = (extend_solution orig ((UNIV (((v1), (u))))::[]) wl)
in USolved (_149_852))
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

let _55_1471 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_906 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _149_906))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(

let probs = (

let _55_1478 = probs
in {attempting = tl; wl_deferred = _55_1478.wl_deferred; ctr = _55_1478.ctr; defer_ok = _55_1478.defer_ok; smt_ok = _55_1478.smt_ok; tcenv = _55_1478.tcenv})
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
| (None, _55_1493, _55_1495) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _55_1499 -> begin
(

let _55_1508 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _55_1505 -> (match (_55_1505) with
| (c, _55_1502, _55_1504) -> begin
(c < probs.ctr)
end))))
in (match (_55_1508) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _149_909 = (FStar_List.map (fun _55_1514 -> (match (_55_1514) with
| (_55_1511, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (_149_909))
end
| _55_1516 -> begin
(let _149_912 = (

let _55_1517 = probs
in (let _149_911 = (FStar_All.pipe_right attempt (FStar_List.map (fun _55_1524 -> (match (_55_1524) with
| (_55_1520, _55_1522, y) -> begin
y
end))))
in {attempting = _149_911; wl_deferred = rest; ctr = _55_1517.ctr; defer_ok = _55_1517.defer_ok; smt_ok = _55_1517.smt_ok; tcenv = _55_1517.tcenv}))
in (solve env _149_912))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _149_918 = (solve_prob orig None [] wl)
in (solve env _149_918))
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
| _55_1559 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t1 = (whnf env t1)
in (

let t2 = (whnf env t2)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _55_1567; FStar_Syntax_Syntax.pos = _55_1565; FStar_Syntax_Syntax.vars = _55_1563}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _55_1579; FStar_Syntax_Syntax.pos = _55_1577; FStar_Syntax_Syntax.vars = _55_1575}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (

let _55_1588 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _55_1603 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(

let _55_1608 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_934 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _149_934 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (

let _55_1613 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_938 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" _149_938))
end else begin
()
end
in (

let _55_1617 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1617) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let _55_1623 = (head_matches_delta env () t1 t2)
in (match (_55_1623) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (_55_1625) -> begin
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

let _55_1641 = (match (ts) with
| Some (t1, t2) -> begin
(let _149_944 = (FStar_Syntax_Subst.compress t1)
in (let _149_943 = (FStar_Syntax_Subst.compress t2)
in ((_149_944), (_149_943))))
end
| None -> begin
(let _149_946 = (FStar_Syntax_Subst.compress t1)
in (let _149_945 = (FStar_Syntax_Subst.compress t2)
in ((_149_946), (_149_945))))
end)
in (match (_55_1641) with
| (t1, t2) -> begin
(

let eq_prob = (fun t1 t2 -> (let _149_952 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _149_951 -> FStar_TypeChecker_Common.TProb (_149_951)) _149_952)))
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(let _149_959 = (let _149_958 = (let _149_955 = (let _149_954 = (let _149_953 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (_149_953)))
in FStar_Syntax_Syntax.Tm_refine (_149_954))
in (FStar_Syntax_Syntax.mk _149_955 None t1.FStar_Syntax_Syntax.pos))
in (let _149_957 = (let _149_956 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (_149_956)::[])
in ((_149_958), (_149_957))))
in Some (_149_959))
end
| (_55_1655, FStar_Syntax_Syntax.Tm_refine (x, _55_1658)) -> begin
(let _149_962 = (let _149_961 = (let _149_960 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (_149_960)::[])
in ((t1), (_149_961)))
in Some (_149_962))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_1664), _55_1668) -> begin
(let _149_965 = (let _149_964 = (let _149_963 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (_149_963)::[])
in ((t2), (_149_964)))
in Some (_149_965))
end
| _55_1671 -> begin
(

let _55_1675 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1675) with
| (head1, _55_1674) -> begin
(match ((let _149_966 = (FStar_Syntax_Util.un_uinst head1)
in _149_966.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _55_1681; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_unfoldable (i); FStar_Syntax_Syntax.fv_qual = _55_1677}) -> begin
(

let prev = if (i > (Prims.parse_int "1")) then begin
FStar_Syntax_Syntax.Delta_unfoldable ((i - (Prims.parse_int "1")))
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t1)
in (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t2)
in (disjoin t1 t2))))
end
| _55_1688 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, _55_1692) -> begin
(

let _55_1717 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _55_23 -> (match (_55_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(

let _55_1703 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1703) with
| (u', _55_1702) -> begin
(match ((let _149_968 = (whnf env u')
in _149_968.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1706) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _55_1710 -> begin
false
end)
end))
end
| _55_1712 -> begin
false
end)
end
| _55_1714 -> begin
false
end))))
in (match (_55_1717) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun _55_1721 tps -> (match (_55_1721) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(match ((let _149_973 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound _149_973))) with
| Some (bound, sub) -> begin
(make_lower_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end)
end
| _55_1734 -> begin
None
end)
end))
in (match ((let _149_975 = (let _149_974 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((_149_974), ([])))
in (make_lower_bound _149_975 lower_bounds))) with
| None -> begin
(

let _55_1736 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
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

let _55_1746 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(

let wl' = (

let _55_1743 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1743.wl_deferred; ctr = _55_1743.ctr; defer_ok = _55_1743.defer_ok; smt_ok = _55_1743.smt_ok; tcenv = _55_1743.tcenv})
in (let _149_976 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" _149_976)))
end else begin
()
end
in (match ((solve_t env eq_prob (

let _55_1748 = wl
in {attempting = sub_probs; wl_deferred = _55_1748.wl_deferred; ctr = _55_1748.ctr; defer_ok = _55_1748.defer_ok; smt_ok = _55_1748.smt_ok; tcenv = _55_1748.tcenv}))) with
| Success (_55_1751) -> begin
(

let wl = (

let _55_1753 = wl
in {attempting = rest; wl_deferred = _55_1753.wl_deferred; ctr = _55_1753.ctr; defer_ok = _55_1753.defer_ok; smt_ok = _55_1753.smt_ok; tcenv = _55_1753.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let _55_1759 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| _55_1762 -> begin
None
end)))
end))
end))
end
| _55_1764 -> begin
(FStar_All.failwith "Impossible: Not a rigid-flex")
end)))
end))))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (

let _55_1768 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_982 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _149_982))
end else begin
()
end
in (

let _55_1772 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1772) with
| (u, args) -> begin
(

let _55_1778 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (_55_1778) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(

let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (

let base_types_match = (fun t1 t2 -> (

let _55_1787 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1787) with
| (h1, args1) -> begin
(

let _55_1791 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_1791) with
| (h2, _55_1790) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = (Prims.parse_int "0")) then begin
Some ([])
end else begin
(let _149_994 = (let _149_993 = (let _149_992 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _149_991 -> FStar_TypeChecker_Common.TProb (_149_991)) _149_992))
in (_149_993)::[])
in Some (_149_994))
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
(let _149_998 = (let _149_997 = (let _149_996 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _149_995 -> FStar_TypeChecker_Common.TProb (_149_995)) _149_996))
in (_149_997)::[])
in Some (_149_998))
end
end else begin
None
end
end
| _55_1803 -> begin
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
in (let _149_1005 = (let _149_1004 = (let _149_1003 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _149_1003))
in ((_149_1004), (m)))
in Some (_149_1005))))))
end))
end
| (_55_1825, FStar_Syntax_Syntax.Tm_refine (y, _55_1828)) -> begin
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
| (FStar_Syntax_Syntax.Tm_refine (x, _55_1838), _55_1842) -> begin
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
| _55_1849 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, _55_1857) -> begin
(

let _55_1882 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _55_24 -> (match (_55_24) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(

let _55_1868 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1868) with
| (u', _55_1867) -> begin
(match ((let _149_1007 = (whnf env u')
in _149_1007.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1871) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _55_1875 -> begin
false
end)
end))
end
| _55_1877 -> begin
false
end)
end
| _55_1879 -> begin
false
end))))
in (match (_55_1882) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun _55_1886 tps -> (match (_55_1886) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(match ((let _149_1012 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _149_1012))) with
| Some (bound, sub) -> begin
(make_upper_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end)
end
| _55_1899 -> begin
None
end)
end))
in (match ((let _149_1014 = (let _149_1013 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((_149_1013), ([])))
in (make_upper_bound _149_1014 upper_bounds))) with
| None -> begin
(

let _55_1901 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
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

let _55_1911 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(

let wl' = (

let _55_1908 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1908.wl_deferred; ctr = _55_1908.ctr; defer_ok = _55_1908.defer_ok; smt_ok = _55_1908.smt_ok; tcenv = _55_1908.tcenv})
in (let _149_1015 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _149_1015)))
end else begin
()
end
in (match ((solve_t env eq_prob (

let _55_1913 = wl
in {attempting = sub_probs; wl_deferred = _55_1913.wl_deferred; ctr = _55_1913.ctr; defer_ok = _55_1913.defer_ok; smt_ok = _55_1913.smt_ok; tcenv = _55_1913.tcenv}))) with
| Success (_55_1916) -> begin
(

let wl = (

let _55_1918 = wl
in {attempting = rest; wl_deferred = _55_1918.wl_deferred; ctr = _55_1918.ctr; defer_ok = _55_1918.defer_ok; smt_ok = _55_1918.smt_ok; tcenv = _55_1918.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let _55_1924 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _55_1927 -> begin
None
end)))
end))
end))
end
| _55_1929 -> begin
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

let _55_1946 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1043 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _149_1043))
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

let _55_1960 = hd1
in (let _149_1044 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1960.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1960.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_1044}))
in (

let hd2 = (

let _55_1963 = hd2
in (let _149_1045 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1963.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1963.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_1045}))
in (

let prob = (let _149_1048 = (let _149_1047 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _149_1047 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _149_1046 -> FStar_TypeChecker_Common.TProb (_149_1046)) _149_1048))
in (

let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (

let subst = (let _149_1049 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd1))))::_149_1049)
in (

let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux ((((hd1), (imp)))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi = (let _149_1051 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _149_1050 = (FStar_Syntax_Util.close_forall ((((hd1), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj _149_1051 _149_1050)))
in (

let _55_1975 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1053 = (FStar_Syntax_Print.term_to_string phi)
in (let _149_1052 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _149_1053 _149_1052)))
end else begin
()
end
in FStar_Util.Inl ((((prob)::sub_probs), (phi)))))
end
| fail -> begin
fail
end)))))))
end
| _55_1979 -> begin
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
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _149_1057 = (compress_tprob wl problem)
in (solve_t' env _149_1057 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (

let _55_2007 = (head_matches_delta env wl t1 t2)
in (match (_55_2007) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (_55_2009), _55_2012) -> begin
(

let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _55_2025 -> begin
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
in (let _149_1086 = (let _149_1085 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _149_1085 t2))
in (FStar_Syntax_Util.mk_forall x _149_1086)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _149_1087 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _149_1087)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_55_2035, Some (t1, t2)) -> begin
(solve_t env (

let _55_2041 = problem
in {FStar_TypeChecker_Common.pid = _55_2041.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_2041.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_2041.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2041.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2041.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2041.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2041.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2041.FStar_TypeChecker_Common.rank}) wl)
end
| (_55_2044, None) -> begin
(

let _55_2047 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1091 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1090 = (FStar_Syntax_Print.tag_of_term t1)
in (let _149_1089 = (FStar_Syntax_Print.term_to_string t2)
in (let _149_1088 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _149_1091 _149_1090 _149_1089 _149_1088)))))
end else begin
()
end
in (

let _55_2051 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_2051) with
| (head1, args1) -> begin
(

let _55_2054 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_2054) with
| (head2, args2) -> begin
(

let nargs = (FStar_List.length args1)
in if (nargs <> (FStar_List.length args2)) then begin
(let _149_1096 = (let _149_1095 = (FStar_Syntax_Print.term_to_string head1)
in (let _149_1094 = (args_to_string args1)
in (let _149_1093 = (FStar_Syntax_Print.term_to_string head2)
in (let _149_1092 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _149_1095 _149_1094 _149_1093 _149_1092)))))
in (giveup env _149_1096 orig))
end else begin
if ((nargs = (Prims.parse_int "0")) || (eq_args args1 args2)) then begin
(match ((solve_maybe_uinsts env orig head1 head2 wl)) with
| USolved (wl) -> begin
(let _149_1097 = (solve_prob orig None [] wl)
in (solve env _149_1097))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(

let _55_2064 = (base_and_refinement env wl t1)
in (match (_55_2064) with
| (base1, refinement1) -> begin
(

let _55_2067 = (base_and_refinement env wl t2)
in (match (_55_2067) with
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

let subprobs = (FStar_List.map2 (fun _55_2080 _55_2084 -> (match (((_55_2080), (_55_2084))) with
| ((a, _55_2079), (a', _55_2083)) -> begin
(let _149_1101 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _149_1100 -> FStar_TypeChecker_Common.TProb (_149_1100)) _149_1101))
end)) args1 args2)
in (

let formula = (let _149_1103 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _149_1103))
in (

let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _55_2090 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env (

let _55_2093 = problem
in {FStar_TypeChecker_Common.pid = _55_2093.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _55_2093.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _55_2093.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2093.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2093.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2093.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2093.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2093.FStar_TypeChecker_Common.rank}) wl)))
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

let _55_2112 = p
in (match (_55_2112) with
| (((u, k), xs, c), ps, (h, _55_2109, qs)) -> begin
(

let xs = (sn_binders env xs)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _55_2118 = (imitation_sub_probs orig env xs ps qs)
in (match (_55_2118) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (let _149_1118 = (h gs_xs)
in (let _149_1117 = (let _149_1116 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _149_1114 -> FStar_Util.Inl (_149_1114)))
in (FStar_All.pipe_right _149_1116 (fun _149_1115 -> Some (_149_1115))))
in (FStar_Syntax_Util.abs xs _149_1118 _149_1117)))
in (

let _55_2120 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1125 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _149_1124 = (FStar_Syntax_Print.comp_to_string c)
in (let _149_1123 = (FStar_Syntax_Print.term_to_string im)
in (let _149_1122 = (FStar_Syntax_Print.tag_of_term im)
in (let _149_1121 = (let _149_1119 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _149_1119 (FStar_String.concat ", ")))
in (let _149_1120 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" _149_1125 _149_1124 _149_1123 _149_1122 _149_1121 _149_1120)))))))
end else begin
()
end
in (

let wl = (solve_prob orig (Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (

let imitate' = (fun orig env wl _55_25 -> (match (_55_25) with
| None -> begin
(giveup env "unable to compute subterms" orig)
end
| Some (p) -> begin
(imitate orig env wl p)
end))
in (

let project = (fun orig env wl i p -> (

let _55_2146 = p
in (match (_55_2146) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _55_2151 = (FStar_List.nth ps i)
in (match (_55_2151) with
| (pi, _55_2150) -> begin
(

let _55_2155 = (FStar_List.nth xs i)
in (match (_55_2155) with
| (xi, _55_2154) -> begin
(

let rec gs = (fun k -> (

let _55_2160 = (FStar_Syntax_Util.arrow_formals k)
in (match (_55_2160) with
| (bs, k) -> begin
(

let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
(([]), ([]))
end
| ((a, _55_2168))::tl -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (

let _55_2174 = (new_uvar r xs k_a)
in (match (_55_2174) with
| (gi_xs, gi) -> begin
(

let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (

let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst = (FStar_Syntax_Syntax.NT (((a), (gi_xs))))::subst
in (

let _55_2180 = (aux subst tl)
in (match (_55_2180) with
| (gi_xs', gi_ps') -> begin
(let _149_1155 = (let _149_1152 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_149_1152)::gi_xs')
in (let _149_1154 = (let _149_1153 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_149_1153)::gi_ps')
in ((_149_1155), (_149_1154))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _149_1156 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _149_1156)) then begin
None
end else begin
(

let _55_2184 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_55_2184) with
| (g_xs, _55_2183) -> begin
(

let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (let _149_1161 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (let _149_1160 = (let _149_1159 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _149_1157 -> FStar_Util.Inl (_149_1157)))
in (FStar_All.pipe_right _149_1159 (fun _149_1158 -> Some (_149_1158))))
in (FStar_Syntax_Util.abs xs _149_1161 _149_1160)))
in (

let sub = (let _149_1167 = (let _149_1166 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _149_1165 = (let _149_1164 = (FStar_List.map (fun _55_2192 -> (match (_55_2192) with
| (_55_2188, _55_2190, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _149_1164))
in (mk_problem (p_scope orig) orig _149_1166 (p_rel orig) _149_1165 None "projection")))
in (FStar_All.pipe_left (fun _149_1162 -> FStar_TypeChecker_Common.TProb (_149_1162)) _149_1167))
in (

let _55_2194 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1169 = (FStar_Syntax_Print.term_to_string proj)
in (let _149_1168 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _149_1169 _149_1168)))
end else begin
()
end
in (

let wl = (let _149_1171 = (let _149_1170 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_149_1170))
in (solve_prob orig _149_1171 ((TERM (((u), (proj))))::[]) wl))
in (let _149_1173 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _149_1172 -> Some (_149_1172)) _149_1173)))))))
end))
end)
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl -> (

let _55_2209 = lhs
in (match (_55_2209) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let _55_2214 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (_55_2214) with
| (xs, c) -> begin
if ((FStar_List.length xs) = (FStar_List.length ps)) then begin
(let _149_1197 = (let _149_1196 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (_149_1196)))
in Some (_149_1197))
end else begin
(

let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (match ((let _149_1203 = (let _149_1202 = (FStar_Syntax_Subst.compress k)
in _149_1202.FStar_Syntax_Syntax.n)
in ((_149_1203), (args)))) with
| (_55_2220, []) -> begin
(let _149_1205 = (let _149_1204 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_149_1204)))
in Some (_149_1205))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(

let _55_2237 = (FStar_Syntax_Util.head_and_args k)
in (match (_55_2237) with
| (uv, uv_args) -> begin
(match ((let _149_1206 = (FStar_Syntax_Subst.compress uv)
in _149_1206.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, _55_2240) -> begin
(match ((pat_vars env [] uv_args)) with
| None -> begin
None
end
| Some (scope) -> begin
(

let xs = (FStar_All.pipe_right args (FStar_List.map (fun _55_2246 -> (let _149_1212 = (let _149_1211 = (let _149_1210 = (let _149_1209 = (let _149_1208 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_1208 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _149_1209))
in (Prims.fst _149_1210))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) _149_1211))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _149_1212)))))
in (

let c = (let _149_1216 = (let _149_1215 = (let _149_1214 = (let _149_1213 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_1213 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _149_1214))
in (Prims.fst _149_1215))
in (FStar_Syntax_Syntax.mk_Total _149_1216))
in (

let k' = (FStar_Syntax_Util.arrow xs c)
in (

let uv_sol = (let _149_1222 = (let _149_1221 = (let _149_1220 = (let _149_1219 = (let _149_1218 = (let _149_1217 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_1217 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total _149_1218))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_1219))
in FStar_Util.Inl (_149_1220))
in Some (_149_1221))
in (FStar_Syntax_Util.abs scope k' _149_1222))
in (

let _55_2252 = (FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)))
in Some (((xs), (c))))))))
end)
end
| _55_2255 -> begin
None
end)
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), _55_2261) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs)
in if (n_xs = n_args) then begin
(let _149_1224 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right _149_1224 (fun _149_1223 -> Some (_149_1223))))
end else begin
if (n_xs < n_args) then begin
(

let _55_2267 = (FStar_Util.first_N n_xs args)
in (match (_55_2267) with
| (args, rest) -> begin
(

let _55_2270 = (FStar_Syntax_Subst.open_comp xs c)
in (match (_55_2270) with
| (xs, c) -> begin
(let _149_1226 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt _149_1226 (fun _55_2273 -> (match (_55_2273) with
| (xs', c) -> begin
Some ((((FStar_List.append xs xs')), (c)))
end))))
end))
end))
end else begin
(

let _55_2276 = (FStar_Util.first_N n_args xs)
in (match (_55_2276) with
| (xs, rest) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) None k.FStar_Syntax_Syntax.pos)
in (let _149_1229 = (let _149_1227 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs _149_1227))
in (FStar_All.pipe_right _149_1229 (fun _149_1228 -> Some (_149_1228)))))
end))
end
end))
end
| _55_2279 -> begin
(let _149_1233 = (let _149_1232 = (FStar_Syntax_Print.uvar_to_string uv)
in (let _149_1231 = (FStar_Syntax_Print.term_to_string k)
in (let _149_1230 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" _149_1232 _149_1231 _149_1230))))
in (FStar_All.failwith _149_1233))
end))
in (let _149_1271 = (elim k_uv ps)
in (FStar_Util.bind_opt _149_1271 (fun _55_2282 -> (match (_55_2282) with
| (xs, c) -> begin
(let _149_1270 = (let _149_1269 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (_149_1269)))
in Some (_149_1270))
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
| Failed (_55_2290) -> begin
(

let _55_2292 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + (Prims.parse_int "1"))))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(

let _55_2300 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + (Prims.parse_int "1"))))
end
| Some (sol) -> begin
sol
end)
end))
end)
in (

let check_head = (fun fvs1 t2 -> (

let _55_2310 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_2310) with
| (hd, _55_2309) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _55_2321 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(

let _55_2323 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1282 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _149_1282))
end else begin
()
end
in false)
end)
end)
end)))
in (

let imitate_ok = (fun t2 -> (

let fvs_hd = (let _149_1286 = (let _149_1285 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _149_1285 Prims.fst))
in (FStar_All.pipe_right _149_1286 FStar_Syntax_Free.names))
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

let _55_2336 = (occurs_check env wl ((uv), (k_uv)) t2)
in (match (_55_2336) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _149_1288 = (let _149_1287 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _149_1287))
in (giveup_or_defer orig _149_1288))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t2)) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _149_1289 = (subterms args_lhs)
in (imitate' orig env wl _149_1289))
end else begin
(

let _55_2337 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1292 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1291 = (names_to_string fvs1)
in (let _149_1290 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _149_1292 _149_1291 _149_1290))))
end else begin
()
end
in (

let sol = (match (vars) with
| [] -> begin
t2
end
| _55_2341 -> begin
(let _149_1293 = (sn_binders env vars)
in (u_abs k_uv _149_1293 t2))
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

let _55_2344 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1296 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1295 = (names_to_string fvs1)
in (let _149_1294 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _149_1296 _149_1295 _149_1294))))
end else begin
()
end
in (let _149_1297 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _149_1297 (~- ((Prims.parse_int "1"))))))
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
if (let _149_1298 = (FStar_Syntax_Free.names t1)
in (check_head _149_1298 t2)) then begin
(

let im_ok = (imitate_ok t2)
in (

let _55_2349 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1299 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _149_1299 (if (im_ok < (Prims.parse_int "0")) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _149_1300 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _149_1300 im_ok))))
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

let force_quasi_pattern = (fun xs_opt _55_2361 -> (match (_55_2361) with
| (t, u, k, args) -> begin
(

let _55_2365 = (FStar_Syntax_Util.arrow_formals k)
in (match (_55_2365) with
| (all_formals, _55_2364) -> begin
(

let _55_2366 = ()
in (

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match (((formals), (args))) with
| ([], []) -> begin
(

let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _55_2379 -> (match (_55_2379) with
| (x, imp) -> begin
(let _149_1322 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_149_1322), (imp)))
end))))
in (

let pattern_vars = (FStar_List.rev pattern_vars)
in (

let kk = (

let _55_2385 = (FStar_Syntax_Util.type_u ())
in (match (_55_2385) with
| (t, _55_2384) -> begin
(let _149_1323 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _149_1323))
end))
in (

let _55_2389 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_55_2389) with
| (t', tm_u1) -> begin
(

let _55_2396 = (destruct_flex_t t')
in (match (_55_2396) with
| (_55_2391, u1, k1, _55_2395) -> begin
(

let sol = (let _149_1325 = (let _149_1324 = (u_abs k all_formals t')
in ((((u), (k))), (_149_1324)))
in TERM (_149_1325))
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _55_2415 -> (match (_55_2415) with
| (x, _55_2414) -> begin
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
(let _149_1327 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _149_1327 formals tl))
end)
end)
end)
end
| _55_2419 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _149_1328 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _149_1328 all_formals args))))
end))
end))
in (

let solve_both_pats = (fun wl _55_2426 _55_2431 r -> (match (((_55_2426), (_55_2431))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _149_1337 = (solve_prob orig None [] wl)
in (solve env _149_1337))
end else begin
(

let xs = (sn_binders env xs)
in (

let ys = (sn_binders env ys)
in (

let zs = (intersect_vars xs ys)
in (

let _55_2436 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1342 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _149_1341 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _149_1340 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (let _149_1339 = (FStar_Syntax_Print.term_to_string k1)
in (let _149_1338 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" _149_1342 _149_1341 _149_1340 _149_1339 _149_1338))))))
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
(let _149_1352 = (let _149_1351 = (FStar_Syntax_Print.term_to_string k)
in (let _149_1350 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _149_1349 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" _149_1351 _149_1350 _149_1349))))
in (FStar_All.failwith _149_1352))
end)))
in (

let _55_2478 = (

let _55_2446 = (let _149_1353 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals _149_1353))
in (match (_55_2446) with
| (bs, k1') -> begin
(

let _55_2449 = (let _149_1354 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals _149_1354))
in (match (_55_2449) with
| (cs, k2') -> begin
(

let k1'_xs = (let _149_1355 = (subst_of_list k1 bs args1)
in (FStar_Syntax_Subst.subst _149_1355 k1'))
in (

let k2'_ys = (let _149_1356 = (subst_of_list k2 cs args2)
in (FStar_Syntax_Subst.subst _149_1356 k2'))
in (

let sub_prob = (let _149_1358 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys None "flex-flex kinding")
in (FStar_All.pipe_left (fun _149_1357 -> FStar_TypeChecker_Common.TProb (_149_1357)) _149_1358))
in (match ((let _149_1362 = (let _149_1359 = (FStar_Syntax_Subst.compress k1')
in _149_1359.FStar_Syntax_Syntax.n)
in (let _149_1361 = (let _149_1360 = (FStar_Syntax_Subst.compress k2')
in _149_1360.FStar_Syntax_Syntax.n)
in ((_149_1362), (_149_1361))))) with
| (FStar_Syntax_Syntax.Tm_type (_55_2454), _55_2457) -> begin
((k1'), ((sub_prob)::[]))
end
| (_55_2460, FStar_Syntax_Syntax.Tm_type (_55_2462)) -> begin
((k2'), ((sub_prob)::[]))
end
| _55_2466 -> begin
(

let _55_2470 = (FStar_Syntax_Util.type_u ())
in (match (_55_2470) with
| (t, _55_2469) -> begin
(

let _55_2474 = (new_uvar r zs t)
in (match (_55_2474) with
| (k_zs, _55_2473) -> begin
(

let kprob = (let _149_1364 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k_zs None "flex-flex kinding")
in (FStar_All.pipe_left (fun _149_1363 -> FStar_TypeChecker_Common.TProb (_149_1363)) _149_1364))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end))))
end))
end))
in (match (_55_2478) with
| (k_u', sub_probs) -> begin
(

let _55_2482 = (let _149_1370 = (let _149_1365 = (new_uvar r zs k_u')
in (FStar_All.pipe_left Prims.fst _149_1365))
in (let _149_1369 = (let _149_1366 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs _149_1366))
in (let _149_1368 = (let _149_1367 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys _149_1367))
in ((_149_1370), (_149_1369), (_149_1368)))))
in (match (_55_2482) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs u_zs)
in (

let _55_2486 = (occurs_check env wl ((u1), (k1)) sub1)
in (match (_55_2486) with
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

let _55_2492 = (occurs_check env wl ((u2), (k2)) sub2)
in (match (_55_2492) with
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

let solve_one_pat = (fun _55_2500 _55_2505 -> (match (((_55_2500), (_55_2505))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(

let _55_2506 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1376 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1375 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _149_1376 _149_1375)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(

let sub_probs = (FStar_List.map2 (fun _55_2511 _55_2515 -> (match (((_55_2511), (_55_2515))) with
| ((a, _55_2510), (t2, _55_2514)) -> begin
(let _149_1381 = (let _149_1379 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _149_1379 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _149_1381 (fun _149_1380 -> FStar_TypeChecker_Common.TProb (_149_1380))))
end)) xs args2)
in (

let guard = (let _149_1383 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _149_1383))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(

let t2 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t2)
in (

let _55_2525 = (occurs_check env wl ((u1), (k1)) t2)
in (match (_55_2525) with
| (occurs_ok, _55_2524) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(

let sol = (let _149_1385 = (let _149_1384 = (u_abs k1 xs t2)
in ((((u1), (k1))), (_149_1384)))
in TERM (_149_1385))
in (

let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(

let _55_2536 = (force_quasi_pattern (Some (xs)) ((t2), (u2), (k2), (args2)))
in (match (_55_2536) with
| (sol, (_55_2531, u2, k2, ys)) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (

let _55_2538 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _149_1386 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _149_1386))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _55_2543 -> begin
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

let _55_2548 = lhs
in (match (_55_2548) with
| (t1, u1, k1, args1) -> begin
(

let _55_2553 = rhs
in (match (_55_2553) with
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
| _55_2571 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(

let _55_2575 = (force_quasi_pattern None ((t1), (u1), (k1), (args1)))
in (match (_55_2575) with
| (sol, _55_2574) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (

let _55_2577 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _149_1387 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _149_1387))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _55_2582 -> begin
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
(let _149_1388 = (solve_prob orig None [] wl)
in (solve env _149_1388))
end else begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _149_1389 = (solve_prob orig None [] wl)
in (solve env _149_1389))
end else begin
(

let _55_2586 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _149_1390 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _149_1390))
end else begin
()
end
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let match_num_binders = (fun _55_2591 _55_2594 -> (match (((_55_2591), (_55_2594))) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(

let curry = (fun n bs mk_cod -> (

let _55_2601 = (FStar_Util.first_N n bs)
in (match (_55_2601) with
| (bs, rest) -> begin
(let _149_1420 = (mk_cod rest)
in ((bs), (_149_1420)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _149_1424 = (let _149_1421 = (mk_cod1 [])
in ((bs1), (_149_1421)))
in (let _149_1423 = (let _149_1422 = (mk_cod2 [])
in ((bs2), (_149_1422)))
in ((_149_1424), (_149_1423))))
end else begin
if (l1 > l2) then begin
(let _149_1427 = (curry l2 bs1 mk_cod1)
in (let _149_1426 = (let _149_1425 = (mk_cod2 [])
in ((bs2), (_149_1425)))
in ((_149_1427), (_149_1426))))
end else begin
(let _149_1430 = (let _149_1428 = (mk_cod1 [])
in ((bs1), (_149_1428)))
in (let _149_1429 = (curry l1 bs2 mk_cod2)
in ((_149_1430), (_149_1429))))
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

let mk_c = (fun c _55_26 -> (match (_55_26) with
| [] -> begin
c
end
| bs -> begin
(let _149_1435 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _149_1435))
end))
in (

let _55_2644 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (_55_2644) with
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
in (let _149_1442 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _149_1441 -> FStar_TypeChecker_Common.CProb (_149_1441)) _149_1442)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l _55_27 -> (match (_55_27) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l)))) None t.FStar_Syntax_Syntax.pos)
end))
in (

let _55_2674 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (_55_2674) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _149_1457 = (let _149_1456 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _149_1455 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _149_1456 problem.FStar_TypeChecker_Common.relation _149_1455 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _149_1454 -> FStar_TypeChecker_Common.TProb (_149_1454)) _149_1457))))
end)))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_55_2693) -> begin
true
end
| _55_2696 -> begin
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
in (match ((let _149_1463 = (maybe_eta t1)
in (let _149_1462 = (maybe_eta t2)
in ((_149_1463), (_149_1462))))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(solve_t env (

let _55_2705 = problem
in {FStar_TypeChecker_Common.pid = _55_2705.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_2705.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_2705.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2705.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2705.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2705.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2705.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2705.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs))) | ((FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs))) -> begin
if ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ)) then begin
(let _149_1464 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig _149_1464 t_abs wl))
end else begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end
end
| _55_2716 -> begin
(FStar_All.failwith "Impossible: at least one side is an abstraction")
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_55_2718), FStar_Syntax_Syntax.Tm_refine (_55_2721)) -> begin
(

let _55_2726 = (as_refinement env wl t1)
in (match (_55_2726) with
| (x1, phi1) -> begin
(

let _55_2729 = (as_refinement env wl t2)
in (match (_55_2729) with
| (x2, phi2) -> begin
(

let base_prob = (let _149_1466 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _149_1465 -> FStar_TypeChecker_Common.TProb (_149_1465)) _149_1466))
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

let mk_imp = (fun imp phi1 phi2 -> (let _149_1483 = (imp phi1 phi2)
in (FStar_All.pipe_right _149_1483 (guard_on_element problem x1))))
in (

let fallback = (fun _55_2741 -> (match (()) with
| () -> begin
(

let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (

let guard = (let _149_1486 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _149_1486 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(

let ref_prob = (let _149_1490 = (let _149_1489 = (let _149_1488 = (FStar_Syntax_Syntax.mk_binder x1)
in (_149_1488)::(p_scope orig))
in (mk_problem _149_1489 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _149_1487 -> FStar_TypeChecker_Common.TProb (_149_1487)) _149_1490))
in (match ((solve env (

let _55_2746 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _55_2746.ctr; defer_ok = false; smt_ok = _55_2746.smt_ok; tcenv = _55_2746.tcenv}))) with
| Failed (_55_2749) -> begin
(fallback ())
end
| Success (_55_2752) -> begin
(

let guard = (let _149_1493 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _149_1492 = (let _149_1491 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _149_1491 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _149_1493 _149_1492)))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (

let wl = (

let _55_2756 = wl
in {attempting = _55_2756.attempting; wl_deferred = _55_2756.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = _55_2756.defer_ok; smt_ok = _55_2756.smt_ok; tcenv = _55_2756.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _149_1495 = (destruct_flex_t t1)
in (let _149_1494 = (destruct_flex_t t2)
in (flex_flex orig _149_1495 _149_1494)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _149_1496 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig _149_1496 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_arrow (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
(solve_t' env (

let _55_2927 = problem
in {FStar_TypeChecker_Common.pid = _55_2927.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2927.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _55_2927.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2927.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2927.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2927.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2927.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2927.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2927.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in if (let _149_1497 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _149_1497)) then begin
(let _149_1500 = (FStar_All.pipe_left (fun _149_1498 -> FStar_TypeChecker_Common.TProb (_149_1498)) (

let _55_2953 = problem
in {FStar_TypeChecker_Common.pid = _55_2953.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2953.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2953.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2953.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2953.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2953.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2953.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2953.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2953.FStar_TypeChecker_Common.rank}))
in (let _149_1499 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false _149_1500 _149_1499 t2 wl)))
end else begin
(

let _55_2957 = (base_and_refinement env wl t2)
in (match (_55_2957) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _149_1503 = (FStar_All.pipe_left (fun _149_1501 -> FStar_TypeChecker_Common.TProb (_149_1501)) (

let _55_2959 = problem
in {FStar_TypeChecker_Common.pid = _55_2959.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2959.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2959.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2959.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2959.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2959.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2959.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2959.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2959.FStar_TypeChecker_Common.rank}))
in (let _149_1502 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false _149_1503 _149_1502 t_base wl)))
end
| Some (y, phi) -> begin
(

let y' = (

let _55_2965 = y
in {FStar_Syntax_Syntax.ppname = _55_2965.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_2965.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element problem y' phi)
in (

let base_prob = (let _149_1505 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _149_1504 -> FStar_TypeChecker_Common.TProb (_149_1504)) _149_1505))
in (

let guard = (let _149_1506 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _149_1506 impl))
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

let _55_2998 = (base_and_refinement env wl t1)
in (match (_55_2998) with
| (t_base, _55_2997) -> begin
(solve_t env (

let _55_2999 = problem
in {FStar_TypeChecker_Common.pid = _55_2999.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _55_2999.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2999.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2999.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2999.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2999.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2999.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2999.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_55_3002), _55_3005) -> begin
(

let t2 = (let _149_1507 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _149_1507))
in (solve_t env (

let _55_3008 = problem
in {FStar_TypeChecker_Common.pid = _55_3008.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_3008.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_3008.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_3008.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3008.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3008.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3008.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3008.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3008.FStar_TypeChecker_Common.rank}) wl))
end
| (_55_3011, FStar_Syntax_Syntax.Tm_refine (_55_3013)) -> begin
(

let t1 = (let _149_1508 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _149_1508))
in (solve_t env (

let _55_3017 = problem
in {FStar_TypeChecker_Common.pid = _55_3017.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_3017.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_3017.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_3017.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3017.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3017.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3017.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3017.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3017.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(

let head1 = (let _149_1509 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _149_1509 Prims.fst))
in (

let head2 = (let _149_1510 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _149_1510 Prims.fst))
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
(let _149_1512 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _149_1511 -> Some (_149_1511)) _149_1512))
end
in (let _149_1513 = (solve_prob orig guard [] wl)
in (solve env _149_1513)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _55_3098, _55_3100), _55_3104) -> begin
(solve_t' env (

let _55_3106 = problem
in {FStar_TypeChecker_Common.pid = _55_3106.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_3106.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_3106.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_3106.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3106.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3106.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3106.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3106.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3106.FStar_TypeChecker_Common.rank}) wl)
end
| (_55_3109, FStar_Syntax_Syntax.Tm_ascribed (t2, _55_3112, _55_3114)) -> begin
(solve_t' env (

let _55_3118 = problem
in {FStar_TypeChecker_Common.pid = _55_3118.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_3118.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_3118.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_3118.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3118.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3118.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3118.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3118.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3118.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _149_1516 = (let _149_1515 = (FStar_Syntax_Print.tag_of_term t1)
in (let _149_1514 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _149_1515 _149_1514)))
in (FStar_All.failwith _149_1516))
end
| _55_3157 -> begin
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

let _55_3174 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (

let sub_probs = (FStar_List.map2 (fun _55_3179 _55_3183 -> (match (((_55_3179), (_55_3183))) with
| ((a1, _55_3178), (a2, _55_3182)) -> begin
(let _149_1531 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _149_1530 -> FStar_TypeChecker_Common.TProb (_149_1530)) _149_1531))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (let _149_1533 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _149_1533))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in (

let solve_sub = (fun c1 edge c2 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(

let wp = (match (c1.FStar_Syntax_Syntax.effect_args) with
| ((wp1, _55_3195))::[] -> begin
wp1
end
| _55_3199 -> begin
(let _149_1541 = (let _149_1540 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _149_1540))
in (FStar_All.failwith _149_1541))
end)
in (

let c1 = (let _149_1544 = (let _149_1543 = (let _149_1542 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _149_1542))
in (_149_1543)::[])
in {FStar_Syntax_Syntax.comp_univs = c1.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _149_1544; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2)))
end else begin
(

let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _55_28 -> (match (_55_28) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _55_3207 -> begin
false
end))))
in (

let _55_3228 = (match (((c1.FStar_Syntax_Syntax.effect_args), (c2.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, _55_3213))::_55_3210, ((wp2, _55_3220))::_55_3217) -> begin
((wp1), (wp2))
end
| _55_3225 -> begin
(let _149_1548 = (let _149_1547 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _149_1546 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _149_1547 _149_1546)))
in (FStar_All.failwith _149_1548))
end)
in (match (_55_3228) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _149_1549 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _149_1549 wl))
end else begin
(

let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let g = if is_null_wp_2 then begin
(

let _55_3230 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _149_1559 = (let _149_1558 = (let _149_1557 = (let _149_1551 = (let _149_1550 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_149_1550)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _149_1551 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _149_1556 = (let _149_1555 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _149_1554 = (let _149_1553 = (let _149_1552 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_1552))
in (_149_1553)::[])
in (_149_1555)::_149_1554))
in ((_149_1557), (_149_1556))))
in FStar_Syntax_Syntax.Tm_app (_149_1558))
in (FStar_Syntax_Syntax.mk _149_1559 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(let _149_1571 = (let _149_1570 = (let _149_1569 = (let _149_1561 = (let _149_1560 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_149_1560)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _149_1561 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (let _149_1568 = (let _149_1567 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _149_1566 = (let _149_1565 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _149_1564 = (let _149_1563 = (let _149_1562 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_1562))
in (_149_1563)::[])
in (_149_1565)::_149_1564))
in (_149_1567)::_149_1566))
in ((_149_1569), (_149_1568))))
in FStar_Syntax_Syntax.Tm_app (_149_1570))
in (FStar_Syntax_Syntax.mk _149_1571 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r))
end
in (

let base_prob = (let _149_1573 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _149_1572 -> FStar_TypeChecker_Common.TProb (_149_1572)) _149_1573))
in (

let wl = (let _149_1577 = (let _149_1576 = (let _149_1575 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _149_1575 g))
in (FStar_All.pipe_left (fun _149_1574 -> Some (_149_1574)) _149_1576))
in (solve_prob orig _149_1577 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end
end)))
end))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _149_1578 = (solve_prob orig None [] wl)
in (solve env _149_1578))
end else begin
(

let _55_3235 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1580 = (FStar_Syntax_Print.comp_to_string c1)
in (let _149_1579 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _149_1580 (rel_to_string problem.FStar_TypeChecker_Common.relation) _149_1579)))
end else begin
()
end
in (

let _55_3239 = (let _149_1582 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (let _149_1581 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((_149_1582), (_149_1581))))
in (match (_55_3239) with
| (c1, c2) -> begin
(match (((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, _55_3242), FStar_Syntax_Syntax.Total (t2, _55_3247)) when (FStar_Syntax_Util.non_informative t2) -> begin
(let _149_1583 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _149_1583 wl))
end
| (FStar_Syntax_Syntax.GTotal (_55_3252), FStar_Syntax_Syntax.Total (_55_3255)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.Total (t2, _))) | ((FStar_Syntax_Syntax.GTotal (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) | ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) -> begin
(let _149_1584 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _149_1584 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _149_1587 = (

let _55_3301 = problem
in (let _149_1586 = (let _149_1585 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _149_1585))
in {FStar_TypeChecker_Common.pid = _55_3301.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _149_1586; FStar_TypeChecker_Common.relation = _55_3301.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_3301.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_3301.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3301.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3301.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3301.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3301.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3301.FStar_TypeChecker_Common.rank}))
in (solve_c env _149_1587 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _149_1590 = (

let _55_3317 = problem
in (let _149_1589 = (let _149_1588 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c2)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _149_1588))
in {FStar_TypeChecker_Common.pid = _55_3317.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_3317.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_3317.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _149_1589; FStar_TypeChecker_Common.element = _55_3317.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3317.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3317.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3317.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3317.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3317.FStar_TypeChecker_Common.rank}))
in (solve_c env _149_1590 wl))
end
| (FStar_Syntax_Syntax.Comp (_55_3320), FStar_Syntax_Syntax.Comp (_55_3323)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _149_1591 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _149_1591 wl))
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

let _55_3330 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
if (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (let _149_1592 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative _149_1592))) then begin
(

let edge = {FStar_TypeChecker_Env.msource = c1.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c2.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = (fun r t -> t)}
in (solve_sub c1 edge c2))
end else begin
(let _149_1597 = (let _149_1596 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _149_1595 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _149_1596 _149_1595)))
in (giveup env _149_1597 orig))
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


let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _149_1601 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _55_3350 -> (match (_55_3350) with
| (_55_3340, _55_3342, u, _55_3345, _55_3347, _55_3349) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _149_1601 (FStar_String.concat ", "))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred))) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _55_3357 -> begin
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

let carry = (let _149_1607 = (FStar_List.map (fun _55_3365 -> (match (_55_3365) with
| (_55_3363, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _149_1607 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3374; FStar_TypeChecker_Env.implicits = _55_3372} -> begin
true
end
| _55_3379 -> begin
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
| _55_3397 -> begin
(FStar_All.failwith "impossible")
end)
in (let _149_1628 = (

let _55_3399 = g
in (let _149_1627 = (let _149_1626 = (let _149_1625 = (let _149_1619 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_1619)::[])
in (let _149_1624 = (let _149_1623 = (let _149_1622 = (let _149_1620 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _149_1620 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _149_1622 (fun _149_1621 -> FStar_Util.Inl (_149_1621))))
in Some (_149_1623))
in (FStar_Syntax_Util.abs _149_1625 f _149_1624)))
in (FStar_All.pipe_left (fun _149_1618 -> FStar_TypeChecker_Common.NonTrivial (_149_1618)) _149_1626))
in {FStar_TypeChecker_Env.guard_f = _149_1627; FStar_TypeChecker_Env.deferred = _55_3399.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3399.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3399.FStar_TypeChecker_Env.implicits}))
in Some (_149_1628)))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _55_3406 = g
in (let _149_1639 = (let _149_1638 = (let _149_1637 = (let _149_1636 = (let _149_1635 = (let _149_1634 = (FStar_Syntax_Syntax.as_arg e)
in (_149_1634)::[])
in ((f), (_149_1635)))
in FStar_Syntax_Syntax.Tm_app (_149_1636))
in (FStar_Syntax_Syntax.mk _149_1637 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _149_1633 -> FStar_TypeChecker_Common.NonTrivial (_149_1633)) _149_1638))
in {FStar_TypeChecker_Env.guard_f = _149_1639; FStar_TypeChecker_Env.deferred = _55_3406.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3406.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3406.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_55_3411) -> begin
(FStar_All.failwith "impossible")
end))


let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _149_1646 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_149_1646))
end))


let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _55_3429 -> begin
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


let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _149_1669 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _149_1669; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _55_3456 = g
in (let _149_1684 = (let _149_1683 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _149_1683 (fun _149_1682 -> FStar_TypeChecker_Common.NonTrivial (_149_1682))))
in {FStar_TypeChecker_Env.guard_f = _149_1684; FStar_TypeChecker_Env.deferred = _55_3456.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3456.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3456.FStar_TypeChecker_Env.implicits}))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _149_1692 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _149_1691 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _149_1692 (rel_to_string rel) _149_1691)))
end else begin
"TOP"
end
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (let _149_1703 = (let _149_1702 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _149_1701 -> Some (_149_1701)) _149_1702))
in (FStar_Syntax_Syntax.new_bv _149_1703 t1))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (let _149_1707 = (let _149_1705 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _149_1704 -> Some (_149_1704)) _149_1705))
in (let _149_1706 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _149_1707 _149_1706)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (

let probs = if (FStar_Options.eager_inference ()) then begin
(

let _55_3476 = probs
in {attempting = _55_3476.attempting; wl_deferred = _55_3476.wl_deferred; ctr = _55_3476.ctr; defer_ok = false; smt_ok = _55_3476.smt_ok; tcenv = _55_3476.tcenv})
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

let _55_3483 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(

let _55_3489 = (FStar_Unionfind.rollback tx)
in (

let _55_3491 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _149_1719 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _149_1719))
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

let _55_3498 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _149_1724 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _149_1724))
end else begin
()
end
in (

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (

let _55_3501 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _149_1725 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _149_1725))
end else begin
()
end
in (

let f = (match ((let _149_1726 = (FStar_Syntax_Util.unmeta f)
in _149_1726.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _55_3506 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (

let _55_3508 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _55_3508.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3508.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3508.FStar_TypeChecker_Env.implicits})))))
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _149_1738 = (let _149_1737 = (let _149_1736 = (let _149_1735 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _149_1735 (fun _149_1734 -> FStar_TypeChecker_Common.NonTrivial (_149_1734))))
in {FStar_TypeChecker_Env.guard_f = _149_1736; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _149_1737))
in (FStar_All.pipe_left (fun _149_1733 -> Some (_149_1733)) _149_1738))
end))


let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (

let _55_3519 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1746 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1745 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _149_1746 _149_1745)))
end else begin
()
end
in (

let prob = (let _149_1749 = (let _149_1748 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _149_1748))
in (FStar_All.pipe_left (fun _149_1747 -> FStar_TypeChecker_Common.TProb (_149_1747)) _149_1749))
in (

let g = (let _149_1751 = (solve_and_commit env (singleton env prob) (fun _55_3522 -> None))
in (FStar_All.pipe_left (with_guard env prob) _149_1751))
in g))))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _149_1761 = (let _149_1760 = (let _149_1759 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _149_1758 = (FStar_TypeChecker_Env.get_range env)
in ((_149_1759), (_149_1758))))
in FStar_Syntax_Syntax.Error (_149_1760))
in (Prims.raise _149_1761))
end
| Some (g) -> begin
(

let _55_3531 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1764 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1763 = (FStar_Syntax_Print.term_to_string t2)
in (let _149_1762 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _149_1764 _149_1763 _149_1762))))
end else begin
()
end
in g)
end))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 smt_ok -> (

let _55_3537 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1774 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _149_1773 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _149_1774 _149_1773)))
end else begin
()
end
in (

let _55_3542 = (

let rel = FStar_TypeChecker_Common.SUB
in (new_t_prob env t1 rel t2))
in (match (_55_3542) with
| (prob, x) -> begin
(

let g = (let _149_1776 = (solve_and_commit env (singleton' env prob smt_ok) (fun _55_3543 -> None))
in (FStar_All.pipe_left (with_guard env prob) _149_1776))
in (

let _55_3546 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _149_1780 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _149_1779 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _149_1778 = (let _149_1777 = (FStar_Util.must g)
in (guard_to_string env _149_1777))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _149_1780 _149_1779 _149_1778))))
end else begin
()
end
in (abstract_guard x g)))
end))))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env t1 t2 -> (let _149_1794 = (FStar_TypeChecker_Env.get_range env)
in (let _149_1793 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (FStar_TypeChecker_Errors.report _149_1794 _149_1793))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (

let _55_3557 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1802 = (FStar_Syntax_Print.comp_to_string c1)
in (let _149_1801 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _149_1802 _149_1801)))
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

let prob = (let _149_1805 = (let _149_1804 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _149_1804 "sub_comp"))
in (FStar_All.pipe_left (fun _149_1803 -> FStar_TypeChecker_Common.CProb (_149_1803)) _149_1805))
in (let _149_1807 = (solve_and_commit env (singleton env prob) (fun _55_3561 -> None))
in (FStar_All.pipe_left (with_guard env prob) _149_1807))))))


let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (

let fail = (fun msg u1 u2 -> (

let _55_3570 = (FStar_Unionfind.rollback tx)
in (

let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _149_1825 = (let _149_1824 = (let _149_1823 = (let _149_1821 = (FStar_Syntax_Print.univ_to_string u1)
in (let _149_1820 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _149_1821 _149_1820 msg)))
in (let _149_1822 = (FStar_TypeChecker_Env.get_range env)
in ((_149_1823), (_149_1822))))
in FStar_Syntax_Syntax.Error (_149_1824))
in (Prims.raise _149_1825)))))
in (

let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
(((uv), ((u1)::[])))::[]
end
| (hd)::tl -> begin
(

let _55_3586 = hd
in (match (_55_3586) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
(((uv'), ((u1)::lower_bounds)))::tl
end else begin
(let _149_1832 = (insert uv u1 tl)
in (hd)::_149_1832)
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
(let _149_1837 = (insert uv u1 out)
in (group_by _149_1837 rest))
end)
end
| _55_3601 -> begin
None
end))
end))
in (

let ad_hoc_fallback = (fun _55_3603 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _55_3606 -> begin
(

let wl = (

let _55_3607 = (empty_worklist env)
in {attempting = _55_3607.attempting; wl_deferred = _55_3607.wl_deferred; ctr = _55_3607.ctr; defer_ok = true; smt_ok = _55_3607.smt_ok; tcenv = _55_3607.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun _55_3612 -> (match (_55_3612) with
| (u1, u2) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _55_3617 -> begin
(match ((solve_universe_eq (~- ((Prims.parse_int "1"))) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(

let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _55_3627 -> begin
(u1)::[]
end)
in (

let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _55_3632 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _55_29 -> (match (_55_29) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(

let _55_3639 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_3639) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (

let _55_3643 = (FStar_Syntax_Util.univ_kernel u')
in (match (_55_3643) with
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
| USolved (_55_3645) -> begin
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

let _55_3649 = (empty_worklist env)
in {attempting = _55_3649.attempting; wl_deferred = _55_3649.wl_deferred; ctr = _55_3649.ctr; defer_ok = false; smt_ok = _55_3649.smt_ok; tcenv = _55_3649.tcenv})
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
| _55_3664 -> begin
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

let _55_3669 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail = (fun _55_3676 -> (match (_55_3676) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (

let _55_3679 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_1858 = (wl_to_string wl)
in (let _149_1857 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _149_1858 _149_1857)))
end else begin
()
end
in (

let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(

let _55_3683 = g
in {FStar_TypeChecker_Env.guard_f = _55_3683.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3683.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3683.FStar_TypeChecker_Env.implicits})
end
| _55_3686 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (

let _55_3688 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (

let _55_3690 = g
in {FStar_TypeChecker_Env.guard_f = _55_3690.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3690.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _55_3690.FStar_TypeChecker_Env.implicits})))))))


let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (

let g = (solve_deferred_constraints env g)
in (

let _55_3707 = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(

let _55_3699 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Norm"))) then begin
(let _149_1875 = (FStar_TypeChecker_Env.get_range env)
in (let _149_1874 = (let _149_1873 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" _149_1873))
in (FStar_TypeChecker_Errors.diag _149_1875 _149_1874)))
end else begin
()
end
in (

let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(

let _55_3705 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1878 = (FStar_TypeChecker_Env.get_range env)
in (let _149_1877 = (let _149_1876 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _149_1876))
in (FStar_TypeChecker_Errors.diag _149_1878 _149_1877)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc))
end)))
end)
end
in (

let _55_3709 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3709.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3709.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3709.FStar_TypeChecker_Env.implicits}))))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _55_3718 -> begin
false
end))
in (

let rec until_fixpoint = (fun _55_3722 implicits -> (match (_55_3722) with
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

let _55_3735 = hd
in (match (_55_3735) with
| (_55_3729, env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint (((hd)::out), (changed)) tl)
end else begin
(

let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (

let _55_3738 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_1894 = (FStar_Syntax_Print.uvar_to_string u)
in (let _149_1893 = (FStar_Syntax_Print.term_to_string tm)
in (let _149_1892 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _149_1894 _149_1893 _149_1892))))
end else begin
()
end
in (

let _55_3747 = (env.FStar_TypeChecker_Env.type_of (

let _55_3740 = env
in {FStar_TypeChecker_Env.solver = _55_3740.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _55_3740.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _55_3740.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _55_3740.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _55_3740.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _55_3740.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _55_3740.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _55_3740.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _55_3740.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _55_3740.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _55_3740.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _55_3740.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _55_3740.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _55_3740.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _55_3740.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _55_3740.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _55_3740.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _55_3740.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _55_3740.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _55_3740.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _55_3740.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _55_3740.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _55_3740.FStar_TypeChecker_Env.qname_and_index}) tm)
in (match (_55_3747) with
| (_55_3743, _55_3745, g) -> begin
(

let g = if env.FStar_TypeChecker_Env.is_pattern then begin
(

let _55_3748 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3748.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3748.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3748.FStar_TypeChecker_Env.implicits})
end else begin
g
end
in (

let g' = (discharge_guard' (Some ((fun _55_3751 -> (match (()) with
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

let _55_3753 = g
in (let _149_1898 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _55_3753.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3753.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3753.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _149_1898})))))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g = (let _149_1903 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _149_1903 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _149_1904 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _149_1904))
end
| ((reason, _55_3763, _55_3765, e, t, r))::_55_3760 -> begin
(let _149_1907 = (let _149_1906 = (FStar_Syntax_Print.term_to_string t)
in (let _149_1905 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" _149_1906 _149_1905 reason)))
in (FStar_TypeChecker_Errors.report r _149_1907))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let _55_3773 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _55_3773.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3773.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (((u1), (u2)))::[]; FStar_TypeChecker_Env.implicits = _55_3773.FStar_TypeChecker_Env.implicits}))




